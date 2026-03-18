use error_stack::Report;
use hashbrown::{HashMap, HashSet};
use petgraph::graph::DiGraph;
use protocol_generation::graphs::{self, VisualizationError};

pub mod dfa;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Polarity {
    In,
    Out,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum K {
    T,
    S,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TypeCon {
    End,
    Message(Polarity),
    Branch(Polarity),
    Arrow,
    Base(String),
}

impl TypeCon {
    fn kind(&self) -> K {
        match self {
            TypeCon::Arrow | TypeCon::Base(_) => K::T,
            TypeCon::End | TypeCon::Message(_) | TypeCon::Branch(_) => K::S,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Transition {
    One,
    Two,
    Label(String),
}

enum LtsError {
    BadCycle,
    /// `target` must have kind [`K::S`] but it has kind [`K::T`] instead.
    WrongKind {
        source: dfa::StId,
        transition: Transition,
        target: dfa::StId,
    },
    BadTransition,
}

struct TypingLts(dfa::Dfa<TypeCon, Transition>);

impl TypingLts {
    fn new(dfa: dfa::Dfa<TypeCon, Transition>) -> Result<Self, LtsError> {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        enum Status {
            Unchecked,
            Checking(usize),
            Checked(K),
        }

        struct Visitor<'a> {
            /// The automaton we visit.
            dfa: &'a dfa::Dfa<TypeCon, Transition>,

            /// A map from states to their check status. `None` indicates not fully checked,
            check_status: Box<[Status]>,

            /// One entry per call stack level indicating whether a cycle is allowed to pass
            /// through this node.
            stack_may_cycle: Vec<bool>,
        }

        impl<'a> Visitor<'a> {
            fn new(dfa: &'a dfa::Dfa<TypeCon, Transition>) -> Self {
                Visitor {
                    dfa,
                    check_status: vec![Status::Unchecked; dfa.count()].into_boxed_slice(),
                    stack_may_cycle: vec![],
                }
            }

            fn check(
                &mut self,
                id: dfa::StId,
                kind_s_req: Option<(dfa::StId, &Transition)>,
            ) -> Result<(), LtsError> {
                match self.check_status[id.index()] {
                    // We've encountered a cycle. All nodes on the stack between there and now must
                    // be allowed to participate in cycles.
                    Status::Checking(check_ix) => {
                        if self.stack_may_cycle[check_ix..]
                            .iter()
                            .all(|&may_cycle| may_cycle)
                        {
                            // Cycle is allowed. There is nothing else to do as the node is already
                            // being checked
                            return Ok(());
                        } else {
                            // Invalid cycle!
                            return Err(LtsError::BadCycle);
                        }
                    }

                    // The node has already been checked. Verify that its kind matches a potential
                    // `K::S` requirement.
                    Status::Checked(k) => {
                        if let Some((prev, trans)) = kind_s_req
                            && k == K::T
                        {
                            return Err(LtsError::WrongKind {
                                source: prev,
                                transition: trans.clone(),
                                target: id,
                            });
                        } else {
                            return Ok(());
                        }
                    }

                    Status::Unchecked => {
                        // Fall through to the checking code below.
                    }
                }

                // Retrieve the underlying state and mark the status as being checked.
                let state = &self.dfa[id];
                self.check_status[id.index()] = Status::Checking(self.stack_may_cycle.len());

                // (1)
                if matches!(state.label, TypeCon::End | TypeCon::Base(_))
                    && !state.transitions.is_empty()
                {
                    return Err(LtsError::BadTransition);
                }

                // (2)
                if matches!(state.label, TypeCon::Message(_) | TypeCon::Arrow) {
                    // Precheck also necessary to verify that there are at least two transitions.
                    if state.transitions.len() != 2 {
                        return Err(LtsError::BadTransition);
                    }

                    state.transitions.iter().try_for_each(|(tr, &tgt)| {
                        if matches!(tr, Transition::One | Transition::Two) {
                            self.do_transition(id, state, tr, tgt)
                        } else {
                            Err(LtsError::BadTransition)
                        }
                    })?;
                }

                // (3)
                if matches!(state.label, TypeCon::Branch(_)) {
                    state.transitions.iter().try_for_each(|(tr, &tgt)| {
                        if matches!(tr, Transition::Label(_)) {
                            self.do_transition(id, state, tr, tgt)
                        } else {
                            Err(LtsError::BadTransition)
                        }
                    })?;
                }

                // All checks passed.
                self.check_status[id.index()] = Status::Checked(state.label.kind());
                Ok(())
            }

            fn do_transition(
                &mut self,
                src: dfa::StId,
                state: &dfa::State<TypeCon, Transition>,
                tr: &Transition,
                tgt: dfa::StId,
            ) -> Result<(), LtsError> {
                let session_kinded = state.label.kind() == K::S && *tr != Transition::One;
                self.stack_may_cycle.push(session_kinded);
                self.check(tgt, session_kinded.then_some((src, tr)))?;
                self.stack_may_cycle.pop();
                Ok(())
            }
        }

        let mut visitor = Visitor::new(&dfa);
        dfa.state_ids().try_for_each(|id| visitor.check(id, None))?;
        Ok(TypingLts(dfa))
    }
}

#[derive(Debug, Clone, Copy)]
enum BuildError<'a> {
    InvalidName { name: &'a str },
    MissingConstructor,
    InvalidConstructor { name: &'a str },
    InvalidBranchTarget { target: &'a str },
    DuplicateLabel { label: &'a str },
    DuplicateDefinitions { name: &'a str },
    BinaryLabeledTarget { target: &'a str },
    BinaryWrongTransCount { count: usize },
}

struct DfaBuilder<'a> {
    dfa: dfa::Dfa<Option<TypeCon>, Transition>,
    states: HashMap<&'a str, dfa::StId>,
}

impl<'a> DfaBuilder<'a> {
    fn get_or_create(&mut self, name: Option<&'a str>) -> dfa::StId {
        let mut push_new = || self.dfa.push((name == Some("End")).then_some(TypeCon::End));
        if let Some(name) = name {
            *self.states.entry(name).or_insert_with(push_new)
        } else {
            // This state cannot be referred to, push unconditionally.
            push_new()
        }
    }

    fn read_line(&mut self, s: &'a str) -> Result<(), BuildError<'a>> {
        let mut segs = s.split_whitespace().peekable();
        let name =
            segs.next_if_map_mut(
                |seg| match (seg.as_bytes().first(), seg.as_bytes().last()) {
                    (Some(b'('), Some(b')')) => Some(&seg[1..seg.len() - 1]),
                    _ => None,
                },
            );

        if let Some(name) = name
            && (name.is_empty()
                || name == "End"
                || name.contains(|c: char| {
                    !c.is_alphanumeric() && !matches!(c, '_' | '-' | '?' | '!' | '&' | '+')
                }))
        {
            return Err(BuildError::InvalidName { name });
        }

        let tycon = match segs.next() {
            None if name.is_some() => {
                // Gave a name but no constructor.
                return Err(BuildError::MissingConstructor);
            }

            None => {
                // Empty line, ignore.
                return Ok(());
            }

            Some("+") => TypeCon::Branch(Polarity::Out),
            Some("&") => TypeCon::Branch(Polarity::In),
            Some("!") => TypeCon::Message(Polarity::Out),
            Some("?") => TypeCon::Message(Polarity::In),
            Some("->") => TypeCon::Arrow,

            Some(name) => return Err(BuildError::InvalidConstructor { name }),
        };

        let transitions = if matches!(tycon, TypeCon::Branch(_)) {
            let mut seen_labels = HashSet::new();
            segs.map(|target| {
                if let Some((label, target)) = target.split_once(':') {
                    if !seen_labels.insert(label) {
                        Err(BuildError::DuplicateLabel { label })
                    } else {
                        Ok((
                            Transition::Label(label.to_owned()),
                            self.get_or_create(Some(target)),
                        ))
                    }
                } else {
                    Err(BuildError::InvalidBranchTarget { target })
                }
            })
            .collect::<Result<_, _>>()?
        } else {
            let Some(t1) = segs.next() else {
                return Err(BuildError::BinaryWrongTransCount { count: 0 });
            };
            let Some(t2) = segs.next() else {
                return Err(BuildError::BinaryWrongTransCount { count: 1 });
            };
            if segs.next().is_some() {
                return Err(BuildError::BinaryWrongTransCount {
                    count: 1 + segs.count(),
                });
            };
            if let Some(labeled_target) = [t1, t2].iter().find(|target| target.contains(':')) {
                return Err(BuildError::BinaryLabeledTarget {
                    target: labeled_target,
                });
            }

            let mut transitions = HashMap::with_capacity(2);
            transitions.insert(Transition::One, self.get_or_create(Some(t1)));
            transitions.insert(Transition::Two, self.get_or_create(Some(t2)));
            transitions
        };

        let this_id = self.get_or_create(name);
        let this_state = &mut self.dfa[this_id];

        if this_state.label.is_some() {
            return Err(BuildError::DuplicateDefinitions {
                name: name.expect("duplicate definition implies the state is named"),
            });
        }

        this_state.label = Some(tycon);
        this_state.transitions = transitions;

        Ok(())
    }
}

fn main() -> Result<(), Report<VisualizationError>> {
    let mut g = DiGraph::<String, String>::new();
    let a = g.add_node("+".to_owned());
    let b = g.add_node("&".to_owned());

    let g = DiGraph::<String, String>::from_edges([(a, b, "A".to_owned()), (b, a, "B".to_owned())]);

    eprintln!("pre-visualization");

    graphs::visualize(&g, |_| graphs::Shape::CIRCLE)?;

    eprintln!("post-visualization");

    Ok(())
}
