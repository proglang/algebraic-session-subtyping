use std::{iter::FusedIterator, num::NonZeroU32};

use hashbrown::HashMap;

/// An identifier for a [`Dfa`] state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StId(NonZeroU32);

impl StId {
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }

    fn from_usize(x: usize) -> Self {
        StId(
            x.try_into()
                .ok()
                .and_then(|x32: u32| NonZeroU32::new(x32 + 1))
                .expect("too many states"),
        )
    }
}

pub struct State<L, A> {
    pub label: L,
    pub transitions: HashMap<A, StId>,
}

pub struct Dfa<L, A> {
    states: Vec<State<L, A>>,
}

impl<L, A> Dfa<L, A> {
    pub fn new() -> Self {
        Dfa { states: vec![] }
    }

    pub fn push(&mut self, label: L) -> StId {
        self.states.push(State {
            label,
            transitions: HashMap::new(),
        });

        StId::from_usize(self.states.len())
    }

    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    pub fn count(&self) -> usize {
        self.states.len()
    }

    pub fn state_ids(
        &self,
    ) -> impl DoubleEndedIterator<Item = StId> + ExactSizeIterator + FusedIterator {
        (0..self.count()).map(StId::from_usize)
    }

    pub fn states(
        &self,
    ) -> impl DoubleEndedIterator<Item = (StId, &State<L, A>)> + ExactSizeIterator + FusedIterator
    {
        self.state_ids().zip(self.states.iter())
    }
}

impl<L, A> std::ops::Index<StId> for Dfa<L, A> {
    type Output = State<L, A>;

    fn index(&self, index: StId) -> &Self::Output {
        &self.states[index.index()]
    }
}

impl<L, A> std::ops::IndexMut<StId> for Dfa<L, A> {
    fn index_mut(&mut self, index: StId) -> &mut Self::Output {
        &mut self.states[index.index()]
    }
}

/*
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Transition<A> {
    source: StId,
    symbol: A,
}

impl<A: Eq> hashbrown::Equivalent<Transition<A>> for Transition<&A> {
    fn equivalent(&self, other: &Transition<A>) -> bool {
        self.source == other.source && *self.symbol == other.symbol
    }
}

pub struct LabeledAutomaton<L, A: Hash + Eq> {
    label: Vec<L>,
    //label_map: HashMap<L, Vec<Id>>,
    transitions: HashMap<Transition<A>, StId>,
}

#[derive(Clone, Copy)]
pub struct State<'a, L, A: Hash + Eq> {
    id: StId,
    automaton: &'a LabeledAutomaton<L, A>,
}

impl<L, A: Hash + Eq> LabeledAutomaton<L, A> {
    pub fn state_label(&self, id: StId) -> &L {
        &self.label[id.0.get() - 1]
    }

    pub fn state_count(&self) -> usize {
        self.label.len()
    }

    pub fn state_ids(
        &self,
    ) -> impl DoubleEndedIterator<Item = StId> + ExactSizeIterator + FusedIterator + Clone {
        (0..self.state_count())
            .map(|idx| StId(NonZeroUsize::new(idx + 1).expect("too many states")))
    }

    pub fn states(
        &self,
    ) -> impl DoubleEndedIterator<Item = State<'_, L, A>> + ExactSizeIterator + FusedIterator + Clone
    {
        self.state_ids().map(|id| State {
            id,
            automaton: self,
        })
    }

    pub fn state(&self, id: StId) -> State<'_, L, A> {
        State {
            id,
            automaton: self,
        }
    }

    /*
    fn reverse_transitions(&self) -> HashMap<Transition<&A>, Vec<Id>> {
        let mut rev: HashMap<Transition<&A>, Vec<Id>> = HashMap::new();
        for (tr, tgt) in self.transitions.iter() {
            rev.entry(Transition {
                source: *tgt,
                symbol: &tr.symbol,
            })
            .or_default()
            .push(tr.source);
        }
        rev
    }
    */
}

/*
impl<L: Hash + Eq, A: Hash + Eq> LabeledAutomaton<L, A> {
    pub fn minimize<'a>(&'a self) -> Self
    where
        A: Enumerate<'a>,
    {
        let mut partitions = self
            .state_ids()
            .into_group_map_by(|&id| self.state_label(id))
            .into_values()
            .map(BTreeSet::from_iter)
            .collect_vec();

        let Some(smallest) = partitions.iter().min_by_key(|p| p.len()) else {
            todo!();
        };

        let mut waiting = self.state_ids().map(|id| (smallest, id)).collect_vec();
        while let Some((w, a)) = waiting.pop() {

        }

        todo!()
    }
}
*/

impl<'a, L, A: Hash + Eq> State<'a, L, A> {
    pub fn label(self) -> &'a L {
        self.automaton.state_label(self.id)
    }

    pub fn step(self, sym: &A) -> Option<Self> {
        let transition: Transition<&A> = Transition {
            source: self.id,
            symbol: sym,
        };
        Some(State {
            id: *self.automaton.transitions.get(&transition)?,
            automaton: self.automaton,
        })
    }

    pub fn target<'b>(self, word: impl IntoIterator<Item = &'b A>) -> Option<Self>
    where
        A: 'b,
    {
        word.into_iter().try_fold(self, State::step)
    }
}
*/
