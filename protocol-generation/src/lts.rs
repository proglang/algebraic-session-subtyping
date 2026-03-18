use petgraph::{
    graph::DiGraph,
    visit::{GraphBase, IntoEdgeReferences, IntoNeighbors, IntoNodeReferences, Visitable},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Polarity {
    In,
    Out,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum K {
    T,
    S,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeCon {
    End,
    Message(Polarity),
    Branch(Polarity),
    Arrow,
    Base(String),
}

impl TypeCon {
    pub fn kind(&self) -> K {
        match self {
            TypeCon::Arrow | TypeCon::Base(_) => K::T,
            TypeCon::End | TypeCon::Message(_) | TypeCon::Branch(_) => K::S,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Transition {
    One,
    Two,
    Label(String),
}

pub enum FromGraphError<N> {
    /// The graph contains a cycle that passes over an edge labelled [`Transition::One`].
    ///
    /// The cycle is formed by starting from `start`, transitioning according to `cycle`, and arriving
    /// at `end` which has a [`Transition::One`] transition to `start`.
    OneEdgeCycle {
        start: N,
        end: N,
        cycle: Box<[Transition]>,
    },

    /// The graph contains a cycle that passes through a non-session type.
    ///
    /// The cycle is formed by starting from `node` which has the non-session type label `ty_con`,
    /// transitioning according to `cycle`, and arriving back at `node`.
    NonSessionCycle {
        node: N,
        ty_con: TypeCon,
        cycle: Box<[Transition]>,
    },

    /// The graph contains an edge from a session type node to a non-session type node. The
    /// edge is labelled by something other than [`Transition::One`].
    ///
    /// `target` must have kind [`K::S`] but it has kind [`K::T`] instead.
    WrongKind {
        start: N,
        end: N,
        transition: Transition,
    },

    /// The graph contains an otherwise bad transition.
    ///
    /// Examples for bad transitions include edges labelled [`Transition::One`] from a node
    /// labelled [`TypeCon::Branch`], edges labelled [`Transition::Label`] from any node not
    /// labelled [`TypeCon::Branch`], duplicate edges, or any outgoing edge from a node labelled
    /// [`TypeCon::End`] or [`TypeCon::Base`].
    BadTransition {
        start: N,
        end: N,
        transition: Transition,
    },
}

pub struct TypingLts<G> {
    graph: G,
}

impl<G> TypingLts<G>
where
    G: IntoNeighbors + Visitable,
{
    pub fn from_graph(graph: G) -> Result<Self, FromGraphError<G::NodeId>> {
        todo!()
    }
}
