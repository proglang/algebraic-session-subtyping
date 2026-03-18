#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, thiserror::Error)]
#[error("graph visualizition failed")]
pub struct Error;

pub type Result = std::result::Result<(), error_stack::Report<Error>>;

pub trait Visualizer<T> {
    fn visualize(&mut self, data: T) -> Result;
}

/// The unit type `()` is a visualizer for anything by doing nothing.
impl<A> Visualizer<A> for () {
    fn visualize(&mut self, _data: A) -> Result {
        Ok(())
    }
}
