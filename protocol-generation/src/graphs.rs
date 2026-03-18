use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::marker::PhantomData;
use std::process::{Command, Stdio};

use error_stack::{Report, ResultExt};
use petgraph::{dot::Dot, visit::*};

use crate::vis::{self, Visualizer};

/// A lightweight abstraction around a [`String`] marking it as valid SVG.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Svg {
    pub code: String,
}

impl Svg {
    pub fn new() -> Self {
        Self::default()
    }
}

impl std::ops::Deref for Svg {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.code
    }
}

impl Display for Svg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self)
    }
}

impl TryFrom<Vec<u8>> for Svg {
    type Error = std::string::FromUtf8Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        Ok(Svg {
            code: String::from_utf8(value)?,
        })
    }
}

pub trait GraphvizOutput: TryFrom<Vec<u8>> {
    /// The value to provide to the `-T` flag for the graphviz invocation.
    const GRAPHVIZ_OUTPUT: &'static str;
}

impl GraphvizOutput for Svg {
    const GRAPHVIZ_OUTPUT: &'static str = "svg";
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shape {
    shape: &'static str,
}

impl Shape {
    pub const BOX: Shape = Shape { shape: "box" };
    pub const CIRCLE: Shape = Shape { shape: "circle" };
}

pub struct GraphvizVisualizer<A, G, F, T>
where
    G: IntoNodeReferences,
    F: Fn(G, G::NodeRef) -> Shape,
    T: Visualizer<A>,
{
    pub visualizer: T,
    pub shape_fn: F,
    _target: PhantomData<A>,
    _shape_fn: PhantomData<fn(G)>,
}

impl<A, G, F, T> GraphvizVisualizer<A, G, F, T>
where
    G: IntoNodeReferences,
    F: Fn(G, G::NodeRef) -> Shape,
    T: Visualizer<A>,
{
    pub fn new(node_shape: F) -> Self
    where
        T: Default,
    {
        Self::with_inner(node_shape, T::default())
    }

    pub fn with_inner(node_shape: F, visualizer: T) -> Self {
        GraphvizVisualizer {
            visualizer,
            shape_fn: node_shape,
            _target: PhantomData,
            _shape_fn: PhantomData,
        }
    }
}

impl<A, G, F, T> Visualizer<G> for GraphvizVisualizer<A, G, F, T>
where
    A: GraphvizOutput,
    A::Error: error_stack::IntoReport,
    G: GraphProp + IntoEdgeReferences + IntoNodeReferences + NodeIndexable,
    G::EdgeWeight: Display,
    G::NodeWeight: Display,
    F: Fn(G, G::NodeRef) -> Shape,
    T: Visualizer<A>,
{
    fn visualize(&mut self, graph: G) -> vis::Result {
        // Render the graph into dot source.
        let make_edge_attrs = |_, _| String::new();
        let make_node_attrs = |g, node| format!("shape = {}", (self.shape_fn)(g, node).shape);
        let dot = Dot::with_attr_getters(graph, &[], &make_edge_attrs, &make_node_attrs);

        // Render the dot source.
        let rendered = run_dot(dot, A::GRAPHVIZ_OUTPUT)
            .change_context(vis::Error)
            .attach("graphviz rendering failed")?;

        // Try to parse the graphviz output.
        let output = A::try_from(rendered)
            .change_context(vis::Error)
            .attach("invalid graphviz output")?;

        // Call into the nested visualizer.
        self.visualizer.visualize(output)
    }
}

/// Executes the `dot` executable assumed to live at `/usr/bin/dot` on the given input and returns
/// the rendered graph as SVG.
///
/// TODO: Make the `dot` executable path configurable.
fn run_dot(dot_src: impl Display, target: &str) -> Result<Vec<u8>, Report<std::io::Error>> {
    // Spawn graphviz.
    let dot_path = "/usr/bin/dot";
    let mut gv_dot = Command::new(dot_path)
        .arg(format!("-T{target}"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .attach_with(|| format!("spawn of {dot_path} failed"))?;

    // Write the dot source to the stdin pipe.
    let mut stdin = gv_dot.stdin.take().expect("stdin handle required");
    write!(stdin, "{dot_src}").attach("writing dot input failed")?;

    // Close the stdin handle so that we don't block ourselves while we wait for graphviz to
    // output the rendered SVG.
    drop(stdin);

    // Read the rendered SVG.
    let mut stdout = gv_dot.stdout.take().expect("stdout handle required");
    let mut buf = Vec::new();
    stdout
        .read_to_end(&mut buf)
        .attach("reading rendered SVG failed")?;

    // Wait until graphviz finishes.
    let exit = gv_dot
        .wait()
        .attach("while waiting for graphviz to finish")?;
    if !exit.success() {
        return Err(Report::new(std::io::Error::other(format!(
            "graphviz exited with code {exit}"
        ))));
    }

    // Return the successfully rendered SVG.
    Ok(buf)
}
