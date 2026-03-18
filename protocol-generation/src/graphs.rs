use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::process::{Command, Stdio};

use error_stack::{Report, ResultExt};
use petgraph::{dot::Dot, visit::*};
use tao::{
    event::{Event, WindowEvent},
    event_loop::ControlFlow,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Shape {
    shape: &'static str,
}

impl Shape {
    pub const BOX: Shape = Shape { shape: "box" };
    pub const CIRCLE: Shape = Shape { shape: "circle" };
}

#[derive(Debug, Clone, thiserror::Error)]
#[error("graph visualizition failed")]
pub struct VisualizationError;

pub fn visualize<G>(
    graph: G,
    node_shape: impl Fn(G::NodeRef) -> Shape,
) -> Result<(), Report<VisualizationError>>
where
    G: GraphProp + IntoEdgeReferences + IntoNodeReferences + NodeIndexable,
    G::EdgeWeight: Display,
    G::NodeWeight: Display,
{
    // Render the graph into dot source.
    let make_shape_attr = |_, node| format!("shape = {}", node_shape(node).shape);
    let dot = Dot::with_attr_getters(graph, &[], &|_, _edge| String::new(), &make_shape_attr);

    // Render the dot source into an SVG.
    let svg = run_dot(dot)
        .change_context(VisualizationError)
        .attach("graphviz rendering failed")?;

    // Display the SVG.
    display_svg(svg).change_context(VisualizationError)?;

    Ok(())
}

/// Executes the `dot` executable assumed to live at `/usr/bin/dot` on the given input and returns
/// the rendered graph as SVG.
///
/// TODO: Make the `dot` executable path configurable.
fn run_dot(dot_src: impl Display) -> Result<String, Report<std::io::Error>> {
    // Spawn graphviz.
    let dot_path = "/usr/bin/dot";
    let mut gv_dot = Command::new(dot_path)
        .arg("-Tsvg")
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
    let mut svg = String::new();
    stdout
        .read_to_string(&mut svg)
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
    Ok(svg)
}

fn display_svg(svg_content: String) -> Result<(), Report<VisualizationError>> {
    let event_loop = tao::event_loop::EventLoop::new();
    let window = tao::window::WindowBuilder::new()
        .with_title(env!("CARGO_PKG_NAME"))
        .build(&event_loop)
        .change_context(VisualizationError)?;

    let builder = wry::WebViewBuilder::new().with_html(svg_content);

    #[cfg(any(
        target_os = "windows",
        target_os = "macos",
        target_os = "ios",
        target_os = "android"
    ))]
    let _webview = builder.build(&window).change_context(VisualizationError)?;

    #[cfg(not(any(
        target_os = "windows",
        target_os = "macos",
        target_os = "ios",
        target_os = "android"
    )))]
    let _webview = {
        use tao::platform::unix::WindowExtUnix;
        use wry::WebViewBuilderExtUnix;
        let vbox = window.default_vbox().unwrap();
        builder.build_gtk(vbox).change_context(VisualizationError)?
    };

    event_loop.run(move |event, _target, control_flow| {
        *control_flow = ControlFlow::Wait;

        if matches!(
            event,
            Event::WindowEvent {
                event: WindowEvent::CloseRequested,
                ..
            }
        ) {
            *control_flow = ControlFlow::ExitWithCode(0);
        }
    });
}
