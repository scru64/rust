use std::{env, sync};

use super::{NodeSpec, Scru64Generator, Scru64Id};

/// A zero-sized type that forwards supported method calls to the process-wide global generator.
///
/// The global generator reads the node configuration from the `SCRU64_NODE_SPEC` environment
/// variable by default, and it panics if it fails to read a well-formed node spec string (e.g.,
/// `"42/8"`, `"0xb00/12"`, `"0u2r85hm2pt3/16"`) when a generator method is first called. See also
/// [`NodeSpec`] for the node spec string format.
///
/// # Examples
///
/// ```rust
/// use scru64::generator::GlobalGenerator;
///
/// std::env::set_var("SCRU64_NODE_SPEC", "42/8");
///
/// assert_eq!(GlobalGenerator.node_id(), 42);
/// assert_eq!(GlobalGenerator.node_id_size(), 8);
/// assert_eq!(GlobalGenerator.node_spec().to_string(), "42/8");
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalGenerator;

static G: sync::OnceLock<sync::Mutex<Scru64Generator>> = sync::OnceLock::new();

impl GlobalGenerator {
    fn lock(&self) -> sync::MutexGuard<'_, Scru64Generator> {
        G.get_or_init(|| {
            let node_spec = env::var("SCRU64_NODE_SPEC")
                .expect("scru64: could not read config from SCRU64_NODE_SPEC env var")
                .parse()
                .expect("scru64: could not initialize global generator");
            sync::Mutex::new(Scru64Generator::new(node_spec))
        })
        .lock()
        .expect("scru64: could not lock global generator")
    }

    /// Configures the global generator with a node spec, discarding the existing configuration if
    /// any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scru64::generator::GlobalGenerator;
    ///
    /// GlobalGenerator.configure("0xb00/12".parse()?);
    /// assert_eq!(GlobalGenerator.node_id(), 0xb00);
    /// assert_eq!(GlobalGenerator.node_id_size(), 12);
    /// assert_eq!(GlobalGenerator.node_spec().to_string(), "2816/12");
    ///
    /// GlobalGenerator.configure("0u2r85hm2pt3/16".parse()?);
    /// assert_eq!(GlobalGenerator.node_id(), 11001);
    /// assert_eq!(GlobalGenerator.node_id_size(), 16);
    /// assert_eq!(GlobalGenerator.node_spec().to_string(), "0u2r85hm2pt3/16");
    /// # Ok::<(), scru64::generator::NodeSpecParseError>(())
    /// ```
    pub fn configure(&self, node_spec: NodeSpec) {
        let mut g = Some(Scru64Generator::new(node_spec));
        G.get_or_init(|| sync::Mutex::new(g.take().unwrap()));
        if let Some(g) = g {
            // replace current one if get_or_init closure was not called
            *self.lock() = g;
        }
    }

    /// Calls [`Scru64Generator::generate`] of the global generator.
    pub fn generate(&self) -> Option<Scru64Id> {
        self.lock().generate()
    }

    /// Calls [`Scru64Generator::node_id`] of the global generator.
    pub fn node_id(&self) -> u32 {
        self.lock().node_id()
    }

    /// Calls [`Scru64Generator::node_id_size`] of the global generator.
    pub fn node_id_size(&self) -> u8 {
        self.lock().node_id_size()
    }

    /// Calls [`Scru64Generator::node_spec`] of the global generator.
    pub fn node_spec(&self) -> NodeSpec {
        self.lock().node_spec()
    }
}
