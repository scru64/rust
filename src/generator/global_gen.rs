use std::{env, error, fmt, sync};

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
    fn lock(&self) -> sync::MutexGuard<'static, Scru64Generator> {
        G.get_or_init(|| {
            use error::Error as _;
            let node_spec = read_env_var("SCRU64_NODE_SPEC")
                .unwrap_or_else(|err| panic!("scru64: {}: {}", err, err.source().unwrap()));
            sync::Mutex::new(Scru64Generator::new(node_spec))
        })
        .lock()
        .expect("scru64: could not lock global generator")
    }

    /// Configures the global generator with the node spec read from the `SCRU64_NODE_SPEC`
    /// environment variable.
    ///
    /// This method returns an error if it fails to read a well-formed node spec string from the
    /// environment variable or, otherwise, configures the global generator and discards the
    /// existing configuration (if any).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scru64::generator::GlobalGenerator;
    ///
    /// std::env::set_var("SCRU64_NODE_SPEC", "");
    /// assert!(GlobalGenerator.configure_from_env().is_err());
    ///
    /// std::env::set_var("SCRU64_NODE_SPEC", "42/8");
    /// assert!(GlobalGenerator.configure_from_env().is_ok());
    /// ```
    pub fn configure_from_env(&self) -> Result<(), impl error::Error> {
        self.configure(read_env_var("SCRU64_NODE_SPEC")?);
        Ok::<(), EnvVarError<'static>>(())
    }

    /// Configures the global generator with a node spec, discarding the existing configuration (if
    /// any).
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

/// Reads the node spec from the environment variable.
fn read_env_var(key: &str) -> Result<NodeSpec, EnvVarError> {
    env::var(key)
        .map_err(|err| EnvVarError {
            key,
            source: Box::new(err),
        })?
        .parse()
        .map_err(|err| EnvVarError {
            key,
            source: Box::new(err),
        })
}

/// An error reading the node spec from the environment variable.
#[derive(Debug)]
struct EnvVarError<'a> {
    key: &'a str,
    source: Box<dyn error::Error>,
}

impl<'a> fmt::Display for EnvVarError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "could not read config from {} env var", self.key)
    }
}

impl<'a> error::Error for EnvVarError<'a> {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(self.source.as_ref())
    }
}
