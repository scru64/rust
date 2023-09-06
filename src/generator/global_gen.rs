use std::{env, error, fmt, sync};

use super::{NodeSpec, Scru64Generator, Scru64Id};

/// A zero-sized type that forwards supported method calls to the process-wide global generator.
///
/// By default, the global generator reads the node configuration from the `SCRU64_NODE_SPEC`
/// environment variable when a generator method is first called, and it panics if it fails to do
/// so. The node configuration is encoded in a node spec string consisting of `node_id` and
/// `node_id_size` integers separated by a slash (e.g., "42/8", "0xb00/12"; see [`NodeSpec`] for
/// details). You can configure the global generator differently by calling
/// [`GlobalGenerator::initialize`] before the default initializer is triggered.
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
    /// Acquires the lock for the global generator, initializing it based on the environment
    /// variable if not yet initialized.
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

    /// Initializes the global generator, if not initialized, with the node spec passed.
    ///
    /// This method configures the global generator with the argument and returns `Ok` only when
    /// the global generator is not yet initialized. Otherwise, it preserves the existing
    /// configuration and returns `Err` wrapping the argument passed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scru64::generator::GlobalGenerator;
    ///
    /// let x = GlobalGenerator.initialize("0xb00/12".parse()?);
    /// assert!(x.is_ok());
    /// assert_eq!(GlobalGenerator.node_id(), 0xb00);
    /// assert_eq!(GlobalGenerator.node_id_size(), 12);
    /// assert_eq!(GlobalGenerator.node_spec().to_string(), "2816/12");
    ///
    /// let y = GlobalGenerator.initialize("0u2r85hm2pt3/16".parse()?);
    /// assert!(y.is_err());
    /// assert_eq!(y.unwrap_err().to_string(), "0u2r85hm2pt3/16");
    /// assert_eq!(GlobalGenerator.node_id(), 0xb00);
    /// assert_eq!(GlobalGenerator.node_id_size(), 12);
    /// assert_eq!(GlobalGenerator.node_spec().to_string(), "2816/12");
    /// # Ok::<(), scru64::generator::NodeSpecParseError>(())
    /// ```
    ///
    /// Use this method to substitute for the default panicking initializer to handle errors
    /// gracefully.
    ///
    /// ```rust
    /// use scru64::generator::GlobalGenerator;
    ///
    /// std::env::set_var("SCRU64_NODE_SPEC", "42/8");
    ///
    /// let node_spec = std::env::var("SCRU64_NODE_SPEC")?.parse()?;
    /// assert!(GlobalGenerator.initialize(node_spec).is_ok());
    ///
    /// assert_eq!(GlobalGenerator.node_id(), 42);
    /// assert_eq!(GlobalGenerator.node_id_size(), 8);
    /// assert_eq!(GlobalGenerator.node_spec().to_string(), "42/8");
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn initialize(&self, node_spec: NodeSpec) -> Result<(), NodeSpec> {
        let mut wrap = Some(node_spec);
        G.get_or_init(|| sync::Mutex::new(Scru64Generator::new(wrap.take().unwrap())));
        match wrap {
            None => Ok(()),
            Some(node_spec) => Err(node_spec),
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
