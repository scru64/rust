use std::{env, sync};

use super::{NodeSpec, Scru64Generator, Scru64Id};

/// A zero-sized type that forwards supported method calls to the process-wide global generator.
///
/// # Examples
///
/// ```rust
/// # use scru64::generator::GlobalGenerator;
/// std::env::set_var("SCRU64_NODE_SPEC", "42/8");
///
/// assert_eq!(GlobalGenerator.node_id(), 42);
/// assert_eq!(GlobalGenerator.node_id_size(), 8);
/// assert_eq!(GlobalGenerator.node_spec().to_string(), "42/8");
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalGenerator;

impl GlobalGenerator {
    fn lock(&self) -> sync::MutexGuard<'_, Scru64Generator> {
        static G: sync::OnceLock<sync::Mutex<Scru64Generator>> = sync::OnceLock::new();

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
