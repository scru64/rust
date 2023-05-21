use std::{env, sync};

use once_cell::sync::OnceCell as OnceLock;

use super::{Scru64Generator, Scru64Id};

/// A zero-sized type that forwards supported method calls to the process-wide global generator.
///
/// # Examples
///
/// ```rust
/// # use scru64::generator::GlobalGenerator;
/// std::env::set_var("SCRU64_NODE_SPEC", "42/8");
///
/// assert_eq!(GlobalGenerator.node_spec(), "42/8");
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalGenerator;

impl GlobalGenerator {
    fn lock(&self) -> sync::MutexGuard<'_, Scru64Generator> {
        static G: OnceLock<sync::Mutex<Scru64Generator>> = OnceLock::new();

        G.get_or_init(|| {
            let node_spec = env::var("SCRU64_NODE_SPEC")
                .expect("scru64: could not read config from SCRU64_NODE_SPEC env var");
            let g = Scru64Generator::parse(&node_spec)
                .expect("scru64: could not initialize global generator");
            sync::Mutex::new(g)
        })
        .lock()
        .expect("scru64: could not lock global generator")
    }

    /// Calls [`Scru64Generator::generate`] of the global generator.
    pub fn generate(&self) -> Option<Scru64Id> {
        self.lock().generate()
    }

    /// Calls [`Scru64Generator::node_prev`] of the global generator.
    pub fn node_prev(&self) -> Option<Scru64Id> {
        self.lock().node_prev()
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
    pub fn node_spec(&self) -> String {
        self.lock().node_spec()
    }
}
