//! # SCRU64: Sortable, Clock-based, Realm-specifically Unique identifier
//!
//! SCRU64 ID offers compact, time-ordered unique identifiers generated by
//! distributed nodes. SCRU64 has the following features:
//!
//! - ~62-bit non-negative integer storable as signed/unsigned 64-bit integer
//! - Sortable by generation time (as integer and as text)
//! - 12-digit case-insensitive textual representation (Base36)
//! - ~38-bit Unix epoch-based timestamp that ensures useful life until year 4261
//! - Variable-length node/machine ID and counter fields that share 24 bits
//!
//! ```rust
//! // pass node ID through environment variable
//! std::env::set_var("SCRU64_NODE_SPEC", "42/8");
//!
//! // generate a new identifier object
//! let x = scru64::new();
//! println!("{x}"); // e.g. "0u2r85hm2pt3"
//! println!("{}", x.to_u64()); // as a 64-bit unsigned integer
//!
//! // generate a textual representation directly
//! println!("{}", scru64::new_string()); // e.g. "0u2r85hm2pt4"
//! ```
//!
//! See [SCRU64 Specification] for details.
//!
//! SCRU64's uniqueness is realm-specific, i.e., dependent on the centralized
//! assignment of node ID to each generator. If you need decentralized, globally
//! unique time-ordered identifiers, consider [SCRU128].
//!
//! [SCRU64 Specification]: https://github.com/scru64/spec
//! [SCRU128]: https://github.com/scru128/spec
//!
//! ## Crate features
//!
//! Default features:
//!
//! - `std` enables the primary [`new()`] and [`new_string()`] functions and configures
//!   [`generator::Scru64Generator`] with the system clock. Without `std`, this crate
//!   provides limited functionality available under `no_std` environments.
//!
//! Optional features:
//!
//! - `serde` enables serialization/deserialization via serde.
//! - `tokio` enables the [`async_tokio::new()`] and [`async_tokio::new_string()`]
//!   functions, the non-blocking counterpart of `new()` and `new_string()`.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod generator;
mod identifier;

pub use identifier::{ConversionError, Scru64Id};

#[cfg(feature = "std")]
pub use global_gen::{new, new_string};

#[cfg(all(feature = "std", feature = "tokio"))]
pub use global_gen::async_tokio;

/// The total size in bits of the `node_id` and `counter` fields.
const NODE_CTR_SIZE: u8 = 24;

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod global_gen {
    use std::{env, sync::Mutex, thread, time};

    use once_cell::sync::Lazy;

    use crate::{generator::Scru64Generator, Scru64Id};

    static GLOBAL_GENERATOR: Lazy<Mutex<Scru64Generator>> = Lazy::new(|| {
        let g = match env::var("SCRU64_NODE_SPEC") {
            Err(err) => {
                panic!("scru64: could not read config from SCRU64_NODE_SPEC env var: {err}")
            }
            Ok(node_spec) => Scru64Generator::parse(&node_spec).unwrap_or_else(|err| {
                panic!("scru64: could not initialize global generator: {err}")
            }),
        };
        Mutex::new(g)
    });

    fn generate_no_rewind() -> Option<Scru64Id> {
        GLOBAL_GENERATOR
            .lock()
            .unwrap_or_else(|err| panic!("scru64: could not lock global generator: {err}"))
            .generate_no_rewind()
    }

    const DELAY: time::Duration = time::Duration::from_millis(64);

    /// Generates a new SCRU64 ID object using the global generator.
    ///
    /// # Panics
    ///
    /// Panics if the global generator is not properly configured through the `SCRU64_NODE_SPEC`
    /// environment variable.
    pub fn new() -> Scru64Id {
        loop {
            if let Some(value) = generate_no_rewind() {
                break value;
            } else {
                thread::sleep(DELAY);
            }
        }
    }

    /// Generates a new SCRU64 ID encoded in the 12-digit canonical string representation using the
    /// global generator.
    ///
    /// # Panics
    ///
    /// Panics if the global generator is not properly configured through the `SCRU64_NODE_SPEC`
    /// environment variable.
    pub fn new_string() -> String {
        new().into()
    }

    /// Non-blocking global generator functions using `tokio`.
    #[cfg(feature = "tokio")]
    #[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
    pub mod async_tokio {
        use super::{generate_no_rewind, Scru64Id, DELAY};

        /// Generates a new SCRU64 ID object using the global generator.
        ///
        /// # Panics
        ///
        /// Panics if the global generator is not properly configured through the
        /// `SCRU64_NODE_SPEC` environment variable.
        pub async fn new() -> Scru64Id {
            loop {
                if let Some(value) = generate_no_rewind() {
                    break value;
                } else {
                    tokio::time::sleep(DELAY).await;
                }
            }
        }

        /// Generates a new SCRU64 ID encoded in the 12-digit canonical string representation using
        /// the global generator.
        ///
        /// # Panics
        ///
        /// Panics if the global generator is not properly configured through the
        /// `SCRU64_NODE_SPEC` environment variable.
        pub async fn new_string() -> String {
            loop {
                if let Some(value) = generate_no_rewind() {
                    break value.into();
                } else {
                    tokio::time::sleep(DELAY).await;
                }
            }
        }
    }
}
