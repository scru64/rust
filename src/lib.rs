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
//! println!("{x}"); // e.g., "0u2r85hm2pt3"
//! println!("{}", x.to_u64()); // as a 64-bit unsigned integer
//!
//! // generate a textual representation directly
//! println!("{}", scru64::new_string()); // e.g., "0u2r85hm2pt4"
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
//! - `std` integrates the library with, among others, the system clock to draw
//!   current timestamps. Without `std`, this crate provides limited functionality
//!   available under `no_std` environments.
//! - `global_gen` (implies `std`) enables the primary [`new()`] and [`new_string()`]
//!   functions and the process-wide global generator under the hood.
//!
//! Optional features:
//!
//! - `serde` enables serialization/deserialization via serde.
//! - `tokio` (together with `global_gen`) enables the [`async_tokio::new()`] and
//!   [`async_tokio::new_string()`] functions, the non-blocking counterpart of [`new()`]
//!   and [`new_string()`].

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod generator;
mod identifier;

pub use identifier::{ParseError, RangeError, Scru64Id};

#[cfg(feature = "global_gen")]
pub use shortcut::{new, new_string};

#[cfg(all(feature = "global_gen", feature = "tokio"))]
pub use shortcut::async_tokio;

#[cfg(test)]
mod test_cases;

/// The total size in bits of the `node_id` and `counter` fields.
const NODE_CTR_SIZE: u8 = 24;

#[cfg(feature = "global_gen")]
#[cfg_attr(docsrs, doc(cfg(feature = "global_gen")))]
mod shortcut {
    use std::{thread, time};

    use crate::{generator::GlobalGenerator, Scru64Id};

    const DELAY: time::Duration = time::Duration::from_millis(64);

    /// Generates a new SCRU64 ID object using the global generator.
    ///
    /// The [`GlobalGenerator`] reads the node configuration from the `SCRU64_NODE_SPEC`
    /// environment variable by default, and it panics if it fails to read a well-formed node spec
    /// string (e.g., `"42/8"`, `"0xb00/12"`, `"0u2r85hm2pt3/16"`) when a generator method is first
    /// called. See also [`NodeSpec`](crate::generator::NodeSpec) for the node spec string format.
    ///
    /// This function usually returns a value immediately, but if not possible, it sleeps and waits
    /// for the next timestamp tick. It employs blocking sleep to wait; see [`async_tokio::new`]
    /// for the non-blocking equivalent.
    ///
    /// # Panics
    ///
    /// Panics if the global generator is not properly configured.
    pub fn new() -> Scru64Id {
        loop {
            if let Some(value) = GlobalGenerator.generate() {
                break value;
            } else {
                thread::sleep(DELAY);
            }
        }
    }

    /// Generates a new SCRU64 ID encoded in the 12-digit canonical string representation using the
    /// global generator.
    ///
    /// The [`GlobalGenerator`] reads the node configuration from the `SCRU64_NODE_SPEC`
    /// environment variable by default, and it panics if it fails to read a well-formed node spec
    /// string (e.g., `"42/8"`, `"0xb00/12"`, `"0u2r85hm2pt3/16"`) when a generator method is first
    /// called. See also [`NodeSpec`](crate::generator::NodeSpec) for the node spec string format.
    ///
    /// This function usually returns a value immediately, but if not possible, it sleeps and waits
    /// for the next timestamp tick. It employs blocking sleep to wait; see
    /// [`async_tokio::new_string`] for the non-blocking equivalent.
    ///
    /// # Panics
    ///
    /// Panics if the global generator is not properly configured.
    pub fn new_string() -> String {
        new().into()
    }

    /// Non-blocking global generator functions using `tokio`.
    #[cfg(feature = "tokio")]
    #[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
    pub mod async_tokio {
        use super::{GlobalGenerator, Scru64Id, DELAY};

        /// Generates a new SCRU64 ID object using the global generator.
        ///
        /// The [`GlobalGenerator`] reads the node configuration from the `SCRU64_NODE_SPEC`
        /// environment variable by default, and it panics if it fails to read a well-formed node
        /// spec string (e.g., `"42/8"`, `"0xb00/12"`, `"0u2r85hm2pt3/16"`) when a generator method
        /// is first called. See also [`NodeSpec`](crate::generator::NodeSpec) for the node spec
        /// string format.
        ///
        /// This function usually returns a value immediately, but if not possible, it sleeps and
        /// waits for the next timestamp tick.
        ///
        /// # Panics
        ///
        /// Panics if the global generator is not properly configured.
        pub async fn new() -> Scru64Id {
            loop {
                if let Some(value) = GlobalGenerator.generate() {
                    break value;
                } else {
                    tokio::time::sleep(DELAY).await;
                }
            }
        }

        /// Generates a new SCRU64 ID encoded in the 12-digit canonical string representation using
        /// the global generator.
        ///
        /// The [`GlobalGenerator`] reads the node configuration from the `SCRU64_NODE_SPEC`
        /// environment variable by default, and it panics if it fails to read a well-formed node
        /// spec string (e.g., `"42/8"`, `"0xb00/12"`, `"0u2r85hm2pt3/16"`) when a generator method
        /// is first called. See also [`NodeSpec`](crate::generator::NodeSpec) for the node spec
        /// string format.
        ///
        /// This function usually returns a value immediately, but if not possible, it sleeps and
        /// waits for the next timestamp tick.
        ///
        /// # Panics
        ///
        /// Panics if the global generator is not properly configured.
        pub async fn new_string() -> String {
            loop {
                if let Some(value) = GlobalGenerator.generate() {
                    break value.into();
                } else {
                    tokio::time::sleep(DELAY).await;
                }
            }
        }
    }
}
