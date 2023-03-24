//! SCRU64 generator and related items.

#[cfg(not(feature = "std"))]
use core as std;
use std::fmt;

use pcg32::Pcg32;

use crate::{Scru64Id, NODE_CTR_SIZE};

/// Represents a SCRU64 ID generator.
///
/// The generator offers four different methods to generate a SCRU64 ID:
///
/// | Flavor                      | Timestamp | On big clock rewind |
/// | --------------------------- | --------- | ------------------- |
/// | [`generate`]                | Now       | Rewinds state       |
/// | [`generate_no_rewind`]      | Now       | Returns `None`      |
/// | [`generate_core`]           | Argument  | Rewinds state       |
/// | [`generate_core_no_rewind`] | Argument  | Returns `None`      |
///
/// Each method returns monotonically increasing IDs unless a timestamp provided is significantly
/// (by ~10 seconds or more) smaller than the one embedded in the immediately preceding ID. If such
/// a significant clock rollback is detected, the standard `generate` rewinds the generator state
/// and returns a new ID based on the current timestamp, whereas `no_rewind` variants keep the
/// state untouched and return `None`. `core` functions offer low-level primitives.
///
/// [`generate`]: Scru64Generator::generate
/// [`generate_no_rewind`]: Scru64Generator::generate_no_rewind
/// [`generate_core`]: Scru64Generator::generate_core
/// [`generate_core_no_rewind`]: Scru64Generator::generate_core_no_rewind
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scru64Generator {
    prev: Scru64Id,
    counter_size: u8,
    rng: Pcg32,
}

impl Scru64Generator {
    /// Creates a generator with a node configuration.
    ///
    /// The `node_id` must fit in `node_id_size` bits, where `node_id_size` ranges from 1 to 23,
    /// inclusive.
    ///
    /// # Panics
    ///
    /// Panics if the arguments represent an invalid node configuration.
    pub fn new(node_id: u32, node_id_size: u8) -> Self {
        verify_node(node_id, node_id_size).unwrap_or_else(|err| panic!("{err}"));
        let counter_size = NODE_CTR_SIZE - node_id_size;
        let prev = Scru64Id::from_parts(0, node_id << counter_size);
        let seed = &counter_size as *const u8; // use local var address as seed
        Self {
            prev,
            counter_size,
            rng: Pcg32::new(prev.to_u64(), seed as u64),
        }
    }

    /// Creates a generator by parsing a node spec string that describes the node configuration.
    ///
    /// A node spec string consists of `node_id` and `node_id_size` separated by a slash (e.g.,
    /// `"42/8"`, `"12345/16"`).
    ///
    /// # Errors
    ///
    /// Returns `Err` if the node spec does not conform to the valid syntax or represents an
    /// invalid node configuration.
    pub fn parse(node_spec: &str) -> Result<Self, NodeSpecError> {
        const ERR: NodeSpecError = NodeSpecError::Syntax;
        let mut iter = node_spec.split('/');
        let node_id: u32 = iter.next().ok_or(ERR)?.parse().or(Err(ERR))?;
        let node_id_size: u8 = iter.next().ok_or(ERR)?.parse().or(Err(ERR))?;
        if iter.next().is_some() {
            return Err(ERR);
        }

        verify_node(node_id, node_id_size)?;
        Ok(Self::new(node_id, node_id_size))
    }

    /// Returns the `node_id` of the generator.
    pub const fn node_id(&self) -> u32 {
        self.prev.node_ctr() >> self.counter_size
    }

    /// Returns the size in bits of the `node_id` adopted by the generator.
    pub const fn node_id_size(&self) -> u8 {
        NODE_CTR_SIZE - self.counter_size
    }

    /// Calculates the combined `node_ctr` field value for the next `timestamp` tick.
    fn init_node_ctr(&mut self) -> u32 {
        // initialize counter at `counter_size - 1`-bit random number
        const OVERFLOW_GUARD_SIZE: u8 = 1;
        let counter = self.rng.gen() >> (32 + OVERFLOW_GUARD_SIZE - self.counter_size);

        (self.node_id() << self.counter_size) | counter
    }

    /// Generates a new SCRU64 ID object from a Unix timestamp in milliseconds.
    ///
    /// See the [`Scru64Generator`] type documentation for the description.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a positive integer within the valid range.
    pub fn generate_core(&mut self, unix_ts_ms: u64) -> Scru64Id {
        if let Some(value) = self.generate_core_no_rewind(unix_ts_ms) {
            value
        } else {
            // reset state and resume
            self.prev = Scru64Id::from_parts(unix_ts_ms >> 8, self.init_node_ctr());
            self.prev
        }
    }

    /// Generates a new SCRU64 ID object from a Unix timestamp in milliseconds, guaranteeing the
    /// monotonic order of generated IDs despite a significant timestamp rollback.
    ///
    /// See the [`Scru64Generator`] type documentation for the description.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a positive integer within the valid range.
    pub fn generate_core_no_rewind(&mut self, unix_ts_ms: u64) -> Option<Scru64Id> {
        const ROLLBACK_ALLOWANCE: u64 = 40; // x256 milliseconds = ~10 seconds

        let timestamp = unix_ts_ms >> 8;
        assert!(timestamp > 0, "`timestamp` out of range");

        let prev_timestamp = self.prev.timestamp();
        if timestamp > prev_timestamp {
            self.prev = Scru64Id::from_parts(timestamp, self.init_node_ctr());
        } else if timestamp + ROLLBACK_ALLOWANCE > prev_timestamp {
            // go on with previous timestamp if new one is not much smaller
            let prev_node_ctr = self.prev.node_ctr();
            let counter_mask = (1u32 << self.counter_size) - 1;
            if (prev_node_ctr & counter_mask) < counter_mask {
                self.prev = Scru64Id::from_parts(prev_timestamp, prev_node_ctr + 1);
            } else {
                // increment timestamp at counter overflow
                self.prev = Scru64Id::from_parts(prev_timestamp + 1, self.init_node_ctr());
            }
        } else {
            // abort if clock went backwards to unbearable extent
            return None;
        }
        Some(self.prev)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::{Scru64Generator, Scru64Id};

    /// Returns the current Unix timestamp in milliseconds.
    fn unix_ts_ms() -> u64 {
        use std::time;
        time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .expect("clock may have gone backward")
            .as_millis() as u64
    }

    impl Scru64Generator {
        /// Generates a new SCRU64 ID object from the current `timestamp`.
        ///
        /// See the [`Scru64Generator`] type documentation for the description.
        pub fn generate(&mut self) -> Scru64Id {
            self.generate_core(unix_ts_ms())
        }

        /// Generates a new SCRU64 ID object from the current `timestamp`, guaranteeing the
        /// monotonic order of generated IDs despite a significant timestamp rollback.
        ///
        /// See the [`Scru64Generator`] type documentation for the description.
        pub fn generate_no_rewind(&mut self) -> Option<Scru64Id> {
            self.generate_core_no_rewind(unix_ts_ms())
        }
    }
}

/// Tests if a pair of `node_id` and `node_id_size` is valid.
const fn verify_node(node_id: u32, node_id_size: u8) -> Result<(), NodeSpecError> {
    if node_id_size == 0 || node_id_size >= NODE_CTR_SIZE {
        return Err(NodeSpecError::NodeSizeRange);
    }
    if (node_id >> node_id_size) > 0 {
        return Err(NodeSpecError::NodeRange);
    }
    Ok(())
}

/// An error parsing a node spec string.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum NodeSpecError {
    /// Invalid node spec syntax.
    Syntax,

    /// `node_id` is greater than the `node_id_size` range.
    NodeRange,

    /// `node_id_size` is zero or greater than 23.
    NodeSizeRange,
}

impl fmt::Display for NodeSpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax => f.write_str("invalid `node_spec`; it looks like: `42/8`, `12345/16`"),
            Self::NodeRange => f.write_str("`node_id` must fit in `node_id_size` bits"),
            Self::NodeSizeRange => f.write_str("`node_id_size` must range from 1 to 23"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for NodeSpecError {}
