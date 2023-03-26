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
/// | Flavor                     | Timestamp | On big clock rewind |
/// | -------------------------- | --------- | ------------------- |
/// | [`generate`]               | Now       | Returns `None`      |
/// | [`generate_or_reset`]      | Now       | Resets generator    |
/// | [`generate_or_abort_core`] | Argument  | Returns `None`      |
/// | [`generate_or_reset_core`] | Argument  | Resets generator    |
///
/// All of these methods return monotonically increasing IDs unless a timestamp provided is
/// significantly (by default, approx. 10 seconds or more) smaller than the one embedded in the
/// immediately preceding ID. If such a significant clock rollback is detected, the `generate`
/// (or_abort) method aborts and returns `None`, while the `or_reset` variants reset the generator
/// and return a new ID based on the given timestamp. The `core` functions offer low-level
/// primitives.
///
/// [`generate`]: Scru64Generator::generate
/// [`generate_or_reset`]: Scru64Generator::generate_or_reset
/// [`generate_or_abort_core`]: Scru64Generator::generate_or_abort_core
/// [`generate_or_reset_core`]: Scru64Generator::generate_or_reset_core
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
        let x = iter.next().ok_or(ERR)?;
        let y = iter.next().ok_or(ERR)?;
        if iter.next().is_some() || x.starts_with('+') || y.starts_with('+') {
            return Err(ERR);
        }

        let node_id: u32 = x.parse().or(Err(ERR))?;
        let node_id_size: u8 = y.parse().or(Err(ERR))?;
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
        let counter = if OVERFLOW_GUARD_SIZE < self.counter_size {
            self.rng.gen() >> (32 + OVERFLOW_GUARD_SIZE - self.counter_size)
        } else {
            0
        };

        (self.node_id() << self.counter_size) | counter
    }

    /// Generates a new SCRU64 ID object from a Unix timestamp in milliseconds, or resets the
    /// generator upon significant timestamp rollback.
    ///
    /// See the [`Scru64Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a positive integer within the valid range.
    pub fn generate_or_reset_core(&mut self, unix_ts_ms: u64, rollback_allowance: u64) -> Scru64Id {
        if let Some(value) = self.generate_or_abort_core(unix_ts_ms, rollback_allowance) {
            value
        } else {
            // reset state and resume
            self.prev = Scru64Id::from_parts(unix_ts_ms >> 8, self.init_node_ctr());
            self.prev
        }
    }

    /// Generates a new SCRU64 ID object from a Unix timestamp in milliseconds, or returns `None`
    /// upon significant timestamp rollback.
    ///
    /// See the [`Scru64Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a positive integer within the valid range.
    pub fn generate_or_abort_core(
        &mut self,
        unix_ts_ms: u64,
        rollback_allowance: u64,
    ) -> Option<Scru64Id> {
        let timestamp = unix_ts_ms >> 8;
        let allowance = rollback_allowance >> 8;
        assert!(timestamp > 0, "`timestamp` out of range");
        assert!(
            allowance < (1 << 40),
            "`rollback_allowance` out of reasonable range"
        );

        let prev_timestamp = self.prev.timestamp();
        if timestamp > prev_timestamp {
            self.prev = Scru64Id::from_parts(timestamp, self.init_node_ctr());
        } else if timestamp + allowance > prev_timestamp {
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
            .expect("clock may have gone backwards")
            .as_millis() as u64
    }

    impl Scru64Generator {
        /// Generates a new SCRU64 ID object from the current `timestamp`, or returns `None` upon
        /// significant timestamp rollback.
        ///
        /// See the [`Scru64Generator`] type documentation for the description.
        pub fn generate(&mut self) -> Option<Scru64Id> {
            self.generate_or_abort_core(unix_ts_ms(), 10_000)
        }

        /// Generates a new SCRU64 ID object from the current `timestamp`, or resets the generator
        /// upon significant timestamp rollback.
        ///
        /// See the [`Scru64Generator`] type documentation for the description.
        pub fn generate_or_reset(&mut self) -> Scru64Id {
            self.generate_or_reset_core(unix_ts_ms(), 10_000)
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

#[cfg(test)]
mod tests {
    use super::{Scru64Generator, Scru64Id};

    const NODE_SPECS: &[(u32, u8, &'static str)] = &[
        (0, 1, "0/1"),
        (1, 1, "1/1"),
        (0, 8, "0/8"),
        (42, 8, "42/8"),
        (255, 8, "255/8"),
        (0, 16, "0/16"),
        (334, 16, "334/16"),
        (65535, 16, "65535/16"),
        (0, 23, "0/23"),
        (123456, 23, "123456/23"),
        (8388607, 23, "8388607/23"),
    ];

    /// Tests constructors.
    #[test]
    fn construct() {
        for &(node_id, node_id_size, node_spec) in NODE_SPECS {
            let x = Scru64Generator::new(node_id, node_id_size);
            assert_eq!(x.node_id(), node_id);
            assert_eq!(x.node_id_size(), node_id_size);

            let y = Scru64Generator::parse(node_spec).unwrap();
            assert_eq!(y.node_id(), node_id);
            assert_eq!(y.node_id_size(), node_id_size);
        }
    }

    /// Tests if constructor fails on invalid `node_spec` inputs.
    #[test]
    fn construct_error() {
        let cases = [
            "", " 42/8", "42/8 ", " 42/8 ", "42 / 8", "+42/8", "42/+8", "-42/8", "42/-8", "ab/8",
            "0x42/8", "0/0", "0/24", "8/1", "1024/8",
        ];

        for e in cases {
            assert!(Scru64Generator::parse(e).is_err());
        }
    }

    fn test_consecutive_pair(first: Scru64Id, second: Scru64Id) {
        assert!(first < second);
        if first.timestamp() == second.timestamp() {
            assert_eq!(first.node_ctr() + 1, second.node_ctr());
        } else {
            assert_eq!(first.timestamp() + 1, second.timestamp());
        }
    }

    /// Tests `generate_or_reset_core()`.
    #[test]
    fn generate_or_reset() {
        const N_LOOPS: usize = 64;
        const ALLOWANCE: u64 = 10_000;

        for &(node_id, node_id_size, node_spec) in NODE_SPECS {
            let counter_size = 24 - node_id_size;
            let mut g = Scru64Generator::parse(node_spec).unwrap();

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_reset_core(ts, ALLOWANCE);
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == node_id);

                prev = curr;
            }

            // keep monotonic order under mildly decreasing timestamps
            ts += ALLOWANCE * 16;
            prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts -= 16;
                let curr = g.generate_or_reset_core(ts, ALLOWANCE);
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == node_id);

                prev = curr;
            }

            // reset state with significantly decreasing timestamps
            ts += ALLOWANCE * 16;
            prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts -= ALLOWANCE;
                let curr = g.generate_or_reset_core(ts, ALLOWANCE);
                assert!(prev > curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == node_id);

                prev = curr;
            }
        }
    }

    /// Tests `generate_or_abort_core()`.
    #[test]
    fn generate_or_abort() {
        const N_LOOPS: usize = 64;
        const ALLOWANCE: u64 = 10_000;

        for &(node_id, node_id_size, node_spec) in NODE_SPECS {
            let counter_size = 24 - node_id_size;
            let mut g = Scru64Generator::parse(node_spec).unwrap();

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == node_id);

                prev = curr;
            }

            // keep monotonic order under mildly decreasing timestamps
            ts += ALLOWANCE * 16;
            prev = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            for _ in 0..N_LOOPS {
                ts -= 16;
                let curr = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == node_id);

                prev = curr;
            }

            // abort with significantly decreasing timestamps
            ts += ALLOWANCE * 16;
            g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            ts -= ALLOWANCE;
            for _ in 0..N_LOOPS {
                ts -= 16;
                assert!(g.generate_or_abort_core(ts, ALLOWANCE).is_none());
            }
        }
    }

    /// Tests if generator methods embed up-to-date timestamps.
    #[cfg(feature = "std")]
    #[test]
    fn system_clock() {
        fn now() -> u64 {
            use std::time;
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis() as u64
                >> 8
        }

        for &(_, _, node_spec) in NODE_SPECS {
            let mut g = Scru64Generator::parse(node_spec).unwrap();
            let mut ts_now = now();
            let mut x = g.generate().unwrap();
            assert!((x.timestamp() - ts_now) <= 1);

            ts_now = now();
            x = g.generate_or_reset();
            assert!((x.timestamp() - ts_now) <= 1);
        }
    }
}
