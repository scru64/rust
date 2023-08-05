//! SCRU64 generator and related items.

#[cfg(not(feature = "std"))]
use core as std;
use std::fmt;

use pcg32::Pcg32;

use crate::{Scru64Id, NODE_CTR_SIZE};

pub mod counter_mode;

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod global_gen;

#[cfg(feature = "std")]
pub use global_gen::GlobalGenerator;

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
    /// Creates a new generator with a given node configuration.
    ///
    /// The `node_id` must fit in `node_id_size` bits, where `node_id_size` ranges from 1 to 23,
    /// inclusive.
    ///
    /// # Panics
    ///
    /// Panics if the arguments represent an invalid node configuration.
    pub fn new(node_id: u32, node_id_size: u8) -> Self {
        verify_node(node_id, node_id_size).unwrap_or_else(|err| panic!("{err}"));
        Self::restore(
            Scru64Id::from_parts(0, node_id << (NODE_CTR_SIZE - node_id_size)),
            node_id_size,
        )
    }

    /// Restores the generator state from the immediately preceding SCRU64 ID and `node_id_size`
    /// parameter.
    ///
    /// The returned generator refers to `node_prev` as the source of `node_id` and as the
    /// preceding ID when generating a monotonically increasing ID.
    ///
    /// # Panics
    ///
    /// Panics if `node_id_size` is zero or greater than 23.
    pub fn restore(node_prev: Scru64Id, node_id_size: u8) -> Self {
        verify_node_id_size(node_id_size).unwrap_or_else(|err| panic!("{err}"));
        let counter_size = NODE_CTR_SIZE - node_id_size;
        let seed = &counter_size as *const u8; // use local var address as seed
        Self {
            prev: node_prev,
            counter_size,
            rng: Pcg32::new(node_prev.to_u64(), seed as u64),
        }
    }

    /// Creates a generator by parsing a node spec string that describes the node configuration.
    ///
    /// A node spec string starts with a decimal `node_id` or 12-digit `node_prev` value, followed
    /// by a slash and a decimal `node_id_size` value ranging from 1 to 23 (e.g., `"42/8"`,
    /// `"0u2r85hm2pt3/16"`). The first form creates a fresh new generator with the given `node_id`,
    /// while the second form constructs one that generates subsequent IDs to the `node_prev`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the node spec does not conform to the valid syntax or represents an
    /// invalid node configuration.
    pub fn parse(node_spec: &str) -> Result<Self, NodeSpecError> {
        use NodeSpecError::Syntax;
        let mut iter = node_spec.split('/');
        let x = iter.next().ok_or(Syntax)?;
        let y = iter.next().ok_or(Syntax)?;
        if iter.next().is_some()
            || x.starts_with('+')
            || x.len() > 12
            || y.starts_with('+')
            || y.len() > 3
        {
            return Err(Syntax);
        }

        let node_id_size: u8 = y.parse().or(Err(Syntax))?;
        if x.len() == 12 {
            let node_prev = x.parse().or(Err(Syntax))?;
            verify_node_id_size(node_id_size)?;
            Ok(Self::restore(node_prev, node_id_size))
        } else {
            let node_id = x.parse().or(Err(Syntax))?;
            verify_node(node_id, node_id_size)?;
            Ok(Self::new(node_id, node_id_size))
        }
    }

    /// Returns the immediately preceding ID that the generator generated.
    pub const fn node_prev(&self) -> Option<Scru64Id> {
        if self.prev.timestamp() > 0 {
            Some(self.prev)
        } else {
            None
        }
    }

    /// Returns the `node_id` of the generator.
    pub const fn node_id(&self) -> u32 {
        self.prev.node_ctr() >> self.counter_size
    }

    /// Returns the size in bits of the `node_id` adopted by the generator.
    pub const fn node_id_size(&self) -> u8 {
        NODE_CTR_SIZE - self.counter_size
    }

    /// Writes the node spec string describing `self` into a `buffer`.
    #[cfg_attr(not(feature = "std"), allow(dead_code))]
    fn write_node_spec(&self, buffer: &mut impl fmt::Write) -> fmt::Result {
        if let Some(prev) = self.node_prev() {
            write!(buffer, "{}/{}", prev, self.node_id_size())
        } else {
            write!(buffer, "{}/{}", self.node_id(), self.node_id_size())
        }
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
        /// Returns the node spec string that revives the current generator state through
        /// [`Scru64Generator::parse`].
        pub fn node_spec(&self) -> String {
            let mut buffer = String::new();
            self.write_node_spec(&mut buffer)
                .expect("could not write `node_spec` into `String`");
            buffer
        }

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

/// Tests if `node_id_size` is within the valid value range.
const fn verify_node_id_size(node_id_size: u8) -> Result<(), NodeSpecError> {
    if 0 < node_id_size && node_id_size < NODE_CTR_SIZE {
        Ok(())
    } else {
        Err(NodeSpecError::NodeIdSizeRange)
    }
}

/// Tests if a pair of `node_id` and `node_id_size` is valid.
const fn verify_node(node_id: u32, node_id_size: u8) -> Result<(), NodeSpecError> {
    match verify_node_id_size(node_id_size) {
        Ok(_) => match node_id >> node_id_size {
            0 => Ok(()),
            _ => Err(NodeSpecError::NodeIdRange),
        },
        err => err,
    }
}

/// An error parsing a node spec string.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum NodeSpecError {
    /// Invalid node spec syntax.
    Syntax,

    /// `node_id` is greater than the `node_id_size` range.
    NodeIdRange,

    /// `node_id_size` is zero or greater than 23.
    NodeIdSizeRange,
}

impl fmt::Display for NodeSpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax => {
                f.write_str("invalid `node_spec`; it looks like: `42/8`, `0u2r85hm2pt3/16`")
            }
            Self::NodeIdRange => f.write_str("`node_id` must fit in `node_id_size` bits"),
            Self::NodeIdSizeRange => f.write_str("`node_id_size` must range from 1 to 23"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for NodeSpecError {}

#[cfg(test)]
mod tests {
    use super::{Scru64Generator, Scru64Id};
    use crate::test_cases::EXAMPLE_NODE_SPECS;

    /// Initializes with node ID and size pair and node spec string.
    #[test]
    fn constructor() {
        for e in EXAMPLE_NODE_SPECS {
            let node_prev = Scru64Id::const_from_u64(e.node_prev);

            let newed = Scru64Generator::new(e.node_id, e.node_id_size);
            assert_eq!(newed.node_id(), e.node_id);
            assert_eq!(newed.node_id_size(), e.node_id_size);
            if e.spec_type == "new" {
                assert_eq!(newed.prev, node_prev);
            }

            let parsed = Scru64Generator::parse(e.node_spec).unwrap();
            assert_eq!(parsed.node_id(), e.node_id);
            assert_eq!(parsed.node_id_size(), e.node_id_size);
            assert_eq!(parsed.prev, node_prev);

            let restored = Scru64Generator::restore(node_prev, e.node_id_size);
            assert_eq!(restored.node_id(), e.node_id);
            assert_eq!(restored.node_id_size(), e.node_id_size);
            assert_eq!(restored.prev, node_prev);

            #[cfg(feature = "std")]
            {
                if e.spec_type == "new" {
                    assert_eq!(newed.node_spec(), e.node_spec);
                }
                assert_eq!(parsed.node_spec(), e.node_spec);
                assert_eq!(restored.node_spec(), e.node_spec);
            }
        }
    }

    /// Fails to initialize with invalid node spec string.
    #[test]
    fn constructor_error() {
        let cases = [
            "",
            "42",
            "/8",
            "42/",
            " 42/8",
            "42/8 ",
            " 42/8 ",
            "42 / 8",
            "+42/8",
            "42/+8",
            "-42/8",
            "42/-8",
            "ab/8",
            "0x42/8",
            "1/2/3",
            "0/0",
            "0/24",
            "8/1",
            "1024/8",
            "0000000000001/8",
            "1/0016",
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

    /// Normally generates monotonic IDs or resets state upon significant rollback.
    #[test]
    fn generate_or_reset() {
        const N_LOOPS: usize = 64;
        const ALLOWANCE: u64 = 10_000;

        for e in EXAMPLE_NODE_SPECS {
            let counter_size = 24 - e.node_id_size;
            let mut g = Scru64Generator::new(e.node_id, e.node_id_size);

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_reset_core(ts, ALLOWANCE);
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

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
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

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
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

                prev = curr;
            }
        }
    }

    /// Normally generates monotonic IDs or aborts upon significant rollback.
    #[test]
    fn generate_or_abort() {
        const N_LOOPS: usize = 64;
        const ALLOWANCE: u64 = 10_000;

        for e in EXAMPLE_NODE_SPECS {
            let counter_size = 24 - e.node_id_size;
            let mut g = Scru64Generator::new(e.node_id, e.node_id_size);

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
                test_consecutive_pair(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

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
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

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

    /// Embeds up-to-date timestamp.
    #[cfg(feature = "std")]
    #[test]
    fn clock_integration() {
        fn now() -> u64 {
            use std::time;
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis() as u64
                >> 8
        }

        for e in EXAMPLE_NODE_SPECS {
            let mut g = Scru64Generator::new(e.node_id, e.node_id_size);
            let mut ts_now = now();
            let mut x = g.generate().unwrap();
            assert!((x.timestamp() - ts_now) <= 1);

            ts_now = now();
            x = g.generate_or_reset();
            assert!((x.timestamp() - ts_now) <= 1);
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde_support {
    #[cfg(not(feature = "std"))]
    use core as std;
    use std::{fmt, str};

    use super::Scru64Generator;
    use serde::{de, Deserializer, Serializer};

    impl serde::Serialize for Scru64Generator {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let mut buffer = fstr::FStr::<16>::repeat(b'\0');
            self.write_node_spec(&mut buffer.writer()).unwrap();
            serializer.serialize_str(buffer.slice_to_terminator('\0'))
        }
    }

    impl<'de> serde::Deserialize<'de> for Scru64Generator {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_str(VisitorImpl)
        }
    }

    struct VisitorImpl;

    impl<'de> de::Visitor<'de> for VisitorImpl {
        type Value = Scru64Generator;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a SCRU64 node spec string")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            Self::Value::parse(value).map_err(de::Error::custom)
        }

        fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
            match str::from_utf8(value) {
                Ok(str_value) => self.visit_str(str_value),
                _ => Err(de::Error::invalid_value(
                    de::Unexpected::Bytes(value),
                    &self,
                )),
            }
        }
    }

    /// Supports serialization and deserialization.
    #[cfg(test)]
    #[test]
    fn test() {
        use serde::{Deserialize, Serialize};
        use serde_test::Token;

        #[derive(Debug)]
        struct CustomEqWrapper(Scru64Generator);
        impl PartialEq for CustomEqWrapper {
            fn eq(&self, other: &CustomEqWrapper) -> bool {
                self.0.prev == other.0.prev && self.0.counter_size == other.0.counter_size
            }
        }
        impl Serialize for CustomEqWrapper {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                Scru64Generator::serialize(&self.0, serializer)
            }
        }
        impl<'de> Deserialize<'de> for CustomEqWrapper {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                Ok(CustomEqWrapper(Scru64Generator::deserialize(deserializer)?))
            }
        }

        for e in crate::test_cases::EXAMPLE_NODE_SPECS {
            let x = CustomEqWrapper(Scru64Generator::parse(e.node_spec).unwrap());
            serde_test::assert_tokens(&x, &[Token::Str(e.node_spec)]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.node_spec.as_bytes())]);
        }
    }
}
