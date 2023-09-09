//! SCRU64 generator and related items.

use crate::{Scru64Id, NODE_CTR_SIZE};

mod node_spec;
pub use node_spec::{NodeSpec, NodeSpecError, NodeSpecParseError};

pub mod counter_mode;
use counter_mode::{CounterMode, DefaultCounterMode, RenewContext};

#[cfg(feature = "global_gen")]
#[cfg_attr(docsrs, doc(cfg(feature = "global_gen")))]
mod global_gen;

#[cfg(feature = "global_gen")]
pub use global_gen::GlobalGenerator;

/// Represents a SCRU64 ID generator.
///
/// The generator comes with several different methods that generate a SCRU64 ID:
///
/// | Flavor                     | Timestamp | On big clock rewind |
/// | -------------------------- | --------- | ------------------- |
/// | [`generate`]               | Now       | Returns `None`      |
/// | [`generate_or_reset`]      | Now       | Resets generator    |
/// | [`generate_or_abort_core`] | Argument  | Returns `None`      |
/// | [`generate_or_reset_core`] | Argument  | Resets generator    |
///
/// All of these methods return a monotonically increasing ID by reusing the previous `timestamp`
/// even if the one provided is smaller than the immediately preceding ID's, unless such a clock
/// rollback is considered significant (by default, approx. 10 seconds). A clock rollback may also
/// be detected when a generator has generated too many IDs within a certain unit of time, because
/// this implementation increments the previous `timestamp` when `counter` reaches the limit to
/// continue instant monotonic generation. When a significant clock rollback is detected:
///
/// 1.  `generate` (or_abort) methods abort and return `None` immediately.
/// 2.  `or_reset` variants reset the generator and return a new ID based on the given `timestamp`,
///     breaking the increasing order of IDs.
///
/// The `core` functions offer low-level primitives to customize the behavior.
///
/// [`generate`]: Scru64Generator::generate
/// [`generate_or_reset`]: Scru64Generator::generate_or_reset
/// [`generate_or_abort_core`]: Scru64Generator::generate_or_abort_core
/// [`generate_or_reset_core`]: Scru64Generator::generate_or_reset_core
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scru64Generator<C = DefaultCounterMode> {
    prev: Scru64Id,
    counter_size: u8,
    counter_mode: C,
}

impl Scru64Generator {
    /// Creates a new generator with the given node configuration.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scru64::generator::Scru64Generator;
    ///
    /// let g = Scru64Generator::new("42/8".parse()?);
    /// # Ok::<(), scru64::generator::NodeSpecParseError>(())
    /// ```
    pub const fn new(node_spec: NodeSpec) -> Self {
        if node_spec.node_id_size() < 20 {
            Self::with_counter_mode(node_spec, DefaultCounterMode::new(0))
        } else {
            // reserve one overflow guard bit if `counter_size` is very small
            Self::with_counter_mode(node_spec, DefaultCounterMode::new(1))
        }
    }
}

impl<C> Scru64Generator<C> {
    /// Returns the `node_id` of the generator.
    pub const fn node_id(&self) -> u32 {
        self.prev.node_ctr() >> self.counter_size
    }

    /// Returns the size in bits of the `node_id` adopted by the generator.
    pub const fn node_id_size(&self) -> u8 {
        NODE_CTR_SIZE - self.counter_size
    }

    /// Returns the node configuration specifier describing the generator state.
    pub fn node_spec(&self) -> NodeSpec {
        match NodeSpec::with_node_prev(self.prev, self.node_id_size()) {
            Ok(t) => t,
            Err(_) => unreachable!(),
        }
    }
}

impl<C: CounterMode> Scru64Generator<C> {
    /// Creates a new generator with the given node configuration and counter initialization mode.
    pub const fn with_counter_mode(node_spec: NodeSpec, counter_mode: C) -> Self {
        Self {
            prev: node_spec.node_prev_raw(),
            counter_size: NODE_CTR_SIZE - node_spec.node_id_size(),
            counter_mode,
        }
    }

    /// Calculates the combined `node_ctr` field value for the next `timestamp` tick.
    fn renew_node_ctr(&mut self, timestamp: u64) -> u32 {
        let node_id = self.node_id();
        let context = RenewContext { timestamp, node_id };
        let counter = self.counter_mode.renew(self.counter_size, &context);
        assert!(
            counter < (1 << self.counter_size),
            "illegal `CounterMode` implementation"
        );
        (node_id << self.counter_size) | counter
    }

    /// Generates a new SCRU64 ID object from a Unix timestamp in milliseconds, or resets the
    /// generator upon significant timestamp rollback.
    ///
    /// See the [`Scru64Generator`] type documentation for the description.
    ///
    /// Note that this mode of generation is not recommended because rewinding `timestamp` without
    /// changing `node_id` considerably increases the risk of duplicate results.
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
            let timestamp = unix_ts_ms >> 8;
            self.prev = Scru64Id::from_parts(timestamp, self.renew_node_ctr(timestamp)).unwrap();
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
            self.prev = Scru64Id::from_parts(timestamp, self.renew_node_ctr(timestamp)).unwrap();
        } else if timestamp + allowance >= prev_timestamp {
            // go on with previous timestamp if new one is not much smaller
            let prev_node_ctr = self.prev.node_ctr();
            let counter_mask = (1u32 << self.counter_size) - 1;
            if (prev_node_ctr & counter_mask) < counter_mask {
                self.prev = Scru64Id::from_parts(prev_timestamp, prev_node_ctr + 1).unwrap();
            } else {
                // increment timestamp at counter overflow
                self.prev = Scru64Id::from_parts(
                    prev_timestamp + 1,
                    self.renew_node_ctr(prev_timestamp + 1),
                )
                .expect("`timestamp` and `counter` reached max; no more ID available");
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
    use super::{CounterMode, Scru64Generator, Scru64Id};

    /// Returns the current Unix timestamp in milliseconds.
    fn unix_ts_ms() -> u64 {
        use std::time;
        time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .expect("clock may have gone backwards")
            .as_millis() as u64
    }

    impl<C: CounterMode> Scru64Generator<C> {
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
        ///
        /// Note that this mode of generation is not recommended because rewinding `timestamp`
        /// without changing `node_id` considerably increases the risk of duplicate results.
        pub fn generate_or_reset(&mut self) -> Scru64Id {
            self.generate_or_reset_core(unix_ts_ms(), 10_000)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{NodeSpec, Scru64Generator, Scru64Id};
    use crate::test_cases::EXAMPLE_NODE_SPECS;

    fn assert_consecutive(first: Scru64Id, second: Scru64Id) {
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
            let node_spec = NodeSpec::with_node_id(e.node_id, e.node_id_size).unwrap();
            let mut g = Scru64Generator::new(node_spec);

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_reset_core(ts, ALLOWANCE);
                assert_consecutive(prev, curr);
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
                assert_consecutive(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

                prev = curr;
            }

            // reset state with significantly decreasing timestamps
            ts += ALLOWANCE * 16;
            prev = g.generate_or_reset_core(ts, ALLOWANCE);
            for _ in 0..N_LOOPS {
                ts -= ALLOWANCE + 0x100;
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
            let node_spec = NodeSpec::with_node_id(e.node_id, e.node_id_size).unwrap();
            let mut g = Scru64Generator::new(node_spec);

            // happy path
            let mut ts = 1_577_836_800_000u64; // 2020-01-01
            let mut prev = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            for _ in 0..N_LOOPS {
                ts += 16;
                let curr = g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
                assert_consecutive(prev, curr);
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
                assert_consecutive(prev, curr);
                assert!((curr.timestamp() - (ts >> 8)) < (ALLOWANCE >> 8));
                assert!((curr.node_ctr() >> counter_size) == e.node_id);

                prev = curr;
            }

            // abort with significantly decreasing timestamps
            ts += ALLOWANCE * 16;
            g.generate_or_abort_core(ts, ALLOWANCE).unwrap();
            ts -= ALLOWANCE + 0x100;
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
            let node_spec = NodeSpec::with_node_id(e.node_id, e.node_id_size).unwrap();
            let mut g = Scru64Generator::new(node_spec);
            let mut ts_now = now();
            let mut x = g.generate().unwrap();
            assert!((x.timestamp() - ts_now) <= 1);

            ts_now = now();
            x = g.generate_or_reset();
            assert!((x.timestamp() - ts_now) <= 1);
        }
    }
}
