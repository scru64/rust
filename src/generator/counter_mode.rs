//! Types to customize the counter behavior of [`Scru64Generator`].

use crate::NODE_CTR_SIZE;

#[cfg(doc)]
use super::Scru64Generator;

/// A trait to customize the initial counter value for each new timestamp.
///
/// [`Scru64Generator`] calls `init_counter()` to obtain the initial counter value when the
/// `timestamp` field has changed since the immediately preceding ID. Types implementing this trait
/// may apply their respective logic to calculate the initial counter value.
pub trait InitCounter {
    /// Returns the next initial counter value of `counter_size` bits.
    ///
    /// [`Scru64Generator`] passes the `counter_size` (from 1 to 23) and other context information
    /// that might be useful for counter initialization. The returned value must be within the
    /// range of `counter_size`-bit unsigned integer.
    fn init_counter(&mut self, counter_size: u8, context: &InitCounterContext) -> u32;
}

/// Represents the context information provided by [`Scru64Generator`] to [`InitCounter`].
#[derive(Debug)]
#[non_exhaustive]
pub struct InitCounterContext {
    pub timestamp: u64,
    pub node_id: u32,
}

/// The zero-starting counter mode.
///
/// With this strategy, the counter is reset to zero for each new `timestamp` tick.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct ZeroStarting;

impl InitCounter for ZeroStarting {
    fn init_counter(&mut self, _: u8, _: &InitCounterContext) -> u32 {
        0
    }
}

/// The partial random counter mode.
///
/// With this strategy, the counter is reset to a random number for each new `timestamp` tick, but
/// some specified leading bits are set to zero to reserve space as the counter overflow guard.
///
/// Note that the random number generator employed is not cryptographically strong nor is securely
/// seeded. This mode does not pay for security because a small random number is insecure anyway.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartialRandom {
    overflow_guard_size: u8,
    rng: u64,
}

impl Default for PartialRandom {
    /// Equivalent to `PartialRandom::new(1)`.
    fn default() -> Self {
        Self::new(1)
    }
}

impl PartialRandom {
    /// Creates a new instance with the size (in bits) of overflow guard bits.
    pub const fn new(overflow_guard_size: u8) -> Self {
        assert!(overflow_guard_size < NODE_CTR_SIZE);
        Self {
            overflow_guard_size,
            rng: 0, // zero indicates uninitialized state
        }
    }

    /// Initializes the random number generator.
    #[cold]
    fn new_rng(&self, counter_size: u8, context: &InitCounterContext) -> u64 {
        // use context and variable addresses as seed
        #[cfg(feature = "std")]
        let addr = Box::into_raw(Box::new(42)) as u64;
        #[cfg(not(feature = "std"))]
        let addr = (self as *const Self) as u64;

        addr ^ ((context.timestamp << NODE_CTR_SIZE) | ((context.node_id as u64) << counter_size))
    }
}

impl InitCounter for PartialRandom {
    fn init_counter(&mut self, counter_size: u8, context: &InitCounterContext) -> u32 {
        debug_assert!(counter_size < NODE_CTR_SIZE);
        if self.rng == 0 {
            self.rng = self.new_rng(counter_size, context);
        }

        if self.overflow_guard_size < counter_size {
            let shift = 64 + self.overflow_guard_size - counter_size;

            // xorshift64* (Vigna 2016)
            self.rng ^= self.rng >> 12;
            self.rng ^= self.rng << 25;
            self.rng ^= self.rng >> 27;
            (self.rng.wrapping_mul(2685821657736338717) >> shift) as u32
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mock_context() -> InitCounterContext {
        InitCounterContext {
            timestamp: 0x0123_4567_89ab,
            node_id: 0,
        }
    }

    /// `ZeroStarting` always returns zero.
    #[test]
    fn zero_starting() {
        const N: usize = 1024;

        let context = mock_context();
        for counter_size in 1..NODE_CTR_SIZE {
            let mut c = ZeroStarting;
            for _ in 0..N {
                assert_eq!(c.init_counter(counter_size, &context), 0);
            }
        }
    }

    /// `PartialRandom` returns random numbers, setting the leading guard bits to zero.
    #[test]
    fn partial_random() {
        const N: usize = 1024;
        // set margin based on binom dist 99.999% confidence interval
        let margin = 4.417173 * (0.5 * 0.5 / N as f64).sqrt();

        let context = mock_context();
        for counter_size in 1..NODE_CTR_SIZE {
            for overflow_guard_size in 0..NODE_CTR_SIZE {
                // count number of set bits by bit position (from LSB to MSB)
                let mut counts_by_pos = [0u32; NODE_CTR_SIZE as usize];

                let mut c = PartialRandom::new(overflow_guard_size);
                for _ in 0..N {
                    let mut n = c.init_counter(counter_size, &context);
                    for e in counts_by_pos.iter_mut() {
                        *e += n & 1;
                        n >>= 1;
                    }
                }

                let filled = counter_size.saturating_sub(overflow_guard_size) as usize;
                for &e in counts_by_pos[..filled].iter() {
                    assert!((e as f64 / N as f64 - 0.5).abs() < margin);
                }
                for &e in counts_by_pos[filled..].iter() {
                    assert_eq!(e, 0);
                }
            }
        }
    }
}
