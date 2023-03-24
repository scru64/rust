#[cfg(not(feature = "std"))]
use core as std;
use std::{fmt, str};

use fstr::FStr;

use crate::NODE_CTR_SIZE;

/// The maximum valid value of the `timestamp` field.
const MAX_TIMESTAMP: u64 = Scru64Id::MAX.to_u64() >> NODE_CTR_SIZE;

/// The maximum valid value of the combined `node_ctr` field.
const MAX_NODE_CTR: u32 = (1 << NODE_CTR_SIZE) - 1;

/// Digit characters used in the Base36 notation.
const DIGITS: [u8; 36] = *b"0123456789abcdefghijklmnopqrstuvwxyz";

/// An O(1) map from ASCII code points to Base36 digit values.
const DECODE_MAP: [u8; 256] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
    0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
    0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
];

/// Represents a SCRU64 ID.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
#[repr(transparent)]
pub struct Scru64Id(u64);

impl Scru64Id {
    /// The minimum valid value (i.e., `000000000000`).
    pub const MIN: Self = Scru64Id(0u64);

    /// The maximum valid value (i.e., `zzzzzzzzzzzz`).
    pub const MAX: Self = Scru64Id(36u64.pow(12) - 1);

    /// Returns the integer representation.
    pub const fn to_u64(self) -> u64 {
        self.0
    }

    /// Creates a value from a 64-bit integer in the `const` context.
    ///
    /// # Panics
    ///
    /// Panics if the argument is out of the valid value range.
    pub const fn const_from_u64(value: u64) -> Self {
        match Self::try_from_u64(value) {
            Ok(t) => t,
            Err(_) => panic!("out of valid integer range"),
        }
    }

    /// Creates a value from a 64-bit integer in the `const` context.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the argument is out of the valid value range.
    const fn try_from_u64(value: u64) -> Result<Self, ConversionError> {
        if value <= Self::MAX.0 {
            Ok(Self(value))
        } else {
            Err(ConversionError::OutOfRange)
        }
    }

    /// Returns the 12-digit canonical string representation stored in a stack-allocated
    /// string-like type that can be handled like [`String`] through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use scru64::Scru64Id;
    ///
    /// let x = "0u2r87q2rol5".parse::<Scru64Id>()?;
    /// let y = x.encode();
    /// assert_eq!(y, "0u2r87q2rol5");
    /// assert_eq!(format!("{y}"), "0u2r87q2rol5");
    /// # Ok::<(), scru64::ConversionError>(())
    /// ```
    pub const fn encode(self) -> FStr<12> {
        let mut buffer = [0u8; 12];
        let mut n = self.0;
        let mut i = buffer.len();
        while i > 0 {
            i -= 1;
            let (quo, rem) = (n / 36, n % 36);
            buffer[i] = DIGITS[rem as usize];
            n = quo;
        }
        // SAFETY: ok because buffer consists of ASCII code points
        debug_assert!(str::from_utf8(&buffer).is_ok());
        unsafe { FStr::from_inner_unchecked(buffer) }
    }

    /// Creates a value from a 12-digit string representation in the `const` context.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a valid string representation.
    pub const fn const_from_str(value: &str) -> Self {
        match Self::try_from_str(value) {
            Ok(t) => t,
            Err(_) => panic!("invalid string representation"),
        }
    }

    /// Creates a value from a 12-digit string representation in the `const` context.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the argument is not a valid string representation.
    const fn try_from_str(value: &str) -> Result<Self, ConversionError> {
        if value.len() != 12 {
            Err(ConversionError::InvalidLength)
        } else {
            let buffer = value.as_bytes();
            let mut n = 0u64;
            let mut i = 0;
            while i < value.len() {
                let e = DECODE_MAP[buffer[i] as usize];
                if e == 0xff {
                    return Err(ConversionError::InvalidDigit);
                }
                n = n * 36 + e as u64;
                i += 1;
            }
            Self::try_from_u64(n)
        }
    }

    /// Returns the `timestamp` field value.
    pub const fn timestamp(self) -> u64 {
        self.0 >> NODE_CTR_SIZE
    }

    /// Returns the `node_id` and `counter` field values combined as a single integer.
    pub const fn node_ctr(self) -> u32 {
        self.0 as u32 & MAX_NODE_CTR
    }

    /// Creates a value from the `timestamp` and the combined `node_ctr` field value.
    ///
    /// # Panics
    ///
    /// Panics if any argument is out of the valid value range.
    pub const fn from_parts(timestamp: u64, node_ctr: u32) -> Self {
        assert!(timestamp <= MAX_TIMESTAMP, "`timestamp` out of range");
        assert!(node_ctr <= MAX_NODE_CTR, "`node_ctr` out of range");
        Self(timestamp << NODE_CTR_SIZE | node_ctr as u64)
    }
}

impl From<Scru64Id> for u64 {
    fn from(value: Scru64Id) -> Self {
        value.to_u64()
    }
}

impl TryFrom<u64> for Scru64Id {
    type Error = ConversionError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::try_from_u64(value)
    }
}

impl From<Scru64Id> for i64 {
    fn from(value: Scru64Id) -> Self {
        value.to_u64() as i64
    }
}

impl TryFrom<i64> for Scru64Id {
    type Error = ConversionError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        // cast negative numbers to so large numbers that try_from_u64 rejects
        Self::try_from(value as u64)
    }
}

impl fmt::Display for Scru64Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.encode())
    }
}

impl str::FromStr for Scru64Id {
    type Err = ConversionError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(value)
    }
}

/// An error converting a value into SCRU64 ID.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ConversionError {
    /// Out of valid integer range.
    OutOfRange,

    /// Invalid length of string.
    InvalidLength,

    /// Invalid digit char found.
    InvalidDigit,
}

impl fmt::Display for ConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("could not convert to SCRU64 ID: ")?;
        match self {
            Self::OutOfRange => f.write_str("out of valid integer range"),
            Self::InvalidLength => f.write_str("invalid length of string"),
            Self::InvalidDigit => f.write_str("invalid digit char found"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::{ConversionError, Scru64Id};

    impl TryFrom<String> for Scru64Id {
        type Error = ConversionError;

        fn try_from(value: String) -> Result<Self, Self::Error> {
            value.parse()
        }
    }

    impl From<Scru64Id> for String {
        fn from(object: Scru64Id) -> Self {
            object.encode().into()
        }
    }

    impl std::error::Error for ConversionError {}
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde_support {
    use super::{fmt, Scru64Id};
    use serde::{de, Deserializer, Serializer};

    impl serde::Serialize for Scru64Id {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            if serializer.is_human_readable() {
                serializer.serialize_str(&self.encode())
            } else {
                serializer.serialize_u64(self.to_u64())
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for Scru64Id {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            if deserializer.is_human_readable() {
                deserializer.deserialize_str(VisitorImpl)
            } else {
                deserializer.deserialize_u64(VisitorImpl)
            }
        }
    }

    struct VisitorImpl;

    impl<'de> de::Visitor<'de> for VisitorImpl {
        type Value = Scru64Id;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a SCRU64 ID representation")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            value.parse().map_err(de::Error::custom)
        }

        fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
            Self::Value::try_from(value).map_err(de::Error::custom)
        }

        fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
            Self::Value::try_from(value).map_err(de::Error::custom)
        }
    }
}
