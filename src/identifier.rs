#[cfg(not(feature = "std"))]
use core as std;
use std::{any, fmt, str};

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

    /// Creates a value from a 64-bit integer in the `const` context.
    ///
    /// # Panics
    ///
    /// Panics if the argument is larger than `36^12 - 1`.
    pub const fn const_from_u64(value: u64) -> Self {
        match Self::try_from_u64(value) {
            Ok(t) => t,
            Err(_) => panic!("could not convert integer to SCRU64 ID: `u64` out of range"),
        }
    }

    /// Creates a value from a 64-bit integer in the `const` context.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the argument is larger than `36^12 - 1`.
    const fn try_from_u64(value: u64) -> Result<Self, RangeError<u64>> {
        if value <= Self::MAX.0 {
            Ok(Self(value))
        } else {
            Err(RangeError { value })
        }
    }

    /// Returns the integer representation.
    pub const fn to_u64(self) -> u64 {
        self.0
    }

    /// Creates a value from the `timestamp` and the combined `node_ctr` field value.
    ///
    /// # Errors
    ///
    /// Returns `Err` if any argument is larger than their respective maximum value
    /// (`36^12 / 2^24 - 1` and `2^24 - 1`, respectively).
    pub const fn from_parts(timestamp: u64, node_ctr: u32) -> Result<Self, PartsError> {
        if timestamp <= MAX_TIMESTAMP && node_ctr <= MAX_NODE_CTR {
            // no further check is necessary because `MAX_SCRU64_INT` happens to equal
            // `MAX_TIMESTAMP << 24 | MAX_NODE_CTR`
            Ok(Self(timestamp << NODE_CTR_SIZE | node_ctr as u64))
        } else {
            Err(PartsError {
                timestamp,
                node_ctr,
            })
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

    /// Creates a value from a 12-digit string representation in the `const` context.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a valid string representation.
    pub const fn const_from_str(value: &str) -> Self {
        match Self::try_from_str(value) {
            Ok(t) => t,
            Err(_) => panic!("could not parse string as SCRU64 ID"),
        }
    }

    /// Creates a value from a 12-digit string representation in the `const` context.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the argument is not a valid string representation.
    const fn try_from_str(value: &str) -> Result<Self, ParseError> {
        if value.len() != 12 {
            Err(ParseError::invalid_length(value.len()))
        } else {
            let buffer = value.as_bytes();
            let mut n = 0u64;
            let mut i = 0;
            while i < value.len() {
                let e = DECODE_MAP[buffer[i] as usize];
                if e == 0xff {
                    return Err(ParseError::invalid_digit(value, i));
                }
                n = n * 36 + e as u64;
                i += 1;
            }
            match Self::try_from_u64(n) {
                Ok(t) => Ok(t),
                Err(_) => unreachable!(),
            }
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
    /// assert_eq!(format!("{}", y), "0u2r87q2rol5");
    /// # Ok::<(), scru64::ParseError>(())
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
        debug_assert!(n == 0);

        // SAFETY: ok because buffer consists of ASCII code points
        debug_assert!(str::from_utf8(&buffer).is_ok());
        unsafe { FStr::from_inner_unchecked(buffer) }
    }
}

impl TryFrom<u64> for Scru64Id {
    type Error = RangeError<u64>;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::try_from_u64(value)
    }
}

impl From<Scru64Id> for u64 {
    fn from(value: Scru64Id) -> Self {
        value.to_u64()
    }
}

impl TryFrom<i64> for Scru64Id {
    type Error = RangeError<i64>;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        // cast negative numbers to so large numbers that try_from_u64 rejects
        Self::try_from(value as u64).map_err(|_| RangeError { value })
    }
}

impl From<Scru64Id> for i64 {
    fn from(value: Scru64Id) -> Self {
        value.to_u64() as i64
    }
}

impl str::FromStr for Scru64Id {
    type Err = ParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::try_from_str(value)
    }
}

impl fmt::Display for Scru64Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.encode().as_str(), f)
    }
}

/// An error converting an integer into a SCRU64 ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangeError<T> {
    value: T,
}

impl<T: fmt::Display> fmt::Display for RangeError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "could not convert integer to SCRU64 ID: `{}` out of range: {}",
            any::type_name::<T>(),
            self.value
        )
    }
}

/// An error passing invalid arguments to [`Scru64Id::from_parts()`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartsError {
    timestamp: u64,
    node_ctr: u32,
}

impl PartsError {
    /// Returns `true` if `timestamp` is within the valid range.
    pub fn test_timestamp(&self) -> bool {
        self.timestamp <= MAX_TIMESTAMP
    }

    /// Returns `true` if `node_ctr` is within the valid range.
    pub fn test_node_ctr(&self) -> bool {
        self.node_ctr <= MAX_NODE_CTR
    }
}

impl fmt::Display for PartsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "could not create SCRU64 ID from parts: ")?;
        match (self.test_timestamp(), self.test_node_ctr()) {
            (false, false) => write!(f, "`timestamp` and `node_ctr` out of range"),
            (false, true) => write!(f, "`timestamp` out of range"),
            (true, false) => write!(f, "`node_ctr` out of range"),
            (true, true) => unreachable!(),
        }
    }
}

/// An error parsing an invalid string representation of SCRU64 ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    Length {
        n_bytes: usize,
    },
    Digit {
        /// Holds the invalid character as a UTF-8 byte array to work in the const context.
        utf8_char: [u8; 4],
        position: usize,
    },
}

impl ParseError {
    /// Creates an "invalid length" error from the actual length.
    const fn invalid_length(n_bytes: usize) -> Self {
        Self {
            kind: ParseErrorKind::Length { n_bytes },
        }
    }

    /// Creates an "invalid digit" error from the entire string and the position of invalid digit.
    const fn invalid_digit(src: &str, position: usize) -> Self {
        const fn is_char_boundary(utf8_bytes: &[u8], index: usize) -> bool {
            match index {
                0 => true,
                i if i < utf8_bytes.len() => (utf8_bytes[i] as i8) >= -64,
                _ => index == utf8_bytes.len(),
            }
        }

        let bs = src.as_bytes();
        assert!(is_char_boundary(bs, position));
        let mut utf8_char = [bs[position], 0, 0, 0];

        let mut i = 1;
        while !is_char_boundary(bs, position + i) {
            utf8_char[i] = bs[position + i];
            i += 1;
        }

        Self {
            kind: ParseErrorKind::Digit {
                utf8_char,
                position,
            },
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "could not parse string as SCRU64 ID: ")?;
        match self.kind {
            ParseErrorKind::Length { n_bytes } => {
                write!(f, "invalid length: {} bytes (expected 12)", n_bytes)
            }
            ParseErrorKind::Digit {
                utf8_char,
                position,
            } => {
                let chr = str::from_utf8(&utf8_char).unwrap().chars().next().unwrap();
                write!(f, "invalid digit '{}' at {}", chr.escape_debug(), position)
            }
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::{ParseError, RangeError, Scru64Id};

    use std::{error, fmt};

    impl TryFrom<String> for Scru64Id {
        type Error = ParseError;

        fn try_from(value: String) -> Result<Self, Self::Error> {
            value.parse()
        }
    }

    impl From<Scru64Id> for String {
        fn from(object: Scru64Id) -> Self {
            object.encode().into()
        }
    }

    impl<T: fmt::Debug + fmt::Display> error::Error for RangeError<T> {}

    impl error::Error for ParseError {}
}

#[cfg(test)]
mod tests {
    use super::Scru64Id;
    use crate::test_cases::EXAMPLE_IDS;

    /// Supports equality comparison.
    #[test]
    fn eq() {
        #[cfg(feature = "std")]
        let hash = {
            use std::hash::{BuildHasher, Hash, Hasher};
            let s = std::collections::hash_map::RandomState::new();
            move |value: Scru64Id| {
                let mut hasher = s.build_hasher();
                value.hash(&mut hasher);
                hasher.finish()
            }
        };

        let mut prev = Scru64Id::const_from_u64(EXAMPLE_IDS.last().unwrap().num);
        for e in EXAMPLE_IDS {
            let curr = Scru64Id::const_from_u64(e.num);
            let twin = Scru64Id::const_from_u64(e.num);

            assert_eq!(curr, twin);
            assert_eq!(twin, curr);
            assert_eq!(curr.to_u64(), twin.to_u64());
            assert_eq!(curr.encode(), twin.encode());
            assert_eq!(curr.timestamp(), twin.timestamp());
            assert_eq!(curr.node_ctr(), twin.node_ctr());

            assert_ne!(prev, curr);
            assert_ne!(curr, prev);
            assert_ne!(curr.to_u64(), prev.to_u64());
            assert_ne!(curr.encode(), prev.encode());
            assert!((curr.timestamp() != prev.timestamp()) || (curr.node_ctr() != prev.node_ctr()));

            #[cfg(feature = "std")]
            {
                assert_eq!(curr.to_string(), twin.to_string());
                assert_ne!(curr.to_string(), prev.to_string());
                assert_eq!(hash(curr), hash(twin));
                assert_ne!(hash(curr), hash(prev));
            }

            prev = curr;
        }
    }

    /// Supports ordering comparison.
    #[test]
    fn ord() {
        let mut cases = EXAMPLE_IDS.to_vec();
        cases.sort_by_key(|e| e.num);

        let mut iter = cases.iter();
        let mut prev = Scru64Id::const_from_u64(iter.next().unwrap().num);
        while let Some(e) = iter.next() {
            let curr = Scru64Id::const_from_u64(e.num);

            assert!(prev < curr);
            assert!(prev <= curr);

            assert!(curr > prev);
            assert!(curr >= prev);

            assert!(prev.to_u64() < curr.to_u64());
            assert!(prev.encode().as_str() < curr.encode().as_str());

            prev = curr;
        }
    }

    /// Converts to various types.
    #[test]
    fn convert_to() {
        for e in EXAMPLE_IDS {
            let x = Scru64Id::const_from_u64(e.num);

            assert_eq!(x.to_u64(), e.num);
            assert_eq!(u64::from(x), e.num);
            assert_eq!(i64::from(x), e.num.try_into().unwrap());
            assert_eq!(&x.encode(), e.text);
            assert_eq!(x.timestamp(), e.timestamp);
            assert_eq!(x.node_ctr(), e.node_ctr);

            #[cfg(feature = "std")]
            {
                assert_eq!(x.to_string(), e.text);
                assert_eq!(String::from(x), e.text);
                assert_eq!(format!("{}", x), format!("{}", e.text));
                assert_eq!(format!("{:016}", x), format!("{:016}", e.text));
                assert_eq!(format!("{:-^024}", x), format!("{:-^024}", e.text));
            }
        }
    }

    /// Converts from various types.
    #[test]
    fn convert_from() {
        for e in EXAMPLE_IDS {
            let x = Scru64Id::const_from_u64(e.num);

            assert_eq!(x, (e.num as u64).try_into().unwrap());
            assert_eq!(x, (e.num as i64).try_into().unwrap());
            assert_eq!(x, e.text.parse().unwrap());
            assert_eq!(x, Scru64Id::from_parts(e.timestamp, e.node_ctr).unwrap());

            #[cfg(feature = "std")]
            {
                assert_eq!(x, e.text.to_owned().try_into().unwrap());
                assert_eq!(x, e.text.to_ascii_uppercase().parse().unwrap());
                assert_eq!(x, e.text.to_ascii_uppercase().try_into().unwrap());
            }
        }
    }

    /// Rejects integer out of valid range.
    #[test]
    fn from_int_error() {
        assert!(Scru64Id::try_from(36u64.pow(12)).is_err());
        assert!(Scru64Id::try_from(u64::MAX).is_err());

        assert!(Scru64Id::try_from(-1i64).is_err());
        assert!(Scru64Id::try_from(i64::MAX).is_err());
        assert!(Scru64Id::try_from(i64::MIN).is_err());
    }

    /// Fails to parse invalid textual representations.
    #[test]
    fn parse_error() {
        let cases = [
            "",
            " 0u3wrp5g81jx",
            "0u3wrp5g81jy ",
            " 0u3wrp5g81jz ",
            "+0u3wrp5g81k0",
            "-0u3wrp5g81k1",
            "+u3wrp5q7ta5",
            "-u3wrp5q7ta6",
            "0u3w_p5q7ta7",
            "0u3wrp5-7ta8",
            "0u3wrp5q7t 9",
        ];

        for e in cases {
            assert!(e.parse::<Scru64Id>().is_err());
        }
    }

    /// Rejects `MAX + 1` even if passed as pair of fields.
    #[test]
    fn from_parts_error() {
        let max = 36u64.pow(12) - 1;
        assert!(Scru64Id::from_parts(max >> 24, (max as u32 & 0xff_ffff) + 1).is_err());
    }
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
            Self::Value::try_from_str(value).map_err(de::Error::custom)
        }

        fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
            Self::Value::try_from(value).map_err(de::Error::custom)
        }

        fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
            Self::Value::try_from(value).map_err(de::Error::custom)
        }
    }

    /// Supports serialization and deserialization.
    #[cfg(test)]
    #[test]
    fn test() {
        use crate::test_cases::EXAMPLE_IDS;
        use serde_test::{Configure, Token};

        for e in EXAMPLE_IDS {
            let x = Scru64Id::const_from_u64(e.num);
            serde_test::assert_tokens(&x.readable(), &[Token::Str(e.text)]);
            serde_test::assert_tokens(&x.compact(), &[Token::U64(e.num)]);

            serde_test::assert_de_tokens(&x.readable(), &[Token::U64(e.num)]);
            serde_test::assert_de_tokens(&x.readable(), &[Token::I64(e.num as i64)]);

            serde_test::assert_de_tokens(&x.compact(), &[Token::Str(e.text)]);
            serde_test::assert_de_tokens(&x.compact(), &[Token::I64(e.num as i64)]);
        }
    }
}
