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

#[cfg(test)]
mod tests {
    use super::{test_cases::TEST_CASES, Scru64Id};

    /// Tests equality comparison.
    #[test]
    fn eq() {
        #[cfg(feature = "std")]
        let hash = {
            use core::hash::{BuildHasher, Hash, Hasher};
            let s = std::collections::hash_map::RandomState::new();
            move |value: Scru64Id| {
                let mut hasher = s.build_hasher();
                value.hash(&mut hasher);
                hasher.finish()
            }
        };

        let mut prev = Scru64Id::const_from_u64(TEST_CASES.last().unwrap().num);
        for e in TEST_CASES {
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
                assert_eq!(hash(curr), hash(twin));
                assert_ne!(hash(curr), hash(prev));
            }

            prev = curr;
        }
    }

    /// Tests ordering comparison.
    #[test]
    fn ord() {
        let mut cases = TEST_CASES.to_vec();
        cases.sort_by_key(|e| e.num);

        let mut prev = Scru64Id::const_from_u64(cases[0].num);
        for e in cases.iter().skip(1) {
            let curr = Scru64Id::const_from_u64(e.num);

            assert!(prev < curr);
            assert!(prev <= curr);

            assert!(curr > prev);
            assert!(curr >= prev);

            prev = curr;
        }
    }

    /// Tests conversion-to methods.
    #[test]
    fn convert_to() {
        for e in TEST_CASES {
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
            }
        }
    }

    /// Tests conversion-from methods.
    #[test]
    fn convert_from() {
        for e in TEST_CASES {
            let x = Scru64Id::const_from_u64(e.num);

            assert_eq!(x, (e.num as u64).try_into().unwrap());
            assert_eq!(x, (e.num as i64).try_into().unwrap());
            assert_eq!(x, e.text.parse().unwrap());
            assert_eq!(x, Scru64Id::from_parts(e.timestamp, e.node_ctr));

            #[cfg(feature = "std")]
            {
                assert_eq!(x, e.text.to_owned().try_into().unwrap());
                assert_eq!(x, e.text.to_ascii_uppercase().parse().unwrap());
                assert_eq!(x, e.text.to_ascii_uppercase().try_into().unwrap());
            }
        }
    }

    /// Tests if conversion from too large or small integer fails.
    #[test]
    fn from_int_error() {
        assert!(Scru64Id::try_from(36u64.pow(12)).is_err());
        assert!(Scru64Id::try_from(u64::MAX).is_err());

        assert!(Scru64Id::try_from(-1i64).is_err());
        assert!(Scru64Id::try_from(i64::MAX).is_err());
        assert!(Scru64Id::try_from(i64::MIN).is_err());
    }

    /// Tests if conversion from invalid string representation fails.
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

    /// Tests serialization and deserialization.
    #[cfg(test)]
    #[test]
    fn test() {
        use serde_test::{Configure, Token};

        for e in super::test_cases::TEST_CASES {
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

#[cfg(test)]
mod test_cases {
    #[derive(Clone, Eq, PartialEq, Debug)]
    pub struct PreparedCase {
        pub text: &'static str,
        pub num: u64,
        pub timestamp: u64,
        pub node_ctr: u32,
    }

    pub const TEST_CASES: &[PreparedCase] = &[
        PreparedCase {
            text: "000000000000",
            num: 0x0000000000000000,
            timestamp: 0,
            node_ctr: 0,
        },
        PreparedCase {
            text: "00000009zldr",
            num: 0x0000000000ffffff,
            timestamp: 0,
            node_ctr: 16777215,
        },
        PreparedCase {
            text: "zzzzzzzq0em8",
            num: 0x41c21cb8e0000000,
            timestamp: 282429536480,
            node_ctr: 0,
        },
        PreparedCase {
            text: "zzzzzzzzzzzz",
            num: 0x41c21cb8e0ffffff,
            timestamp: 282429536480,
            node_ctr: 16777215,
        },
        PreparedCase {
            text: "0u375nxqh5cq",
            num: 0x0186d52bbe2a635a,
            timestamp: 6557084606,
            node_ctr: 2777946,
        },
        PreparedCase {
            text: "0u375nxqh5cr",
            num: 0x0186d52bbe2a635b,
            timestamp: 6557084606,
            node_ctr: 2777947,
        },
        PreparedCase {
            text: "0u375nxqh5cs",
            num: 0x0186d52bbe2a635c,
            timestamp: 6557084606,
            node_ctr: 2777948,
        },
        PreparedCase {
            text: "0u375nxqh5ct",
            num: 0x0186d52bbe2a635d,
            timestamp: 6557084606,
            node_ctr: 2777949,
        },
        PreparedCase {
            text: "0u375ny0glr0",
            num: 0x0186d52bbf2a4a1c,
            timestamp: 6557084607,
            node_ctr: 2771484,
        },
        PreparedCase {
            text: "0u375ny0glr1",
            num: 0x0186d52bbf2a4a1d,
            timestamp: 6557084607,
            node_ctr: 2771485,
        },
        PreparedCase {
            text: "0u375ny0glr2",
            num: 0x0186d52bbf2a4a1e,
            timestamp: 6557084607,
            node_ctr: 2771486,
        },
        PreparedCase {
            text: "0u375ny0glr3",
            num: 0x0186d52bbf2a4a1f,
            timestamp: 6557084607,
            node_ctr: 2771487,
        },
        PreparedCase {
            text: "jdsf1we3ui4f",
            num: 0x2367c8dfb2e6d23f,
            timestamp: 152065073074,
            node_ctr: 15127103,
        },
        PreparedCase {
            text: "j0afcjyfyi98",
            num: 0x22b86eaad6b2f7ec,
            timestamp: 149123148502,
            node_ctr: 11728876,
        },
        PreparedCase {
            text: "ckzyfc271xsn",
            num: 0x16fc214296b29057,
            timestamp: 98719318678,
            node_ctr: 11702359,
        },
        PreparedCase {
            text: "t0vgc4c4b18n",
            num: 0x3504295badc14f07,
            timestamp: 227703085997,
            node_ctr: 12668679,
        },
        PreparedCase {
            text: "mwcrtcubk7bp",
            num: 0x29d3c7553e748515,
            timestamp: 179646715198,
            node_ctr: 7636245,
        },
        PreparedCase {
            text: "g9ye86pgplu7",
            num: 0x1dbb24363718aecf,
            timestamp: 127693764151,
            node_ctr: 1617615,
        },
        PreparedCase {
            text: "qmez19t9oeir",
            num: 0x30a122fef7cd6c83,
            timestamp: 208861855479,
            node_ctr: 13462659,
        },
        PreparedCase {
            text: "d81r595fq52m",
            num: 0x18278838f0660f2e,
            timestamp: 103742454000,
            node_ctr: 6688558,
        },
        PreparedCase {
            text: "v0rbps7ay8ks",
            num: 0x38a9e683bb4425ec,
            timestamp: 243368625083,
            node_ctr: 4466156,
        },
        PreparedCase {
            text: "z0jndjt42op2",
            num: 0x3ff596748ea77186,
            timestamp: 274703217806,
            node_ctr: 10973574,
        },
        PreparedCase {
            text: "f2bembkd4zrb",
            num: 0x1b844eb5d1aebb07,
            timestamp: 118183867857,
            node_ctr: 11451143,
        },
        PreparedCase {
            text: "mkg0fd5p76pp",
            num: 0x29391373ab449abd,
            timestamp: 177051235243,
            node_ctr: 4496061,
        },
    ];
}
