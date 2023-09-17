//! Node configuration specifier used to build a [`Scru64Generator`] and related error types.

#[cfg(not(feature = "std"))]
use core as std;
use std::{fmt, str};

use crate::{id::ParseError as Scru64IdParseError, Scru64Id, NODE_CTR_SIZE};

#[cfg(doc)]
use super::Scru64Generator;

/// Represents a node configuration specifier used to build a [`Scru64Generator`].
///
/// A `NodeSpec` is usually expressed as a node spec string, which starts with a decimal `node_id`,
/// a hexadecimal `node_id` prefixed by "0x", or a 12-digit `node_prev` SCRU64 ID value, followed
/// by a slash and a decimal `node_id_size` value ranging from 1 to 23 (e.g., "42/8", "0xb00/12",
/// "0u2r85hm2pt3/16"). The first and second forms create a fresh new generator with the given
/// `node_id`, while the third form constructs one that generates subsequent SCRU64 IDs to the
/// `node_prev`. See also [the usage notes] in the SCRU64 spec for tips and techniques to design
/// node configurations.
///
/// [the usage notes]: https://github.com/scru64/spec#informative-usage-notes
///
/// # Examples
///
/// ```rust
/// use scru64::generator::NodeSpec;
///
/// let a = "42/8".parse::<NodeSpec>()?;
/// assert_eq!(a.node_id(), 42);
/// assert_eq!(a.node_id_size(), 8);
/// assert_eq!(a.node_prev(), None);
///
/// let b = "0xb00/12".parse::<NodeSpec>()?;
/// assert_eq!(b.node_id(), 0xb00);
/// assert_eq!(b.node_id_size(), 12);
/// assert_eq!(b.node_prev(), None);
///
/// let c = "0u2r85hm2pt3/16".parse::<NodeSpec>()?;
/// assert_eq!(c.node_id(), 11001);
/// assert_eq!(c.node_id_size(), 16);
/// assert_eq!(
///     c.node_prev(),
///     "0u2r85hm2pt3".parse::<scru64::Scru64Id>().ok()
/// );
/// # Ok::<(), scru64::generator::NodeSpecParseError>(())
/// ```
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct NodeSpec {
    node_prev: Scru64Id,
    node_id_size: u8,
}

impl NodeSpec {
    /// Returns the `node_id_size` value.
    pub const fn node_id_size(&self) -> u8 {
        self.node_id_size
    }

    /// Creates an instance with `node_prev` and `node_id_size` values.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the `node_id_size` is zero or greater than 23.
    pub const fn with_node_prev(
        node_prev: Scru64Id,
        node_id_size: u8,
    ) -> Result<Self, NodeSpecError> {
        if 0 < node_id_size && node_id_size < NODE_CTR_SIZE {
            Ok(Self {
                node_prev,
                node_id_size,
            })
        } else {
            Err(NodeSpecError::NodeIdSize { node_id_size })
        }
    }

    /// Returns the `node_prev` value if `self` is constructed with one or `None` otherwise.
    pub const fn node_prev(&self) -> Option<Scru64Id> {
        if self.node_prev.timestamp() > 0 {
            Some(self.node_prev)
        } else {
            None
        }
    }

    /// Returns the inner `node_prev` field value.
    pub(super) const fn node_prev_raw(&self) -> Scru64Id {
        self.node_prev
    }

    /// Creates an instance with `node_id` and `node_id_size` values.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the `node_id_size` is zero or greater than 23 or if the `node_id` does not
    /// fit in `node_id_size` bits.
    pub const fn with_node_id(node_id: u32, node_id_size: u8) -> Result<Self, NodeSpecError> {
        if 0 < node_id_size && node_id_size < NODE_CTR_SIZE {
            if node_id < (1 << node_id_size) {
                let counter_size = NODE_CTR_SIZE - node_id_size;
                match Scru64Id::from_parts(0, node_id << counter_size) {
                    Ok(node_prev) => Ok(Self {
                        node_prev,
                        node_id_size,
                    }),
                    Err(_) => unreachable!(),
                }
            } else {
                Err(NodeSpecError::NodeIdRange {
                    node_id,
                    node_id_size,
                })
            }
        } else {
            Err(NodeSpecError::NodeIdSize { node_id_size })
        }
    }

    /// Returns the `node_id` value given at instance creation or encoded in the `node_prev` value.
    pub const fn node_id(&self) -> u32 {
        let counter_size = NODE_CTR_SIZE - self.node_id_size;
        self.node_prev.node_ctr() >> counter_size
    }
}

impl str::FromStr for NodeSpec {
    type Err = NodeSpecParseError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        use NodeSpecParseErrorKind::*;
        let (lft, rgt) = {
            let mut iter = value.split('/');
            let lft = iter.next().unwrap();
            let rgt = iter.next().ok_or(Syntax)?;
            if iter.next().is_some() {
                return Err(Syntax.into());
            }
            (lft, rgt)
        };

        let node_id_size = {
            if rgt.len() > 3 || rgt.starts_with('+') {
                return Err(Right.into());
            }
            rgt.parse().map_err(|_| Right)?
        };

        if lft.len() == 12 {
            let node_prev = lft.parse().map_err(|source| LeftPrev { source })?;
            Self::with_node_prev(node_prev, node_id_size)
                .map_err(|source| NodeSpec { source }.into())
        } else {
            if lft.len() > 8 || lft.starts_with('+') {
                return Err(LeftNodeId.into());
            }
            let node_id = if lft.starts_with("0X") || lft.starts_with("0x") {
                u32::from_str_radix(&lft[2..], 16).map_err(|_| LeftNodeId)?
            } else {
                #[allow(clippy::from_str_radix_10)]
                u32::from_str_radix(lft, 10).map_err(|_| LeftNodeId)?
            };
            Self::with_node_id(node_id, node_id_size).map_err(|source| NodeSpec { source }.into())
        }
    }
}

impl fmt::Display for NodeSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node_prev() {
            Some(node_prev) => write!(f, "{}/{}", node_prev, self.node_id_size()),
            None => write!(f, "{}/{}", self.node_id(), self.node_id_size()),
        }
    }
}

/// An error representing an invalid pair of `node_id` and `node_id_size` to construct a
/// [`NodeSpec`] instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NodeSpecError {
    /// Indicates that `node_id_size` is out of range.
    NodeIdSize { node_id_size: u8 },

    /// Indicates that `node_id` is out of `node_id_size`-bit range.
    NodeIdRange { node_id: u32, node_id_size: u8 },
}

impl fmt::Display for NodeSpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NodeIdSize { node_id_size } => write!(
                f,
                "`node_id_size` ({}) must range from 1 to 23",
                node_id_size
            ),
            Self::NodeIdRange {
                node_id,
                node_id_size,
            } => write!(
                f,
                "`node_id` ({}) must fit in `node_id_size` ({}) bits",
                node_id, node_id_size
            ),
        }
    }
}

/// An error parsing an invalid node spec string representation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeSpecParseError {
    kind: NodeSpecParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum NodeSpecParseErrorKind {
    Syntax,
    Right,
    LeftPrev { source: Scru64IdParseError },
    LeftNodeId,
    NodeSpec { source: NodeSpecError },
}

impl From<NodeSpecParseErrorKind> for NodeSpecParseError {
    fn from(kind: NodeSpecParseErrorKind) -> Self {
        Self { kind }
    }
}

impl fmt::Display for NodeSpecParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use NodeSpecParseErrorKind::*;
        write!(f, "could not parse string as node spec: ")?;
        match &self.kind {
            Syntax => write!(
                f,
                r#"syntax error (expected: e.g., "42/8", "0xb00/12", "0u2r85hm2pt3/16")"#
            ),
            Right => write!(f, "could not parse string as `node_id_size`"),
            LeftPrev { source } => write!(f, "{}", source),
            LeftNodeId => write!(f, "could not parse string as `node_id`"),
            NodeSpec { source } => write!(f, "{}", source),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    impl std::error::Error for super::NodeSpecError {}
    impl std::error::Error for super::NodeSpecParseError {}
}

#[cfg(test)]
mod tests {
    use super::{NodeSpec, Scru64Id};
    use crate::test_cases::EXAMPLE_NODE_SPECS;

    /// Initializes with node ID and size pair and node spec string.
    #[test]
    fn constructor() {
        for e in EXAMPLE_NODE_SPECS {
            let node_prev = Scru64Id::const_from_u64(e.node_prev);

            let with_node_prev = NodeSpec::with_node_prev(node_prev, e.node_id_size).unwrap();
            assert_eq!(with_node_prev.node_id(), e.node_id);
            assert_eq!(with_node_prev.node_id_size(), e.node_id_size);
            if let Some(p) = with_node_prev.node_prev() {
                assert_eq!(p, node_prev);
            }
            assert_eq!(with_node_prev.node_prev_raw(), node_prev);

            let with_node_id = NodeSpec::with_node_id(e.node_id, e.node_id_size).unwrap();
            assert_eq!(with_node_id.node_id(), e.node_id);
            assert_eq!(with_node_id.node_id_size(), e.node_id_size);
            assert!(with_node_id.node_prev().is_none());
            if e.spec_type.ends_with("_node_id") {
                assert_eq!(with_node_id.node_prev_raw(), node_prev);
            }

            let parsed = e.node_spec.parse::<NodeSpec>().unwrap();
            assert_eq!(parsed.node_id(), e.node_id);
            assert_eq!(parsed.node_id_size(), e.node_id_size);
            if let Some(p) = parsed.node_prev() {
                assert_eq!(p, node_prev);
            }
            assert_eq!(parsed.node_prev_raw(), node_prev);

            #[cfg(feature = "std")]
            {
                assert_eq!(with_node_prev.to_string(), e.canonical);
                if e.spec_type.ends_with("_node_id") {
                    assert_eq!(with_node_id.to_string(), e.canonical);
                }
                assert_eq!(parsed.to_string(), e.canonical);
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
            "1/2/3",
            "0/0",
            "0/24",
            "8/1",
            "1024/8",
            "0000000000001/8",
            "1/0016",
            "42/800",
        ];

        for e in cases {
            assert!(e.parse::<NodeSpec>().is_err());
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde_support {
    use super::{fmt, str, NodeSpec};
    use serde::{de, Deserializer, Serializer};

    impl serde::Serialize for NodeSpec {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            use fmt::Write as _;
            let mut buffer = fstr::FStr::<16>::repeat(b'\0');
            write!(buffer.writer(), "{}", self).unwrap();
            serializer.serialize_str(buffer.slice_to_terminator('\0'))
        }
    }

    impl<'de> serde::Deserialize<'de> for NodeSpec {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_str(VisitorImpl)
        }
    }

    struct VisitorImpl;

    impl<'de> de::Visitor<'de> for VisitorImpl {
        type Value = NodeSpec;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a SCRU64 node spec string")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            value.parse().map_err(de::Error::custom)
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
        use serde_test::Token;

        for e in crate::test_cases::EXAMPLE_NODE_SPECS {
            let x = e.node_spec.parse::<NodeSpec>().unwrap();
            serde_test::assert_tokens(&x, &[Token::Str(e.canonical)]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.canonical.as_bytes())]);
        }
    }
}
