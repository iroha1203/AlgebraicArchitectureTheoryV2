//! 入力の不正を表す Issue(結果仕様 §6)。

use crate::canonical::Json;
use crate::types::Type;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Code {
    Syntax,
    DuplicateId,
    Type,
    Reference,
    Cycle,
    UnsupportedVersion,
}

impl Code {
    pub fn name(self) -> &'static str {
        match self {
            Code::Syntax => "syntax",
            Code::DuplicateId => "duplicate_id",
            Code::Type => "type",
            Code::Reference => "reference",
            Code::Cycle => "cycle",
            Code::UnsupportedVersion => "unsupported_version",
        }
    }
}

/// 入力位置。Law は元の byte 列の半開区間。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Location {
    Law { span: (usize, usize) },
}

impl Location {
    pub fn wire(&self) -> Json {
        match self {
            Location::Law { span } => {
                Json::obj([("input", Json::str("law")), ("span", span_wire(*span))])
            }
        }
    }
}

pub fn span_wire(span: (usize, usize)) -> Json {
    Json::Arr(vec![Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)])
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Details {
    Empty,
    Type {
        expected: Type,
        actual: Type,
    },
    Version {
        found_format: String,
        found_semantics: Option<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Issue {
    pub code: Code,
    pub message: String,
    pub location: Location,
    pub details: Details,
}

impl Issue {
    pub fn law(code: Code, span: (usize, usize), message: impl Into<String>) -> Issue {
        Issue {
            code,
            message: message.into(),
            location: Location::Law { span },
            details: Details::Empty,
        }
    }

    pub fn law_type(
        span: (usize, usize),
        expected: &Type,
        actual: &Type,
        message: impl Into<String>,
    ) -> Issue {
        Issue {
            code: Code::Type,
            message: message.into(),
            location: Location::Law { span },
            details: Details::Type {
                expected: expected.erase(),
                actual: actual.erase(),
            },
        }
    }

    pub fn wire(&self) -> Json {
        let details = match &self.details {
            Details::Empty => Json::Obj(Default::default()),
            Details::Type { expected, actual } => {
                Json::obj([("expected", expected.wire()), ("actual", actual.wire())])
            }
            Details::Version {
                found_format,
                found_semantics,
            } => {
                let mut m = std::collections::BTreeMap::new();
                m.insert("found_format".to_owned(), Json::str(found_format.clone()));
                if let Some(s) = found_semantics {
                    m.insert("found_semantics".to_owned(), Json::str(s.clone()));
                }
                Json::Obj(m)
            }
        };
        Json::obj([
            ("code", Json::str(self.code.name())),
            ("message", Json::str(self.message.clone())),
            ("location", self.location.wire()),
            ("dependencies", Json::Arr(vec![])),
            ("missing", Json::Arr(vec![])),
            ("details", details),
        ])
    }
}
