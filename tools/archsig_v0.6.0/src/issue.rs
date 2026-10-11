//! 入力の不正を表す Issue(結果仕様 §6)。

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

/// 入力位置。Law は元の byte 列の半開区間。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Location {
    Law { span: (usize, usize) },
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
}
