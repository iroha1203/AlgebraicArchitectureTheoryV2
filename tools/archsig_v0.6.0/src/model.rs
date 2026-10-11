use serde_json::{Value, json};

pub type Span = [usize; 2];
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Unit,
    Bool,
    Z,
    Q,
    Text,
    Fp(String),
    Ref(String),
    Data(String),
    Owned(String, String),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Set(Box<Type>),
    Option(Box<Type>),
    Map(Box<Type>, Box<Type>),
    Term(Vec<Type>, Box<Type>),
    Path(String, String),
}
impl Type {
    pub fn wire(&self) -> Value {
        match self {
            Self::Unit => json!("Unit"),
            Self::Bool => json!("Bool"),
            Self::Z => json!("Z"),
            Self::Q => json!("Q"),
            Self::Text => json!("Text"),
            Self::Fp(p) => json!(["Fp", p]),
            Self::Ref(n) => json!(["Ref", n]),
            Self::Data(n) => json!(["Data", n]),
            Self::Owned(n, p) => json!(["Owned", n, p]),
            Self::Tuple(xs) => Value::Array(
                std::iter::once(json!("Tuple"))
                    .chain(xs.iter().map(Self::wire))
                    .collect(),
            ),
            Self::List(t) => json!(["List", t.wire()]),
            Self::Set(t) => json!(["Set", t.wire()]),
            Self::Option(t) => json!(["Option", t.wire()]),
            Self::Map(a, b) => json!(["Map", a.wire(), b.wire()]),
            Self::Term(a, b) => json!([
                "Term",
                a.iter().map(Self::wire).collect::<Vec<_>>(),
                b.wire()
            ]),
            Self::Path(a, b) => json!(["Path", a, b]),
        }
    }
    pub fn ref_name(&self) -> Option<&str> {
        match self {
            Self::Ref(n) | Self::Owned(n, _) => Some(n),
            _ => None,
        }
    }
}
#[derive(Clone, Debug)]
pub struct Issue {
    pub code: String,
    pub message: String,
    pub input: String,
    pub span: Span,
    pub pointer: Option<String>,
    pub details: Value,
}
impl Issue {
    pub fn law(code: &str, message: impl Into<String>, span: Span) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
            input: "law".into(),
            span,
            pointer: None,
            details: json!({}),
        }
    }
    pub fn wire(&self) -> Value {
        let mut location = json!({"input":self.input});
        if let Some(p) = &self.pointer {
            location["pointer"] = json!(p);
        } else {
            location["span"] = json!(self.span);
        }
        json!({"code":self.code,"message":self.message,"location":location,"dependencies":[],"missing":[],"details":self.details})
    }
}
pub type Checked<T> = Result<T, Issue>;
pub fn location(span: Span) -> Value {
    json!({"input":"law","span":span})
}
