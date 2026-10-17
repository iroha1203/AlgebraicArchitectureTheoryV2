//! 公開された検査済み表を、元入力から得た表と構造ごとに照合する。
//! scalar と多倍長整数の library 等値は一原始演算、文字列は固定長 byte 単位で比較する。
use super::BundleError;
use crate::{
    issue::{Code, Details, Issue, Location},
    json::InputError,
    observed::control::{Checkpoint, Control},
};
use std::collections::BTreeMap;

pub(super) struct Comparison<'a> {
    control: &'a mut Control,
    location: Location,
    // 不一致を得た事後確認の取消でも、どの段階で不一致を得たかを保持する。
    pub(super) mismatched: bool,
}
impl<'a> Comparison<'a> {
    pub(super) fn new(control: &'a mut Control, location: Location) -> Self {
        Self {
            control,
            location,
            mismatched: false,
        }
    }
    pub(super) fn eq<T: ControlledEq + ?Sized>(&mut self, a: &T, b: &T) -> Result<(), BundleError> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            BundleError::checkpoint(self.control, Checkpoint::TableComparison)?;
            let result = a.compare(b, self);
            BundleError::finish(result, self.control, Checkpoint::TableComparison)
        })
    }
    fn mismatch(&mut self) -> Result<(), BundleError> {
        self.mismatched = true;
        Err(BundleError::Input(Box::new(Issue {
            code: Code::VocabularyMismatch,
            message: "検査済み三表が同じ元入力・定義 identity を参照していない".into(),
            location: self.location.clone(),
            details: Details::Empty,
        })))
    }
}
pub(super) trait ControlledEq {
    fn compare(&self, other: &Self, comparison: &mut Comparison<'_>) -> Result<(), BundleError>;
}
macro_rules! atomic {
    ($($ty:ty),* $(,)?) => {$ (
        impl ControlledEq for $ty {
            fn compare(&self, other: &Self, comparison: &mut Comparison<'_>) -> Result<(), BundleError> {
                if self == other { Ok(()) } else { comparison.mismatch() }
            }
        }
    )*};
}
atomic!(
    bool,
    u8,
    usize,
    u64,
    num_bigint::BigInt,
    num_bigint::BigUint,
    crate::law::ast::Builtin,
    crate::law::ast::BinOp,
    crate::law::ast::UnOp,
    crate::law::ast::QuantKind,
    crate::law::ast::Role,
    crate::law::model::ExpressionKind,
    crate::archmap::Mode
);
impl ControlledEq for str {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.len(), &other.len())?;
        for (a, b) in self
            .as_bytes()
            .chunks(1024)
            .zip(other.as_bytes().chunks(1024))
        {
            BundleError::checkpoint(c.control, Checkpoint::TableComparison)?;
            let result = if a == b { Ok(()) } else { c.mismatch() };
            BundleError::finish(result, c.control, Checkpoint::TableComparison)?;
        }
        Ok(())
    }
}
impl ControlledEq for String {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(self.as_str(), other.as_str())
    }
}
impl<T: ControlledEq + ?Sized> ControlledEq for &T {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(*self, *other)
    }
}
impl<T: ControlledEq> ControlledEq for Vec<T> {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.len(), &other.len())?;
        for (a, b) in self.iter().zip(other) {
            c.eq(a, b)?;
        }
        Ok(())
    }
}
impl<K: ControlledEq + Ord, V: ControlledEq> ControlledEq for BTreeMap<K, V> {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.len(), &other.len())?;
        for ((a, b), (x, y)) in self.iter().zip(other) {
            c.eq(a, x)?;
            c.eq(b, y)?;
        }
        Ok(())
    }
}
impl<T: ControlledEq> ControlledEq for Option<T> {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (None, None) => Ok(()),
            (Some(a), Some(b)) => c.eq(a, b),
            _ => c.mismatch(),
        }
    }
}
impl<T: ControlledEq> ControlledEq for Box<T> {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&**self, &**other)
    }
}
impl<A: ControlledEq, B: ControlledEq> ControlledEq for (A, B) {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.0, &other.0)?;
        c.eq(&self.1, &other.1)
    }
}
impl<A: ControlledEq, B: ControlledEq, C: ControlledEq> ControlledEq for (A, B, C) {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.0, &other.0)?;
        c.eq(&self.1, &other.1)?;
        c.eq(&self.2, &other.2)
    }
}
impl ControlledEq for crate::definition::Binding {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.namespace, &other.namespace)?;
        c.eq(&self.version, &other.version)?;
        c.eq(&self.digest, &other.digest)?;
        c.eq(&self.location, &other.location)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::Field {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.ty, &other.ty)?;
        c.eq(&self.meaning, &other.meaning)?;
        c.eq(&self.location, &other.location)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::Constructor {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.arguments, &other.arguments)?;
        c.eq(&self.meaning, &other.meaning)?;
        c.eq(&self.location, &other.location)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::Alignment {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.source, &other.source)?;
        c.eq(&self.target, &other.target)?;
        c.eq(&self.meaning, &other.meaning)?;
        c.eq(&self.location, &other.location)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::PrimitiveDeclaration {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.namespace, &other.namespace)?;
        c.eq(&self.meaning, &other.meaning)?;
        c.eq(&self.signature, &other.signature)?;
        c.eq(&self.location, &other.location)?;
        c.eq(&self.references, &other.references)?;
        c.eq(&self.dependencies, &other.dependencies)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::Vocabulary {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.namespace, &other.namespace)?;
        c.eq(&self.version, &other.version)?;
        c.eq(&self.dependencies, &other.dependencies)?;
        c.eq(&self.manifest, &other.manifest)?;
        c.eq(&self.digest, &other.digest)?;
        c.eq(&self.location, &other.location)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::DefinitionIdentity {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.input, &other.input)?;
        c.eq(&self.bytes_digest, &other.bytes_digest)?;
        c.eq(&self.model_digest, &other.model_digest)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::CheckedDefinitions {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.declarations, &other.declarations)?;
        c.eq(&self.vocabularies, &other.vocabularies)?;
        c.eq(&self.inputs, &other.inputs)?;
        Ok(())
    }
}
impl ControlledEq for crate::definition::PrimitiveSignature {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Entity {
                    parameters: a0,
                    fields: a1,
                    owner: a2,
                },
                Self::Entity {
                    parameters: b0,
                    fields: b1,
                    owner: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Arrow {
                    parameters: a0,
                    fields: a1,
                    owner: a2,
                    endpoint: a3,
                },
                Self::Arrow {
                    parameters: b0,
                    fields: b1,
                    owner: b2,
                    endpoint: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (
                Self::Correspondence {
                    parameters: a0,
                    fields: a1,
                    from: a2,
                    to: a3,
                    maps: a4,
                    alignments: a5,
                    implicit: a6,
                },
                Self::Correspondence {
                    parameters: b0,
                    fields: b1,
                    from: b2,
                    to: b3,
                    maps: b4,
                    alignments: b5,
                    implicit: b6,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                c.eq(a4, b4)?;
                c.eq(a5, b5)?;
                c.eq(a6, b6)?;
                Ok(())
            }
            (Self::Data { constructors: a0 }, Self::Data { constructors: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::model::Param {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.ty, &other.ty)?;
        c.eq(&self.span, &other.span)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::model::CtorSig {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.args, &other.args)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::model::Declaration {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.reading, &other.reading)?;
        c.eq(&self.signature, &other.signature)?;
        c.eq(&self.span, &other.span)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::model::ResolvedExpression {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.kind, &other.kind)?;
        c.eq(&self.span, &other.span)?;
        c.eq(&self.ty, &other.ty)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::model::DeclarationInfo {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.vocabularies, &other.vocabularies)?;
        c.eq(&self.name, &other.name)?;
        c.eq(&self.kind, &other.kind)?;
        c.eq(&self.parameters, &other.parameters)?;
        c.eq(&self.fields, &other.fields)?;
        c.eq(&self.returns, &other.returns)?;
        c.eq(&self.role, &other.role)?;
        c.eq(&self.span, &other.span)?;
        c.eq(&self.dependencies, &other.dependencies)?;
        c.eq(&self.references, &other.references)?;
        c.eq(&self.expressions, &other.expressions)?;
        c.eq(&self.supplied, &other.supplied)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::model::Signature {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Entity {
                    params: a0,
                    members: a1,
                    owner: a2,
                },
                Self::Entity {
                    params: b0,
                    members: b1,
                    owner: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Arrow {
                    params: a0,
                    members: a1,
                    owner: a2,
                    endpoint: a3,
                },
                Self::Arrow {
                    params: b0,
                    members: b1,
                    owner: b2,
                    endpoint: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (
                Self::Correspondence {
                    params: a0,
                    members: a1,
                    from: a2,
                    to: a3,
                    maps: a4,
                    alignments: a5,
                    implicit: a6,
                },
                Self::Correspondence {
                    params: b0,
                    members: b1,
                    from: b2,
                    to: b3,
                    maps: b4,
                    alignments: b5,
                    implicit: b6,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                c.eq(a4, b4)?;
                c.eq(a5, b5)?;
                c.eq(a6, b6)?;
                Ok(())
            }
            (Self::Data { constructors: a0 }, Self::Data { constructors: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::View {
                    params: a0,
                    returns: a1,
                    body: a2,
                },
                Self::View {
                    params: b0,
                    returns: b1,
                    body: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Law {
                    role: a0,
                    params: a1,
                    guard: a2,
                    body: a3,
                },
                Self::Law {
                    role: b0,
                    params: b1,
                    guard: b2,
                    body: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (
                Self::Local {
                    params: a0,
                    guard: a1,
                    reads: a2,
                },
                Self::Local {
                    params: b0,
                    guard: b1,
                    reads: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Change {
                    params: a0,
                    guard: a1,
                    body: a2,
                },
                Self::Change {
                    params: b0,
                    guard: b1,
                    body: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Relation {
                    params: a0,
                    guard: a1,
                    left: a2,
                    right: a3,
                },
                Self::Relation {
                    params: b0,
                    guard: b1,
                    left: b2,
                    right: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::model::SuppliedRule {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::GuardTrue { span: a0 }, Self::GuardTrue { span: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::SameNameAlignment {
                    span: a0,
                    pairs: a1,
                },
                Self::SameNameAlignment {
                    span: b0,
                    pairs: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::LocalDeclared { span: a0 }, Self::LocalDeclared { span: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::LocalSupport { span: a0 }, Self::LocalSupport { span: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::ast::Ident {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.span, &other.span)?;
        c.eq(&self.tok, &other.tok)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::ast::QName {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.parts, &other.parts)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::ast::Field {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.ty, &other.ty)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::ast::Arm {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.pattern, &other.pattern)?;
        c.eq(&self.body, &other.body)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::ast::Expr {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.kind, &other.kind)?;
        c.eq(&self.span, &other.span)?;
        Ok(())
    }
}
impl ControlledEq for crate::law::ast::TypeAst {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Builtin(a0, a1), Self::Builtin(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::Fp {
                    modulus: a0,
                    span: a1,
                },
                Self::Fp {
                    modulus: b0,
                    span: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::Named {
                    name: a0,
                    index: a1,
                    span: a2,
                },
                Self::Named {
                    name: b0,
                    index: b1,
                    span: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (Self::Tuple(a0, a1), Self::Tuple(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::List(a0, a1), Self::List(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Set(a0, a1), Self::Set(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Option(a0, a1), Self::Option(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Map(a0, a1, a2), Self::Map(b0, b1, b2)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (Self::Term(a0, a1, a2), Self::Term(b0, b1, b2)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (Self::Path(a0, a1, a2), Self::Path(b0, b1, b2)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::ast::Pattern {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Wild(a0), Self::Wild(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Name(a0), Self::Name(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::Ctor {
                    name: a0,
                    args: a1,
                    span: a2,
                },
                Self::Ctor {
                    name: b0,
                    args: b1,
                    span: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::ast::QuantSplit {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Fixed {
                    domain: a0,
                    body: a1,
                },
                Self::Fixed {
                    domain: b0,
                    body: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Candidates(a0), Self::Candidates(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::ast::QuantDomain {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::In(a0), Self::In(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Type(a0), Self::Type(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::ast::ExprKind {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Let {
                    name: a0,
                    value: a1,
                    body: a2,
                },
                Self::Let {
                    name: b0,
                    value: b1,
                    body: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::If {
                    cond: a0,
                    then_branch: a1,
                    else_branch: a2,
                },
                Self::If {
                    cond: b0,
                    then_branch: b1,
                    else_branch: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Match {
                    scrutinee: a0,
                    arms: a1,
                },
                Self::Match {
                    scrutinee: b0,
                    arms: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::Quant {
                    kind: a0,
                    var: a1,
                    split: a2,
                },
                Self::Quant {
                    kind: b0,
                    var: b1,
                    split: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Binary {
                    op: a0,
                    lhs: a1,
                    rhs: a2,
                },
                Self::Binary {
                    op: b0,
                    lhs: b1,
                    rhs: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (
                Self::Unary {
                    op: a0,
                    operand: a1,
                },
                Self::Unary {
                    op: b0,
                    operand: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Dotted(a0), Self::Dotted(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Field { base: a0, name: a1 }, Self::Field { base: b0, name: b1 }) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::Index {
                    base: a0,
                    index: a1,
                    index_span: a2,
                    dot_tok: a3,
                },
                Self::Index {
                    base: b0,
                    index: b1,
                    index_span: b2,
                    dot_tok: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (
                Self::Call {
                    callee: a0,
                    args: a1,
                },
                Self::Call {
                    callee: b0,
                    args: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::With {
                    base: a0,
                    updates: a1,
                },
                Self::With {
                    base: b0,
                    updates: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::ThenOp, Self::ThenOp) => Ok(()),
            (Self::Int(a0), Self::Int(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Str(a0), Self::Str(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Bool(a0), Self::Bool(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Unit, Self::Unit) => Ok(()),
            (Self::Group(a0), Self::Group(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Tuple(a0), Self::Tuple(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::ListLit { ty: a0, items: a1 }, Self::ListLit { ty: b0, items: b1 }) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::SetLit { ty: a0, items: a1 }, Self::SetLit { ty: b0, items: b1 }) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::SetComp {
                    elem: a0,
                    var: a1,
                    domain: a2,
                    filter: a3,
                },
                Self::SetComp {
                    elem: b0,
                    var: b1,
                    domain: b2,
                    filter: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (Self::None(a0), Self::None(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Some(a0), Self::Some(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::Fn {
                    params: a0,
                    body: a1,
                },
                Self::Fn {
                    params: b0,
                    body: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (
                Self::Family {
                    name: a0,
                    owner: a1,
                },
                Self::Family {
                    name: b0,
                    owner: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::archmap::Source {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.uri, &other.uri)?;
        c.eq(&self.revision, &other.revision)?;
        c.eq(&self.digest, &other.digest)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::SourceLocation {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.source, &other.source)?;
        c.eq(&self.path, &other.path)?;
        c.eq(&self.span, &other.span)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::Origin {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.mode, &other.mode)?;
        c.eq(&self.method, &other.method)?;
        c.eq(&self.locations, &other.locations)?;
        c.eq(&self.note, &other.note)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::Field {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.name, &other.name)?;
        c.eq(&self.ty, &other.ty)?;
        c.eq(&self.slot, &other.slot)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::Subject {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.snapshot, &other.snapshot)?;
        c.eq(&self.id, &other.id)?;
        c.eq(&self.ty, &other.ty)?;
        c.eq(&self.origin, &other.origin)?;
        c.eq(&self.fields, &other.fields)?;
        c.eq(&self.pointer, &other.pointer)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::Snapshot {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.id, &other.id)?;
        c.eq(&self.origin, &other.origin)?;
        c.eq(&self.subjects, &other.subjects)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::CheckedArchMap {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.bytes_digest, &other.bytes_digest)?;
        c.eq(&self.model_digest, &other.model_digest)?;
        c.eq(&self.vocabularies, &other.vocabularies)?;
        c.eq(&self.sources, &other.sources)?;
        c.eq(&self.origins, &other.origins)?;
        c.eq(&self.snapshots, &other.snapshots)?;
        Ok(())
    }
}
impl ControlledEq for crate::archmap::Slot {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Known {
                    atom: a0,
                    origin: a1,
                    value: a2,
                    pointer: a3,
                },
                Self::Known {
                    atom: b0,
                    origin: b1,
                    value: b2,
                    pointer: b3,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                c.eq(a3, b3)?;
                Ok(())
            }
            (Self::Missing, Self::Missing) => Ok(()),
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::types::Type {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Unit, Self::Unit) => Ok(()),
            (Self::Bool, Self::Bool) => Ok(()),
            (Self::Z, Self::Z) => Ok(()),
            (Self::Q, Self::Q) => Ok(()),
            (Self::Text, Self::Text) => Ok(()),
            (Self::Fp(a0), Self::Fp(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Ref(a0), Self::Ref(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Owned(a0, a1), Self::Owned(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Data(a0), Self::Data(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Tuple(a0), Self::Tuple(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::List(a0), Self::List(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Set(a0), Self::Set(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Option(a0), Self::Option(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Map(a0, a1), Self::Map(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Term(a0, a1), Self::Term(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Path(a0, a1), Self::Path(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::canonical::Json {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Bool(a0), Self::Bool(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Nat(a0), Self::Nat(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Str(a0), Self::Str(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Arr(a0), Self::Arr(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Obj(a0), Self::Obj(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::issue::Location {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (
                Self::Definition {
                    input: a0,
                    pointer: a1,
                    span: a2,
                },
                Self::Definition {
                    input: b0,
                    pointer: b1,
                    span: b2,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                c.eq(a2, b2)?;
                Ok(())
            }
            (Self::Law { span: a0 }, Self::Law { span: b0 }) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::ArchMap {
                    pointer: a0,
                    span: a1,
                },
                Self::ArchMap {
                    pointer: b0,
                    span: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::archmap::value::Value {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        match (self, other) {
            (Self::Unit, Self::Unit) => Ok(()),
            (Self::Bool(a0), Self::Bool(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Z(a0), Self::Z(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Q(a0, a1), Self::Q(b0, b1)) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Fp(a0), Self::Fp(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Text(a0), Self::Text(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::Ref {
                    snapshot: a0,
                    subject: a1,
                },
                Self::Ref {
                    snapshot: b0,
                    subject: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Tuple(a0), Self::Tuple(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::List(a0), Self::List(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Set(a0), Self::Set(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Option(a0), Self::Option(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (
                Self::Data {
                    constructor: a0,
                    args: a1,
                },
                Self::Data {
                    constructor: b0,
                    args: b1,
                },
            ) => {
                c.eq(a0, b0)?;
                c.eq(a1, b1)?;
                Ok(())
            }
            (Self::Map(a0), Self::Map(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            (Self::Term(a0), Self::Term(b0)) => {
                c.eq(a0, b0)?;
                Ok(())
            }
            _ => c.mismatch(),
        }
    }
}
impl ControlledEq for crate::law::CheckedLaw {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.bytes_digest, &other.bytes_digest)?;
        c.eq(&self.model_digest, &other.model_digest)?;
        c.eq(&self.declarations, &other.declarations)?;
        c.eq(&self.exprs, &other.exprs)?;
        c.eq(&self.expr_types, &other.expr_types)?;
        c.eq(&self.quantifier_types, &other.quantifier_types)?;
        c.eq(&self.infos, &other.infos)?;
        c.eq(&self.definitions, &other.definitions)?;
        Ok(())
    }
}
// TermValue の既存 PartialEq と同じく、検査済み補助 arena は等値に含めない。
impl ControlledEq for crate::archmap::value::TermValue {
    fn compare(&self, other: &Self, c: &mut Comparison<'_>) -> Result<(), BundleError> {
        c.eq(&self.params, &other.params)?;
        c.eq(&self.body, &other.body)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        archmap::value::{TermValue, Value},
        canonical::Json,
        law::{
            TermBody,
            ast::{Builtin, Ident, Pattern, TypeAst},
        },
        observed::control::{CheckFailure, Limits, StopReason, Usage},
        result::Signal,
        types::Type,
    };
    use std::{cell::Cell, rc::Rc};

    fn compare<T: ControlledEq>(a: &T, b: &T, control: &mut Control) -> Result<(), BundleError> {
        Comparison::new(control, Location::Law { span: (0, 1) }).eq(a, b)
    }

    fn exercise<T: ControlledEq + PartialEq>(a: &T, b: &T) {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut control = Control::new(Limits::default(), move |point| {
            assert_eq!(point, Checkpoint::TableComparison);
            seen.set(seen.get() + 1);
            Usage::default()
        });
        assert_eq!(compare(a, b, &mut control).is_ok(), a == b);
        assert!(count.get() > 8);
        for at in 1..=count.get() {
            let mut visits = 0;
            let mut control = Control::new(Limits::default(), move |_| {
                visits += 1;
                Usage {
                    signal: (visits == at).then_some(Signal::Term),
                    ..Usage::default()
                }
            });
            assert!(matches!(
                compare(a, b, &mut control),
                Err(CheckFailure::Stopped(StopReason::Cancelled(Signal::Term)))
            ));
        }
    }

    #[test]
    fn controlled_comparison_preserves_recursive_equality_and_internal_stops() {
        let a = Type::Term(
            vec![Type::Tuple(vec![
                Type::Bool,
                Type::Option(Box::new(Type::Q)),
            ])],
            Box::new(Type::Map(
                Box::new(Type::Ref("V.Item".into())),
                Box::new(Type::Text),
            )),
        );
        exercise(&a, &a);
        let a = Json::obj([(
            "items",
            Json::Arr(vec![
                Json::Bool(false),
                Json::obj([("name", Json::str("値"))]),
            ]),
        )]);
        exercise(&a, &a);
        let a = Value::Map(vec![(
            Value::Text("key".into()),
            Value::Data {
                constructor: "V.D.C".into(),
                args: vec![Value::Option(Some(Box::new(Value::Tuple(vec![
                    Value::Unit,
                    Value::Bool(true),
                ]))))],
            },
        )]);
        exercise(&a, &a);
        let a = TypeAst::Term(
            vec![TypeAst::Tuple(
                vec![TypeAst::Builtin(Builtin::Bool, (2, 3))],
                (1, 4),
            )],
            Box::new(TypeAst::List(
                Box::new(TypeAst::Builtin(Builtin::Q, (5, 6))),
                (4, 7),
            )),
            (0, 8),
        );
        exercise(&a, &a);
        let a = Pattern::Ctor {
            name: crate::law::ast::QName {
                parts: vec![Ident {
                    name: "C".into(),
                    span: (0, 1),
                    tok: 0,
                }],
            },
            args: vec![Pattern::Ctor {
                name: crate::law::ast::QName {
                    parts: vec![Ident {
                        name: "D".into(),
                        span: (2, 3),
                        tok: 2,
                    }],
                },
                args: vec![Pattern::Wild((4, 5))],
                span: (2, 6),
            }],
            span: (0, 7),
        };
        exercise(&a, &a);
    }

    #[test]
    fn known_comparison_mismatch_precedes_budget_and_cancellation_precedes_mismatch() {
        for resource in 0..3 {
            let mut visits = 0;
            let mut control = Control::new(
                Limits {
                    time_ms: Some(10),
                    memory_mib: Some(10),
                },
                move |_| {
                    visits += 1;
                    let stop = visits == 2; // scalar 不一致を得た直後。
                    Usage {
                        signal: (stop && resource == 0).then_some(Signal::Int),
                        elapsed_ms: if stop && resource == 1 { 11 } else { 0 },
                        memory_mib: if stop && resource == 2 { 12 } else { 0 },
                    }
                },
            );
            let mut comparison = Comparison::new(&mut control, Location::Law { span: (0, 1) });
            let result = comparison.eq(&false, &true);
            assert!(comparison.mismatched);
            if resource == 0 {
                assert!(matches!(
                    result,
                    Err(CheckFailure::Stopped(StopReason::Cancelled(Signal::Int)))
                ));
            } else {
                assert!(
                    matches!(result, Err(CheckFailure::Input(issue)) if issue.code == Code::VocabularyMismatch)
                );
                assert!(matches!(
                    control.stop_reason(),
                    Some(StopReason::BudgetExhausted { .. })
                ));
            }
        }
    }

    #[test]
    fn comparison_preserves_ast_locations_and_term_equality_contract() {
        let mut control = Control::unlimited();
        // 同じ子列でも variant の違いを消さない。
        let a = Type::List(Box::new(Type::Bool));
        let b = Type::Set(Box::new(Type::Bool));
        assert_ne!(a, b);
        assert!(matches!(
            compare(&a, &b, &mut control),
            Err(CheckFailure::Input(_))
        ));
        let a = Value::Tuple(vec![Value::Bool(true)]);
        let b = Value::List(vec![Value::Bool(true)]);
        assert_ne!(a, b);
        assert!(matches!(
            compare(&a, &b, &mut control),
            Err(CheckFailure::Input(_))
        ));
        let a = TypeAst::Builtin(Builtin::Bool, (0, 1));
        let b = TypeAst::Builtin(Builtin::Bool, (1, 2));
        assert_ne!(a, b);
        assert!(matches!(
            compare(&a, &b, &mut control),
            Err(CheckFailure::Input(_))
        ));
        let a = Pattern::Wild((0, 1));
        let b = Pattern::Wild((1, 2));
        assert_ne!(a, b);
        assert!(matches!(
            compare(&a, &b, &mut control),
            Err(CheckFailure::Input(_))
        ));
        let term = |types| TermValue {
            params: vec!["x".into()],
            body: "x".into(),
            checked: TermBody {
                exprs: vec![],
                root: 0,
                types,
                references: vec![],
                quantifier_types: vec![],
            },
        };
        let a = term(vec![Some(Type::Bool)]);
        let b = term(vec![Some(Type::Z)]);
        assert_eq!(a, b); // 補助 arena を比較しない既存の PartialEq と同じ意味。
        assert!(compare(&a, &b, &mut control).is_ok());
        let b = TermValue {
            body: "false".into(),
            ..b
        };
        assert_ne!(a, b);
        assert!(matches!(
            compare(&a, &b, &mut control),
            Err(CheckFailure::Input(_))
        ));
    }
}
