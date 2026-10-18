//! 恒等 Path の数学的な値と、結果型 T の既出 Ref 表示。
//! 表示 node の番号は値の同一性に含めず、値の挿入前に既出の型付き値を照合する。
use super::{
    control::{Checkpoint, Control},
    data,
    result::{Node, NodeRef, NodeType, Payload, Scalar, ValidationFailure},
};
use crate::{canonical::Json, types::Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Identity {
    pub reading: String,
    pub snapshot: String,
    pub subject: String,
    pub entity: String,
}
fn tick(control: &Control) -> Result<(), ValidationFailure> {
    control.clone().checkpoint(Checkpoint::FiniteIteration)?;
    Ok(())
}
#[cfg(test)]
type Observer = Box<dyn FnMut(&'static str, usize)>;
#[cfg(test)]
thread_local! {
    static OBSERVER: std::cell::RefCell<Option<Observer>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(super) fn observe(observer: impl FnMut(&'static str, usize) + 'static) {
    OBSERVER.with(|current| *current.borrow_mut() = Some(Box::new(observer)));
}
#[cfg(test)]
pub(super) fn clear_observer() {
    OBSERVER.with(|current| *current.borrow_mut() = None);
}
#[cfg(test)]
fn observed(stage: &'static str, index: usize) {
    OBSERVER.with(|current| {
        if let Some(observer) = current.borrow_mut().as_mut() {
            observer(stage, index);
        }
    });
}
impl Identity {
    /// 空語の作用は共通 carrier 全体の恒等。reading は由来として別に照合する。
    pub(super) fn same_action(&self, other: &Self) -> bool {
        self.snapshot == other.snapshot
            && self.subject == other.subject
            && self.entity == other.entity
    }
    pub(super) fn object(&self) -> Scalar {
        Scalar::Subject {
            snapshot: self.snapshot.clone(),
            subject: self.subject.clone(),
            entity: self.entity.clone(),
        }
    }
    pub(super) fn check(&self, control: &Control) -> Result<(), ValidationFailure> {
        tick(control)?;
        if [&self.reading, &self.snapshot, &self.subject, &self.entity]
            .into_iter()
            .any(|part| part.is_empty())
        {
            return Err("恒等 Path の reading・端点の名前が空".into());
        }
        tick(control)
    }
}

/// 型の中の Path を共有制御で検出する。原始 Term の型検査は再実行しない。
pub(super) fn contains_path(ty: &Type, control: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        match ty {
            Type::Path(..) => Ok(true),
            Type::Tuple(items) => {
                for item in items {
                    if contains_path(item, control)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::List(item) | Type::Set(item) | Type::Option(item) => contains_path(item, control),
            Type::Map(a, b) => Ok(contains_path(a, control)? || contains_path(b, control)?),
            Type::Term(args, ret) => {
                for arg in args {
                    if contains_path(arg, control)? {
                        return Ok(true);
                    }
                }
                contains_path(ret, control)
            }
            _ => Ok(false),
        }
    })
}

/// 結果型 T の構成を許す範囲。Term の原始型検査を表示のために再実行しない。
pub(super) fn result_type(ty: &Type, control: &Control) -> Result<bool, ValidationFailure> {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        tick(control)?;
        if data::primitive_type(ty, control)? {
            return Ok(true);
        }
        match ty {
            Type::Path(a, b) => Ok(!a.is_empty() && !b.is_empty()),
            Type::List(item) | Type::Option(item) => result_type(item, control),
            Type::Tuple(items) => {
                for item in items {
                    tick(control)?;
                    if !result_type(item, control)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    })
}

/// Ref は実 arguments の依存先にある同じ型・値の既出 node を指す。
/// 別の問いや無関係な既出値を、payload の一致だけで借用しない。
fn reference(
    value: &Scalar,
    prior: &[Node],
    roots: &[NodeRef],
    control: &Control,
) -> Result<NodeRef, ValidationFailure> {
    let mut pending = roots.to_vec();
    let mut visited = std::collections::BTreeSet::new();
    while let Some(reference) = pending.pop() {
        #[cfg(test)]
        observed("reference", reference.0);
        tick(control)?;
        let index = reference.0;
        if !visited.insert(index) {
            continue;
        }
        let node = prior.get(index).ok_or("値表示の依存 Ref が既出でない")?;
        if node.ty == NodeType::Value(value.ty())
            && let Some(Payload::Scalar(actual)) = &node.payload
            && actual == value
        {
            tick(control)?;
            return Ok(NodeRef(index));
        }
        for child in &node.arguments {
            tick(control)?;
            if child.0 >= index {
                return Err("値表示の依存 DAG に前方参照がある".into());
            }
            pending.push(*child);
            tick(control)?;
        }
        tick(control)?;
    }
    Err("非原始の値表示に対応する型付き既出 node がない".into())
}

pub(super) fn check_refs(
    value: &Scalar,
    prior: &[Node],
    roots: &[NodeRef],
    control: &Control,
) -> Result<(), ValidationFailure> {
    if contains_path(&value.ty(), control)? {
        wire(value, prior, roots, control)?;
    }
    Ok(())
}

pub(super) fn wire(
    value: &Scalar,
    prior: &[Node],
    roots: &[NodeRef],
    control: &Control,
) -> Result<Json, ValidationFailure> {
    tick(control)?;
    if !contains_path(&value.ty(), control)? {
        return Ok(value.wire());
    }
    let json = match value {
        Scalar::Path(identity) => {
            #[cfg(test)]
            observed("identity", prior.len());
            identity.check(control)?;
            let object = reference(&identity.object(), prior, roots, control)?;
            Json::obj([
                ("reading", Json::str(&identity.reading)),
                ("source", object.wire()),
                ("target", object.wire()),
                ("generators", Json::Arr(vec![])),
            ])
        }
        Scalar::Tuple(items) | Scalar::List { items, .. } => {
            let mut refs = Vec::new();
            for item in items {
                #[cfg(test)]
                observed("component", refs.len());
                tick(control)?;
                refs.push(reference(item, prior, roots, control)?.wire());
                tick(control)?;
            }
            Json::Arr(refs)
        }
        Scalar::Option { value: None, .. } => Json::obj([("none", Json::Bool(true))]),
        Scalar::Option {
            value: Some(value), ..
        } => Json::obj([("some", reference(value, prior, roots, control)?.wire())]),
        _ => return Err("非原始の結果型に未対応の値を表示しようとした".into()),
    };
    tick(control)?;
    Ok(json)
}

pub(super) fn construct(
    name: &str,
    reading: &str,
    values: &[Scalar],
    control: &Control,
) -> Result<Scalar, ValidationFailure> {
    tick(control)?;
    let [value] = values else {
        return Err("恒等 Path・端点演算の引数数が違う".into());
    };
    let result = match (name, value) {
        (
            "identity",
            Scalar::Subject {
                snapshot,
                subject,
                entity,
            },
        ) => Scalar::Path(Box::new(Identity {
            reading: reading.into(),
            snapshot: snapshot.clone(),
            subject: subject.clone(),
            entity: entity.clone(),
        })),
        ("source" | "target", Scalar::Path(identity)) => identity.object(),
        _ => return Err("恒等 Path・端点演算の元の値型が違う".into()),
    };
    tick(control)?;
    Ok(result)
}
