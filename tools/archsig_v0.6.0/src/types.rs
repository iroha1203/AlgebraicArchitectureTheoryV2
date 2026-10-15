//! 型の内部表現と wire 表現(入力仕様 §3、結果仕様 §2)。

use crate::canonical::Json;
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};

/// Law の型。`Owned` は依存参照 `E[p]` で、宣言 metadata だけで保持する。
/// 式の型では `erase` で `Ref` へ落とす。
#[derive(Debug, Eq)]
pub enum Type {
    Unit,
    Bool,
    Z,
    Q,
    Text,
    Fp(String),
    Ref(String),
    Owned(String, String),
    Data(String),
    Tuple(Vec<Type>),
    List(Box<Type>),
    Set(Box<Type>),
    Option(Box<Type>),
    Map(Box<Type>, Box<Type>),
    Term(Vec<Type>, Box<Type>),
    Path(String, String),
}

impl Type {
    pub fn wire(&self) -> Json {
        self.wire_controlled::<Box<crate::issue::Issue>>(
            &mut Control::unlimited(),
            Checkpoint::Expression,
        )
        .expect("通常の型表示は中断しない")
    }

    /// 入力の正規化で使う型木にも共有された停止制御を渡す。
    pub(crate) fn wire_controlled<E: InputError>(
        &self,
        control: &mut Control,
        point: Checkpoint,
    ) -> Result<Json, E> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            E::checkpoint(control, point)?;
            let value = match self {
                Type::Unit => Json::str("Unit"),
                Type::Bool => Json::str("Bool"),
                Type::Z => Json::str("Z"),
                Type::Q => Json::str("Q"),
                Type::Text => Json::str("Text"),
                Type::Fp(p) => Json::Arr(vec![Json::str("Fp"), Json::str(p.clone())]),
                Type::Ref(n) => Json::Arr(vec![Json::str("Ref"), Json::str(n.clone())]),
                Type::Owned(n, p) => Json::Arr(vec![
                    Json::str("Owned"),
                    Json::str(n.clone()),
                    Json::str(p.clone()),
                ]),
                Type::Data(n) => Json::Arr(vec![Json::str("Data"), Json::str(n.clone())]),
                Type::Tuple(items) => {
                    let mut values = vec![Json::str("Tuple")];
                    for ty in items {
                        E::checkpoint(control, point)?;
                        values.push(ty.wire_controlled::<E>(control, point)?);
                        E::checkpoint(control, point)?;
                    }
                    Json::Arr(values)
                }
                Type::List(t) | Type::Set(t) | Type::Option(t) => {
                    let tag = match self {
                        Type::List(_) => "List",
                        Type::Set(_) => "Set",
                        _ => "Option",
                    };
                    Json::Arr(vec![
                        Json::str(tag),
                        t.wire_controlled::<E>(control, point)?,
                    ])
                }
                Type::Map(a, b) => Json::Arr(vec![
                    Json::str("Map"),
                    a.wire_controlled::<E>(control, point)?,
                    b.wire_controlled::<E>(control, point)?,
                ]),
                Type::Term(args, ret) => {
                    let mut arguments = Vec::new();
                    for ty in args {
                        E::checkpoint(control, point)?;
                        arguments.push(ty.wire_controlled::<E>(control, point)?);
                        E::checkpoint(control, point)?;
                    }
                    Json::Arr(vec![
                        Json::str("Term"),
                        Json::Arr(arguments),
                        ret.wire_controlled::<E>(control, point)?,
                    ])
                }
                Type::Path(a, b) => Json::Arr(vec![
                    Json::str("Path"),
                    Json::str(a.clone()),
                    Json::str(b.clone()),
                ]),
            };
            E::checkpoint(control, point)?;
            Ok(value)
        })
    }

    /// 依存参照を、所属条件を除いた参照型へ落とす。式の型の比較と表示に使う。
    pub fn erase(&self) -> Type {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Type::Owned(n, _) => Type::Ref(n.clone()),
            Type::Tuple(items) => Type::Tuple(items.iter().map(Type::erase).collect()),
            Type::List(t) => Type::List(Box::new(t.erase())),
            Type::Set(t) => Type::Set(Box::new(t.erase())),
            Type::Option(t) => Type::Option(Box::new(t.erase())),
            Type::Map(a, b) => Type::Map(Box::new(a.erase()), Box::new(b.erase())),
            Type::Term(args, ret) => Type::Term(
                args.iter().map(Type::erase).collect(),
                Box::new(ret.erase()),
            ),
            t => t.clone(),
        })
    }

    pub fn ref_target(&self) -> Option<&str> {
        match self {
            Type::Ref(n) | Type::Owned(n, _) => Some(n),
            _ => None,
        }
    }

    pub fn is_numeric(&self) -> bool {
        match self {
            Type::Z | Type::Q | Type::Fp(_) => true,
            Type::Tuple(items) => items.iter().all(Type::is_numeric),
            _ => false,
        }
    }

    /// 直下と container の中の成分を、data の定義を除いて走査する。
    pub fn any(&self, f: &mut impl FnMut(&Type) -> bool) -> bool {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            if f(self) {
                return true;
            }
            match self {
                Type::Tuple(items) => items.iter().any(|t| t.any(f)),
                Type::List(t) | Type::Set(t) | Type::Option(t) => t.any(f),
                Type::Map(a, b) => a.any(f) || b.any(f),
                Type::Term(args, ret) => args.iter().any(|t| t.any(f)) || ret.any(f),
                _ => false,
            }
        })
    }

    /// `any` と同じ順序・短絡で、各型成分の前後に共有制御を確認する。
    pub(crate) fn any_controlled<E: InputError>(
        &self,
        f: &mut impl FnMut(&Type) -> bool,
        control: &mut Control,
        point: Checkpoint,
    ) -> Result<bool, E> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            E::checkpoint(control, point)?;
            let found = if f(self) {
                true
            } else {
                match self {
                    Type::Tuple(items) => {
                        let mut found = false;
                        for ty in items {
                            E::checkpoint(control, point)?;
                            found = ty.any_controlled::<E>(f, control, point)?;
                            E::checkpoint(control, point)?;
                            if found {
                                break;
                            }
                        }
                        found
                    }
                    Type::List(t) | Type::Set(t) | Type::Option(t) => {
                        t.any_controlled::<E>(f, control, point)?
                    }
                    Type::Map(a, b) => {
                        a.any_controlled::<E>(f, control, point)?
                            || b.any_controlled::<E>(f, control, point)?
                    }
                    Type::Term(args, ret) => {
                        let mut found = false;
                        for ty in args {
                            E::checkpoint(control, point)?;
                            found = ty.any_controlled::<E>(f, control, point)?;
                            E::checkpoint(control, point)?;
                            if found {
                                break;
                            }
                        }
                        found || ret.any_controlled::<E>(f, control, point)?
                    }
                    _ => false,
                }
            };
            E::checkpoint(control, point)?;
            Ok(found)
        })
    }
}

/// 深い入れ子の型を、呼出し側のスタックの深さによらず解放する。
impl Drop for Type {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_children(self, &mut stack);
        while let Some(mut t) = stack.pop() {
            take_children(&mut t, &mut stack);
        }
    }
}

fn take_children(t: &mut Type, stack: &mut Vec<Type>) {
    match t {
        Type::Tuple(items) => stack.append(items),
        Type::List(b) | Type::Set(b) | Type::Option(b) => {
            stack.push(std::mem::replace(&mut **b, Type::Unit))
        }
        Type::Map(a, b) => {
            stack.push(std::mem::replace(&mut **a, Type::Unit));
            stack.push(std::mem::replace(&mut **b, Type::Unit));
        }
        Type::Term(args, r) => {
            stack.append(args);
            stack.push(std::mem::replace(&mut **r, Type::Unit));
        }
        _ => {}
    }
}

/// 深い入れ子の型でも呼出し側のスタックを使い切らないよう、複製と比較は stacker を通す。
impl Clone for Type {
    fn clone(&self) -> Type {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Type::Unit => Type::Unit,
            Type::Bool => Type::Bool,
            Type::Z => Type::Z,
            Type::Q => Type::Q,
            Type::Text => Type::Text,
            Type::Fp(p) => Type::Fp(p.clone()),
            Type::Ref(n) => Type::Ref(n.clone()),
            Type::Owned(n, p) => Type::Owned(n.clone(), p.clone()),
            Type::Data(n) => Type::Data(n.clone()),
            Type::Tuple(items) => Type::Tuple(items.clone()),
            Type::List(t) => Type::List(Box::new((**t).clone())),
            Type::Set(t) => Type::Set(Box::new((**t).clone())),
            Type::Option(t) => Type::Option(Box::new((**t).clone())),
            Type::Map(a, b) => Type::Map(Box::new((**a).clone()), Box::new((**b).clone())),
            Type::Term(args, r) => Type::Term(args.clone(), Box::new((**r).clone())),
            Type::Path(a, b) => Type::Path(a.clone(), b.clone()),
        })
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match (self, other) {
            (Type::Unit, Type::Unit)
            | (Type::Bool, Type::Bool)
            | (Type::Z, Type::Z)
            | (Type::Q, Type::Q)
            | (Type::Text, Type::Text) => true,
            (Type::Fp(a), Type::Fp(b))
            | (Type::Ref(a), Type::Ref(b))
            | (Type::Data(a), Type::Data(b)) => a == b,
            (Type::Owned(a, p), Type::Owned(b, q)) | (Type::Path(a, p), Type::Path(b, q)) => {
                a == b && p == q
            }
            (Type::Tuple(a), Type::Tuple(b)) => a == b,
            (Type::List(a), Type::List(b))
            | (Type::Set(a), Type::Set(b))
            | (Type::Option(a), Type::Option(b)) => **a == **b,
            (Type::Map(a, b), Type::Map(c, d)) => **a == **c && **b == **d,
            (Type::Term(a, r), Type::Term(b, q)) => a == b && **r == **q,
            _ => false,
        })
    }
}

#[cfg(test)]
mod controlled_tests {
    use super::*;
    use crate::issue::Issue;
    use crate::observed::control::{CheckFailure, Limits, StopReason, Usage};
    use crate::result::Signal;
    use std::{cell::Cell, rc::Rc};

    type Failure = CheckFailure<Box<Issue>>;

    fn example() -> Type {
        Type::Term(
            vec![
                Type::Tuple(vec![Type::Z, Type::Option(Box::new(Type::Bool))]),
                Type::List(Box::new(Type::Ref("V.Root".into()))),
            ],
            Box::new(Type::Map(
                Box::new(Type::Ref("V.Root".into())),
                Box::new(Type::Q),
            )),
        )
    }

    #[test]
    fn controlled_type_wire_preserves_nested_component_encoding_and_stops() {
        let ty = example();
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut control = Control::new(Limits::default(), move |_| {
            seen.set(seen.get() + 1);
            Usage::default()
        });
        let wire = ty
            .wire_controlled::<Failure>(&mut control, Checkpoint::Expression)
            .unwrap();
        assert_eq!(
            wire.canonical(),
            r#"["Term",[["Tuple","Z",["Option","Bool"]],["List",["Ref","V.Root"]]],["Map",["Ref","V.Root"],"Q"]]"#
        );
        assert_eq!(ty.wire(), wire);
        let total = count.get();
        assert!(total > 20);
        for at in 1..=total {
            let mut visits = 0;
            let mut control = Control::new(Limits::default(), move |_| {
                visits += 1;
                Usage {
                    signal: (visits == at).then_some(Signal::Int),
                    ..Usage::default()
                }
            });
            assert!(matches!(
                ty.wire_controlled::<Failure>(&mut control, Checkpoint::Expression),
                Err(Failure::Stopped(StopReason::Cancelled(Signal::Int)))
            ));
        }
    }

    #[test]
    fn controlled_any_preserves_preorder_and_short_circuit_with_internal_stops() {
        let ty = example();
        for target in ["Bool", "Q", "absent"] {
            let mut ordinary = Vec::new();
            let found = ty.any(&mut |t| {
                let name = match t {
                    Type::Bool => "Bool",
                    Type::Q => "Q",
                    _ => "other",
                };
                ordinary.push(name);
                name == target
            });
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let mut control = Control::new(Limits::default(), move |_| {
                seen.set(seen.get() + 1);
                Usage::default()
            });
            let mut controlled = Vec::new();
            let actual = ty
                .any_controlled::<Failure>(
                    &mut |t| {
                        let name = match t {
                            Type::Bool => "Bool",
                            Type::Q => "Q",
                            _ => "other",
                        };
                        controlled.push(name);
                        name == target
                    },
                    &mut control,
                    Checkpoint::Expression,
                )
                .unwrap();
            assert_eq!(actual, found);
            assert_eq!(ordinary, controlled);
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
                    ty.any_controlled::<Failure>(
                        &mut |_| false,
                        &mut control,
                        Checkpoint::Expression
                    ),
                    Err(Failure::Stopped(StopReason::Cancelled(Signal::Term)))
                ));
            }
        }
    }
}
