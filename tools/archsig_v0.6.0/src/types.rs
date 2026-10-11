//! 型の内部表現と wire 表現(入力仕様 §3、結果仕様 §2)。

use crate::canonical::Json;

/// Law の型。`Owned` は依存参照 `E[p]` で、宣言 metadata だけで保持する。
/// 式の型では `erase` で `Ref` へ落とす。
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
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
                let mut v = vec![Json::str("Tuple")];
                v.extend(items.iter().map(Type::wire));
                Json::Arr(v)
            }
            Type::List(t) => Json::Arr(vec![Json::str("List"), t.wire()]),
            Type::Set(t) => Json::Arr(vec![Json::str("Set"), t.wire()]),
            Type::Option(t) => Json::Arr(vec![Json::str("Option"), t.wire()]),
            Type::Map(a, b) => Json::Arr(vec![Json::str("Map"), a.wire(), b.wire()]),
            Type::Term(args, ret) => Json::Arr(vec![
                Json::str("Term"),
                Json::Arr(args.iter().map(Type::wire).collect()),
                ret.wire(),
            ]),
            Type::Path(a, b) => Json::Arr(vec![
                Json::str("Path"),
                Json::str(a.clone()),
                Json::str(b.clone()),
            ]),
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
