//! 観測評価の公開射影の静的型付け。動的な constructor・index・owner 条件は評価へ残す。

use crate::{canonical::Json, definition::PrimitiveSignature, law::CheckedLaw, types::Type};

/// Law の型と、計算結果だけに存在する record 型を区別する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionType {
    Law(Type),
    Evaluation(Type),
    Proposition,
    Architecture,
    /// 実値の constructor や異種生成元によって決まる候補型。
    Dynamic(Vec<ProjectionType>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProjectionStep {
    Field(String),
    Index(u64),
}

impl ProjectionStep {
    pub fn wire(&self) -> Json {
        match self {
            Self::Field(s) => Json::str(s),
            Self::Index(n) => Json::Nat(*n),
        }
    }
}

/// 静的に合法な射影。`conditional` は実値による適合検査を必要とする。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionPlan {
    pub ty: ProjectionType,
    pub conditional: bool,
}

/// 閉じた公開表と Law の構造射影だけを解決する。
pub fn resolve_projection(
    law: &CheckedLaw,
    initial: ProjectionType,
    path: &[ProjectionStep],
) -> Result<ProjectionPlan, String> {
    let mut plan = ProjectionPlan {
        ty: initial,
        conditional: false,
    };
    let mut at = 0;
    while at < path.len() {
        let (next, used) = project(law, &plan.ty, &path[at..])?;
        plan.ty = next.ty;
        plan.conditional |= next.conditional;
        at += used;
    }
    Ok(plan)
}

fn project(
    law: &CheckedLaw,
    ty: &ProjectionType,
    path: &[ProjectionStep],
) -> Result<(ProjectionPlan, usize), String> {
    use ProjectionStep::{Field, Index};
    use ProjectionType::{Architecture, Dynamic, Evaluation, Law};
    let exact = |ty| {
        Ok((
            ProjectionPlan {
                ty,
                conditional: false,
            },
            1,
        ))
    };
    let conditional = |ty| {
        Ok((
            ProjectionPlan {
                ty,
                conditional: true,
            },
            1,
        ))
    };
    match (ty, &path[0]) {
        (Evaluation(t), Field(f)) if f == "value" => conditional(Law(t.clone())),
        (Evaluation(_), Field(f)) if f == "environment" => conditional(Architecture),
        (Architecture, Field(f)) if f == "root" => {
            let candidates = law
                .definitions
                .declarations
                .values()
                .filter_map(|d| match &d.signature {
                    PrimitiveSignature::Entity { owner: None, .. } => {
                        Some(Law(Type::Ref(d.name.clone())))
                    }
                    _ => None,
                })
                .collect();
            conditional(Dynamic(candidates))
        }
        (Law(Type::Tuple(ts)), Index(i)) => {
            let t = usize::try_from(*i)
                .ok()
                .and_then(|i| ts.get(i))
                .ok_or("Tuple の index が範囲外")?;
            exact(Law(t.clone()))
        }
        (Law(Type::List(t)), Index(_)) => conditional(Law((**t).clone())),
        (Law(Type::Option(t)), Field(f)) if f == "some" => conditional(Law((**t).clone())),
        (Law(Type::Data(name)), Index(i)) => {
            let Some(d) = law.definitions.declarations.get(name) else {
                return Err("data 宣言がない".into());
            };
            let PrimitiveSignature::Data { constructors } = &d.signature else {
                return Err("data 型でない".into());
            };
            let mut ts = Vec::new();
            for c in constructors {
                if let Some(t) = usize::try_from(*i).ok().and_then(|i| c.arguments.get(i)) {
                    let t = Law(t.clone());
                    if !ts.contains(&t) {
                        ts.push(t);
                    }
                }
            }
            if ts.is_empty() {
                return Err("全 constructor で index が範囲外".into());
            }
            conditional(if ts.len() == 1 {
                ts.remove(0)
            } else {
                Dynamic(ts)
            })
        }
        (Law(Type::Path(a, _)), Field(f)) if f == "source" => exact(Law(Type::Ref(a.clone()))),
        (Law(Type::Path(_, b)), Field(f)) if f == "target" => exact(Law(Type::Ref(b.clone()))),
        (Law(Type::Path(_, _)), Field(f)) if f == "generators" => {
            if !matches!(path.get(1), Some(Index(_))) {
                return Err("generators は index まで指定する".into());
            }
            let ts = law
                .definitions
                .declarations
                .values()
                .filter_map(|d| match &d.signature {
                    PrimitiveSignature::Arrow { .. }
                    | PrimitiveSignature::Correspondence { .. } => {
                        Some(Law(Type::Ref(d.name.clone())))
                    }
                    _ => None,
                })
                .collect();
            Ok((
                ProjectionPlan {
                    ty: Dynamic(ts),
                    conditional: true,
                },
                2,
            ))
        }
        (Dynamic(ts), _) => {
            let mut out = Vec::new();
            let mut used = None;
            for t in ts {
                if let Ok((p, n)) = project(law, t, path) {
                    if used.is_some_and(|u| u != n) {
                        return Err("射影の構造が型候補間で異なる".into());
                    }
                    used = Some(n);
                    if !out.contains(&p.ty) {
                        out.push(p.ty);
                    }
                }
            }
            if out.is_empty() {
                return Err("公開された射影が型候補にない".into());
            }
            Ok((
                ProjectionPlan {
                    ty: if out.len() == 1 {
                        out.remove(0)
                    } else {
                        Dynamic(out)
                    },
                    conditional: true,
                },
                used.unwrap(),
            ))
        }
        _ => Err("この型で公開されていない射影".into()),
    }
}

/// 動的な候補が一つでも宣言型へ適合し得る場合だけ、束縛制約として残せる。
pub fn can_bind(actual: &ProjectionType, expected: &Type) -> bool {
    match actual {
        ProjectionType::Law(t) => t.erase() == expected.erase(),
        ProjectionType::Dynamic(ts) => ts.iter().any(|t| can_bind(t, expected)),
        _ => false,
    }
}
