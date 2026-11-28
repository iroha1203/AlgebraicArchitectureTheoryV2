//! AAT 第18章 強 Kleene 三値評価（正格 `let` 含む）および完全世界上の古典評価ヘルパ。

use crate::ir::partial::{
    BackgroundConstraint, FinitePartialPresentation, PartialArithOp, PartialEvalLawSpec,
    PartialFormula, PartialRecordKind, PartialRecordSpec, PartialTerm, PartialTruth, PartialValue,
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CompleteFiniteWorld {
    pub slots: BTreeMap<String, String>,
    pub op_tables: BTreeMap<String, BTreeMap<Vec<String>, Option<String>>>,
    pub rel_tables: BTreeMap<String, BTreeSet<Vec<String>>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum KleeneVal {
    True,
    False,
    Unknown,
}

impl KleeneVal {
    pub fn as_str(self) -> &'static str {
        match self {
            KleeneVal::True => "true",
            KleeneVal::False => "false",
            KleeneVal::Unknown => "unknown",
        }
    }

    fn not(self) -> Self {
        match self {
            KleeneVal::True => KleeneVal::False,
            KleeneVal::False => KleeneVal::True,
            KleeneVal::Unknown => KleeneVal::Unknown,
        }
    }

    fn and(self, rhs: Self) -> Self {
        match (self, rhs) {
            (KleeneVal::False, _) | (_, KleeneVal::False) => KleeneVal::False,
            (KleeneVal::True, KleeneVal::True) => KleeneVal::True,
            _ => KleeneVal::Unknown,
        }
    }

    fn or(self, rhs: Self) -> Self {
        match (self, rhs) {
            (KleeneVal::True, _) | (_, KleeneVal::True) => KleeneVal::True,
            (KleeneVal::False, KleeneVal::False) => KleeneVal::False,
            _ => KleeneVal::Unknown,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum KleeneTerm {
    Defined(String),
    ExplicitAbsent,
    Unknown,
}

#[derive(Clone, Default)]
pub(super) struct PartialWorld {
    pub slots: BTreeMap<String, String>,
    pub ops: BTreeMap<String, BTreeMap<Vec<String>, Option<String>>>,
    pub op_known_defined: BTreeSet<(String, Vec<String>)>,
    pub op_graph_absent: BTreeSet<(String, Vec<String>, String)>,
    pub rels: BTreeMap<String, BTreeSet<Vec<String>>>,
    pub rel_decided: BTreeSet<(String, Vec<String>)>,
}

pub(super) fn build_partial_world_summary(
    fin: &FinitePartialPresentation,
    records: &[PartialRecordSpec],
) -> PartialWorld {
    let mut pw = PartialWorld::default();
    let mut conflicting_slots = BTreeSet::new();
    for rec in records {
        match &rec.kind {
            PartialRecordKind::SlotAssignment { slot, value } => {
                if let Some(prev) = pw.slots.get(slot) {
                    if prev != value {
                        conflicting_slots.insert(slot.clone());
                    }
                } else {
                    pw.slots.insert(slot.clone(), value.clone());
                }
            }
            PartialRecordKind::OpValue {
                op_name,
                args,
                value,
            } => match value {
                PartialValue::Known(v) => {
                    pw.ops
                        .entry(op_name.clone())
                        .or_default()
                        .insert(args.clone(), Some(v.clone()));
                }
                PartialValue::ExplicitAbsent => {
                    pw.ops
                        .entry(op_name.clone())
                        .or_default()
                        .insert(args.clone(), None);
                }
                PartialValue::UnobservedSlot(_) => {}
            },
            PartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            } => match defined {
                PartialTruth::True => {
                    pw.op_known_defined.insert((op_name.clone(), args.clone()));
                }
                PartialTruth::ExplicitAbsent => {
                    pw.ops
                        .entry(op_name.clone())
                        .or_default()
                        .insert(args.clone(), None);
                }
                PartialTruth::UnobservedSlot(_) => {}
            },
            PartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            } => match present {
                PartialTruth::True => {
                    pw.ops
                        .entry(op_name.clone())
                        .or_default()
                        .insert(args.clone(), Some(output.clone()));
                }
                PartialTruth::ExplicitAbsent => {
                    pw.op_graph_absent
                        .insert((op_name.clone(), args.clone(), output.clone()));
                }
                PartialTruth::UnobservedSlot(_) => {}
            },
            PartialRecordKind::Relation {
                rel_name,
                args,
                holds,
            } => match holds {
                PartialTruth::True => {
                    pw.rels
                        .entry(rel_name.clone())
                        .or_default()
                        .insert(args.clone());
                    pw.rel_decided.insert((rel_name.clone(), args.clone()));
                }
                PartialTruth::ExplicitAbsent => {
                    pw.rel_decided.insert((rel_name.clone(), args.clone()));
                }
                PartialTruth::UnobservedSlot(_) => {}
            },
        }
    }
    for s in &conflicting_slots {
        pw.slots.remove(s);
    }
    for bg in &fin.background_constraints {
        if let BackgroundConstraint::SlotEquality(a, b) = bg {
            if let Some(v) = pw.slots.get(a).cloned()
                && !conflicting_slots.contains(b)
            {
                pw.slots.entry(b.clone()).or_insert(v);
            } else if let Some(v) = pw.slots.get(b).cloned()
                && !conflicting_slots.contains(a)
            {
                pw.slots.entry(a.clone()).or_insert(v);
            }
        }
    }
    pw
}

pub(super) fn eval_law_kleene(
    law: &PartialEvalLawSpec,
    fin: &FinitePartialPresentation,
    partial_world: &PartialWorld,
) -> KleeneVal {
    let env = BTreeMap::new();
    let conc_val = eval_formula_kleene(&law.conclusion, &fin.sorts, partial_world, &env);
    match &law.antecedent {
        None => conc_val,
        Some(ant) => {
            let ant_val = eval_formula_kleene(ant, &fin.sorts, partial_world, &env);
            ant_val.not().or(conc_val)
        }
    }
}

fn eval_term_kleene(
    term: &PartialTerm,
    env: &BTreeMap<&str, Option<String>>,
    pw: &PartialWorld,
) -> KleeneTerm {
    match term {
        PartialTerm::Var(v) => match env.get(v.as_str()) {
            Some(Some(val)) => KleeneTerm::Defined(val.clone()),
            Some(None) => KleeneTerm::ExplicitAbsent,
            None => KleeneTerm::Unknown,
        },
        PartialTerm::Const(c) => KleeneTerm::Defined(c.clone()),
        PartialTerm::Slot(s) => match pw.slots.get(s) {
            Some(v) => KleeneTerm::Defined(v.clone()),
            None => KleeneTerm::Unknown,
        },
        PartialTerm::App { op_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                match eval_term_kleene(a, env, pw) {
                    KleeneTerm::Defined(v) => arg_vals.push(v),
                    KleeneTerm::ExplicitAbsent => return KleeneTerm::ExplicitAbsent,
                    KleeneTerm::Unknown => return KleeneTerm::Unknown,
                }
            }
            match pw.ops.get(op_name).and_then(|t| t.get(&arg_vals)) {
                Some(Some(out)) => KleeneTerm::Defined(out.clone()),
                Some(None) => KleeneTerm::ExplicitAbsent,
                None => KleeneTerm::Unknown,
            }
        }
        PartialTerm::Let { var, bound, body } => match eval_term_kleene(bound, env, pw) {
            KleeneTerm::Defined(val) => {
                let mut next = env.clone();
                next.insert(var.as_str(), Some(val));
                eval_term_kleene(body, &next, pw)
            }
            KleeneTerm::ExplicitAbsent => KleeneTerm::ExplicitAbsent,
            KleeneTerm::Unknown => KleeneTerm::Unknown,
        },
        PartialTerm::BinOp { op, lhs, rhs } => {
            let lv = match eval_term_kleene(lhs, env, pw) {
                KleeneTerm::Defined(v) => v,
                KleeneTerm::ExplicitAbsent => return KleeneTerm::ExplicitAbsent,
                KleeneTerm::Unknown => return KleeneTerm::Unknown,
            };
            let rv = match eval_term_kleene(rhs, env, pw) {
                KleeneTerm::Defined(v) => v,
                KleeneTerm::ExplicitAbsent => return KleeneTerm::ExplicitAbsent,
                KleeneTerm::Unknown => return KleeneTerm::Unknown,
            };
            match apply_binop(*op, &lv, &rv) {
                Some(res) => KleeneTerm::Defined(res),
                None => KleeneTerm::ExplicitAbsent,
            }
        }
    }
}

fn eval_formula_kleene(
    formula: &PartialFormula,
    sorts: &BTreeMap<String, Vec<String>>,
    pw: &PartialWorld,
    env: &BTreeMap<&str, Option<String>>,
) -> KleeneVal {
    match formula {
        PartialFormula::Eq(a, b) => {
            match (eval_term_kleene(a, env, pw), eval_term_kleene(b, env, pw)) {
                (KleeneTerm::ExplicitAbsent, _) | (_, KleeneTerm::ExplicitAbsent) => {
                    KleeneVal::False
                }
                (KleeneTerm::Defined(va), KleeneTerm::Defined(vb)) => {
                    if va == vb {
                        KleeneVal::True
                    } else {
                        KleeneVal::False
                    }
                }
                _ => KleeneVal::Unknown,
            }
        }
        PartialFormula::Rel { rel_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                match eval_term_kleene(a, env, pw) {
                    KleeneTerm::Defined(v) => arg_vals.push(v),
                    KleeneTerm::ExplicitAbsent => return KleeneVal::False,
                    KleeneTerm::Unknown => return KleeneVal::Unknown,
                }
            }
            if !pw
                .rel_decided
                .contains(&(rel_name.clone(), arg_vals.clone()))
            {
                KleeneVal::Unknown
            } else if pw
                .rels
                .get(rel_name)
                .is_some_and(|set| set.contains(&arg_vals))
            {
                KleeneVal::True
            } else {
                KleeneVal::False
            }
        }
        PartialFormula::Graph {
            op_name,
            args,
            output,
        } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                match eval_term_kleene(a, env, pw) {
                    KleeneTerm::Defined(v) => arg_vals.push(v),
                    KleeneTerm::ExplicitAbsent => return KleeneVal::False,
                    KleeneTerm::Unknown => return KleeneVal::Unknown,
                }
            }
            let out_v = match eval_term_kleene(output, env, pw) {
                KleeneTerm::Defined(v) => v,
                KleeneTerm::ExplicitAbsent => return KleeneVal::False,
                KleeneTerm::Unknown => return KleeneVal::Unknown,
            };
            match pw.ops.get(op_name).and_then(|t| t.get(&arg_vals)) {
                Some(Some(actual)) => {
                    if *actual == out_v {
                        KleeneVal::True
                    } else {
                        KleeneVal::False
                    }
                }
                Some(None) => KleeneVal::False,
                None => {
                    if pw
                        .op_graph_absent
                        .contains(&(op_name.clone(), arg_vals, out_v))
                    {
                        KleeneVal::False
                    } else {
                        KleeneVal::Unknown
                    }
                }
            }
        }
        PartialFormula::Defined { op_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                match eval_term_kleene(a, env, pw) {
                    KleeneTerm::Defined(v) => arg_vals.push(v),
                    KleeneTerm::ExplicitAbsent => return KleeneVal::False,
                    KleeneTerm::Unknown => return KleeneVal::Unknown,
                }
            }
            match pw.ops.get(op_name).and_then(|t| t.get(&arg_vals)) {
                Some(Some(_)) => KleeneVal::True,
                Some(None) => KleeneVal::False,
                None => {
                    if pw.op_known_defined.contains(&(op_name.clone(), arg_vals)) {
                        KleeneVal::True
                    } else {
                        KleeneVal::Unknown
                    }
                }
            }
        }
        PartialFormula::Not(inner) => eval_formula_kleene(inner, sorts, pw, env).not(),
        PartialFormula::And(list) => list.iter().fold(KleeneVal::True, |acc, f| {
            acc.and(eval_formula_kleene(f, sorts, pw, env))
        }),
        PartialFormula::Or(list) => list.iter().fold(KleeneVal::False, |acc, f| {
            acc.or(eval_formula_kleene(f, sorts, pw, env))
        }),
        PartialFormula::Exists {
            var,
            sort,
            restricted_domain,
            body,
        } => {
            let dom = restricted_domain.as_deref().unwrap_or(&sorts[sort]);
            dom.iter().fold(KleeneVal::False, |acc, elem| {
                let mut next = env.clone();
                next.insert(var.as_str(), Some(elem.clone()));
                acc.or(eval_formula_kleene(body, sorts, pw, &next))
            })
        }
        PartialFormula::Forall {
            var,
            sort,
            restricted_domain,
            body,
        } => {
            let dom = restricted_domain.as_deref().unwrap_or(&sorts[sort]);
            dom.iter().fold(KleeneVal::True, |acc, elem| {
                let mut next = env.clone();
                next.insert(var.as_str(), Some(elem.clone()));
                acc.and(eval_formula_kleene(body, sorts, pw, &next))
            })
        }
    }
}

pub(super) fn eval_term_complete(
    term: &PartialTerm,
    world: &CompleteFiniteWorld,
    env: &BTreeMap<&str, String>,
) -> Option<String> {
    match term {
        PartialTerm::Var(v) => env.get(v.as_str()).cloned(),
        PartialTerm::Const(c) => Some(c.clone()),
        PartialTerm::Slot(s) => world.slots.get(s).cloned(),
        PartialTerm::App { op_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                arg_vals.push(eval_term_complete(a, world, env)?);
            }
            world
                .op_tables
                .get(op_name)
                .and_then(|t| t.get(&arg_vals))
                .and_then(Clone::clone)
        }
        PartialTerm::Let { var, bound, body } => {
            let val = eval_term_complete(bound, world, env)?;
            let mut next = env.clone();
            next.insert(var.as_str(), val);
            eval_term_complete(body, world, &next)
        }
        PartialTerm::BinOp { op, lhs, rhs } => {
            let lv = eval_term_complete(lhs, world, env)?;
            let rv = eval_term_complete(rhs, world, env)?;
            apply_binop(*op, &lv, &rv)
        }
    }
}

pub(super) fn eval_formula_complete(
    formula: &PartialFormula,
    sorts: &BTreeMap<String, Vec<String>>,
    world: &CompleteFiniteWorld,
    env: &BTreeMap<&str, String>,
) -> Option<bool> {
    match formula {
        PartialFormula::Eq(a, b) => {
            let (Some(va), Some(vb)) = (
                eval_term_complete(a, world, env),
                eval_term_complete(b, world, env),
            ) else {
                return Some(false);
            };
            Some(va == vb)
        }
        PartialFormula::Rel { rel_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                let Some(v) = eval_term_complete(a, world, env) else {
                    return Some(false);
                };
                arg_vals.push(v);
            }
            Some(
                world
                    .rel_tables
                    .get(rel_name)
                    .is_some_and(|s| s.contains(&arg_vals)),
            )
        }
        PartialFormula::Graph {
            op_name,
            args,
            output,
        } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                let Some(v) = eval_term_complete(a, world, env) else {
                    return Some(false);
                };
                arg_vals.push(v);
            }
            let Some(out_v) = eval_term_complete(output, world, env) else {
                return Some(false);
            };
            Some(
                world
                    .op_tables
                    .get(op_name)
                    .and_then(|t| t.get(&arg_vals))
                    .is_some_and(|cell| cell.as_deref() == Some(out_v.as_str())),
            )
        }
        PartialFormula::Defined { op_name, args } => {
            let mut arg_vals = Vec::with_capacity(args.len());
            for a in args {
                let Some(v) = eval_term_complete(a, world, env) else {
                    return Some(false);
                };
                arg_vals.push(v);
            }
            Some(
                world
                    .op_tables
                    .get(op_name)
                    .and_then(|t| t.get(&arg_vals))
                    .is_some_and(Option::is_some),
            )
        }
        PartialFormula::Not(inner) => Some(!eval_formula_complete(inner, sorts, world, env)?),
        PartialFormula::And(list) => {
            for f in list {
                if !eval_formula_complete(f, sorts, world, env)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        PartialFormula::Or(list) => {
            for f in list {
                if eval_formula_complete(f, sorts, world, env)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        PartialFormula::Exists {
            var,
            sort,
            restricted_domain,
            body,
        } => {
            let dom = restricted_domain.as_deref().unwrap_or(&sorts[sort]);
            for elem in dom {
                let mut next = env.clone();
                next.insert(var.as_str(), elem.clone());
                if eval_formula_complete(body, sorts, world, &next)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        PartialFormula::Forall {
            var,
            sort,
            restricted_domain,
            body,
        } => {
            let dom = restricted_domain.as_deref().unwrap_or(&sorts[sort]);
            for elem in dom {
                let mut next = env.clone();
                next.insert(var.as_str(), elem.clone());
                if !eval_formula_complete(body, sorts, world, &next)? {
                    return Some(false);
                }
            }
            Some(true)
        }
    }
}

fn apply_binop(op: PartialArithOp, lhs: &str, rhs: &str) -> Option<String> {
    let a = lhs.parse::<BigInt>().ok()?;
    let b = rhs.parse::<BigInt>().ok()?;
    let res = match op {
        PartialArithOp::Add => a + b,
        PartialArithOp::Sub => a - b,
        PartialArithOp::Mul => a * b,
    };
    Some(res.to_string())
}
