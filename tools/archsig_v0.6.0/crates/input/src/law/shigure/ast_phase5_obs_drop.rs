//! `PartialTerm`・`PartialFormula` 系の深い構文木に対する反復 `Drop` 実装。

use super::ast_phase5_obs::{
    RawPartialFormula, RawPartialTerm, ShigurePartialFormula, ShigurePartialTerm,
};

fn take_raw_term_children(t: &mut RawPartialTerm, stack: &mut Vec<RawPartialTerm>) {
    let leaf = || RawPartialTerm::ConstLit(String::new(), (0, 0));
    match t {
        RawPartialTerm::IdentOrConst(_)
        | RawPartialTerm::ConstLit(_, _)
        | RawPartialTerm::ExplicitConst(_, _)
        | RawPartialTerm::Slot(_) => {}
        RawPartialTerm::App { args, .. } => stack.append(args),
        RawPartialTerm::Let { bound, body, .. } => {
            stack.push(std::mem::replace(&mut **bound, leaf()));
            stack.push(std::mem::replace(&mut **body, leaf()));
        }
        RawPartialTerm::BinOp { lhs, rhs, .. } => {
            stack.push(std::mem::replace(&mut **lhs, leaf()));
            stack.push(std::mem::replace(&mut **rhs, leaf()));
        }
    }
}

impl Drop for RawPartialTerm {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_raw_term_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_raw_term_children(&mut node, &mut stack);
        }
    }
}

fn take_shigure_term_children(t: &mut ShigurePartialTerm, stack: &mut Vec<ShigurePartialTerm>) {
    let leaf = || ShigurePartialTerm::Var(String::new());
    match t {
        ShigurePartialTerm::Var(_) | ShigurePartialTerm::Const(_) | ShigurePartialTerm::Slot(_) => {
        }
        ShigurePartialTerm::App { args, .. } => stack.append(args),
        ShigurePartialTerm::Let { bound, body, .. } => {
            stack.push(std::mem::replace(&mut **bound, leaf()));
            stack.push(std::mem::replace(&mut **body, leaf()));
        }
        ShigurePartialTerm::BinOp { lhs, rhs, .. } => {
            stack.push(std::mem::replace(&mut **lhs, leaf()));
            stack.push(std::mem::replace(&mut **rhs, leaf()));
        }
    }
}

impl Drop for ShigurePartialTerm {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_shigure_term_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_shigure_term_children(&mut node, &mut stack);
        }
    }
}

fn take_raw_formula_children(f: &mut RawPartialFormula, stack: &mut Vec<RawPartialFormula>) {
    let leaf = || RawPartialFormula::And(Vec::new(), (0, 0));
    match f {
        RawPartialFormula::Eq(_, _, _)
        | RawPartialFormula::Rel { .. }
        | RawPartialFormula::Graph { .. }
        | RawPartialFormula::Defined { .. } => {}
        RawPartialFormula::Not(inner, _)
        | RawPartialFormula::Exists { body: inner, .. }
        | RawPartialFormula::Forall { body: inner, .. } => {
            stack.push(std::mem::replace(&mut **inner, leaf()));
        }
        RawPartialFormula::And(list, _) | RawPartialFormula::Or(list, _) => stack.append(list),
    }
}

impl Drop for RawPartialFormula {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_raw_formula_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_raw_formula_children(&mut node, &mut stack);
        }
    }
}

fn take_shigure_formula_children(
    f: &mut ShigurePartialFormula,
    stack: &mut Vec<ShigurePartialFormula>,
) {
    let leaf = || ShigurePartialFormula::And(Vec::new());
    match f {
        ShigurePartialFormula::Eq(_, _)
        | ShigurePartialFormula::Rel { .. }
        | ShigurePartialFormula::Graph { .. }
        | ShigurePartialFormula::Defined { .. } => {}
        ShigurePartialFormula::Not(inner)
        | ShigurePartialFormula::Exists { body: inner, .. }
        | ShigurePartialFormula::Forall { body: inner, .. } => {
            stack.push(std::mem::replace(&mut **inner, leaf()));
        }
        ShigurePartialFormula::And(list) | ShigurePartialFormula::Or(list) => stack.append(list),
    }
}

impl Drop for ShigurePartialFormula {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_shigure_formula_children(self, &mut stack);
        while let Some(mut node) = stack.pop() {
            take_shigure_formula_children(&mut node, &mut stack);
        }
    }
}
