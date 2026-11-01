//! 型検査を終えた式と静的参照。評価ごとの索引構築を持たない。
use super::{
    ast::{Expr, ExprId, ExprKind, Span},
    model::DeclarationInfo,
};
use crate::{
    control::{Checkpoint, Control},
    json::InputError,
    names::QualifiedName,
    types::Type,
};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub(crate) enum Callee {
    View(String),
    Ctor(String, usize),
    Builtin(&'static str),
    Value(Type),
}
#[derive(Clone, Debug)]
pub(crate) struct Projection {
    pub name: QualifiedName,
    pub span: Span,
    pub ty: Type,
}
#[derive(Clone, Copy, Debug)]
pub(crate) enum BindingSource {
    Parameter,
    Let,
    Iteration,
    Pattern,
    TypeQuantifier,
}
#[derive(Clone, Debug)]
pub(crate) struct Lexical {
    pub source: BindingSource,
    pub name: String,
    pub ty: Type,
    pub projections: Vec<Projection>,
}
#[derive(Debug)]
pub(crate) struct Expression {
    pub kind: ExprKind,
    pub span: Span,
    pub ty: Option<Type>,
    pub lexical: Option<Lexical>,
    pub field: Option<QualifiedName>,
}
#[derive(Debug, Default)]
pub(crate) struct Program {
    pub nodes: Vec<Expression>,
    pub callees: BTreeMap<ExprId, Callee>,
    pub expressions: BTreeMap<Span, ExprId>,
    pub dotted_candidates: BTreeMap<Span, Vec<(ExprId, usize)>>,
    pub references: BTreeMap<Span, Vec<QualifiedName>>,
}
impl Program {
    pub fn build<E: InputError>(
        exprs: &[Expr],
        types: &[Option<Type>],
        infos: &[DeclarationInfo],
        lexical: &[(ExprId, Lexical)],
        callees: &[(ExprId, Callee)],
        fields: &[(ExprId, QualifiedName)],
        control: &mut Control,
    ) -> Result<Self, E> {
        let mut program = Self::default();
        let mut bindings = BTreeMap::new();
        for (id, binding) in lexical {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            bindings.insert(*id, binding);
            E::checkpoint(control, Checkpoint::LawIteration)?;
        }
        let mut projections = BTreeMap::new();
        for (id, field) in fields {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            projections.insert(*id, field);
            E::checkpoint(control, Checkpoint::LawIteration)?;
        }
        for (id, expr) in exprs.iter().enumerate() {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            let ty = types.get(id).cloned().flatten();
            if ty.is_some() {
                program.expressions.insert(expr.span, id);
                if let ExprKind::Dotted(parts) = &expr.kind
                    && let Some(first) = parts.first()
                {
                    for (index, part) in parts.iter().enumerate() {
                        E::checkpoint(control, Checkpoint::LawIteration)?;
                        program
                            .dotted_candidates
                            .entry((first.span.0, part.span.1))
                            .or_default()
                            .push((id, index + 1));
                        E::checkpoint(control, Checkpoint::LawIteration)?;
                    }
                }
            }
            program.nodes.push(Expression {
                kind: expr.kind.clone(),
                span: expr.span,
                ty,
                lexical: bindings.get(&id).map(|value| (*value).clone()),
                field: projections.get(&id).map(|value| (*value).clone()),
            });
            E::checkpoint(control, Checkpoint::LawIteration)?;
        }
        for info in infos {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            for (span, target) in &info.references {
                E::checkpoint(control, Checkpoint::LawIteration)?;
                program
                    .references
                    .entry(*span)
                    .or_default()
                    .push(target.clone().into());
                E::checkpoint(control, Checkpoint::LawIteration)?;
            }
            E::checkpoint(control, Checkpoint::LawIteration)?;
        }
        for (id, target) in callees {
            E::checkpoint(control, Checkpoint::LawIteration)?;
            program.callees.insert(*id, target.clone());
            E::checkpoint(control, Checkpoint::LawIteration)?;
        }
        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        control::CheckFailure,
        definition::check_definitions,
        issue::Issue,
        law::{check_law, model::Signature},
        result::Signal,
    };
    use std::{cell::Cell, rc::Rc};

    #[test]
    fn lexical_paths_keep_the_resolved_binder_field_and_type() {
        let definitions = check_definitions(&[(
            "counter",
            include_bytes!("../../tests/fixtures/counter.atoms.json").as_slice(),
        )])
        .unwrap();
        let source = include_str!("../../tests/fixtures/counter.law");
        let law = check_law(source.as_bytes(), &definitions).unwrap();
        let Signature::View { params, body, .. } = &law.declarations["CountCheck.amount"].signature
        else {
            panic!()
        };
        let node = &law.program.nodes[*body];
        let lexical = node.lexical.as_ref().unwrap();
        assert_eq!(lexical.name, params[0].name);
        assert_eq!(lexical.name, "s");
        assert_eq!(lexical.ty, Type::Ref("Counter.State".into()));
        assert_eq!(node.ty, Some(Type::Z));
        assert_eq!(lexical.projections.len(), 1);
        assert_eq!(lexical.projections[0].name, "Counter.State.count");
        assert_eq!(lexical.projections[0].ty, Type::Z);
        assert_eq!(
            &source[lexical.projections[0].span.0..lexical.projections[0].span.1],
            "count"
        );
        assert_eq!(law.program.expressions[&node.span], *body);
        assert!(law.program.dotted_candidates[&node.span].contains(&(*body, 2)));
    }

    #[test]
    fn short_and_qualified_calls_keep_the_same_resolved_target() {
        let definitions = check_definitions(&[(
            "counter",
            include_bytes!("../../tests/fixtures/counter.atoms.json").as_slice(),
        )])
        .unwrap();
        for call in ["amount(s)", "CountCheck.amount(s)", "(amount)(s)"] {
            let source = include_str!("../../tests/fixtures/counter.law")
                .replace("s.count >= 0", &format!("{call} >= 0"));
            let law = check_law(source.as_bytes(), &definitions).unwrap();
            let (_, node) = law
                .program
                .nodes
                .iter()
                .enumerate()
                .find(|(_, node)| &source[node.span.0..node.span.1] == call)
                .unwrap();
            let ExprKind::Call { callee, .. } = node.kind else {
                panic!()
            };
            assert!(
                matches!(&law.program.callees[&callee], Callee::View(target) if target == "CountCheck.amount")
            );
            assert_eq!(node.ty, Some(Type::Z));
        }
    }

    #[test]
    fn lowering_stops_during_each_finite_iteration() {
        let definitions = check_definitions(&[(
            "counter",
            include_bytes!("../../tests/fixtures/counter.atoms.json").as_slice(),
        )])
        .unwrap();
        let source = include_str!("../../tests/fixtures/counter.law")
            .replace("s.count;", "(s).count;")
            .replace("s.count >= 0", "amount(s) >= 0");
        let law = check_law(source.as_bytes(), &definitions).unwrap();
        let fields = law.program.nodes.iter().enumerate().filter_map(|(id, node)| node.field.clone().map(|field| (id, field))).collect::<Vec<_>>();
        assert!(!fields.is_empty());
        assert!(!law.program.callees.is_empty());
        let lexical = law
            .program
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(id, node)| node.lexical.clone().map(|lexical| (id, lexical)))
            .collect::<Vec<_>>();
        let samples = Rc::new(Cell::new(0));
        let observed = samples.clone();
        let mut control = Control::new(move |_| {
            observed.set(observed.get() + 1);
            None
        });
        Program::build::<CheckFailure<Box<Issue>>>(
            &law.exprs,
            &law.expr_types,
            &law.infos,
            &lexical,
            &law.program
                .callees
                .iter()
                .map(|(id, target)| (*id, target.clone()))
                .collect::<Vec<_>>(),
            &fields,
            &mut control,
        )
        .unwrap();
        assert!(samples.get() > law.program.nodes.len());
        for stop in 1..=samples.get() {
            let count = Rc::new(Cell::new(0));
            let observed = count.clone();
            let mut control = Control::new(move |_| {
                observed.set(observed.get() + 1);
                (observed.get() == stop).then_some(Signal::Term)
            });
            let result = Program::build::<CheckFailure<Box<Issue>>>(
                &law.exprs,
                &law.expr_types,
                &law.infos,
                &lexical,
                &law.program
                    .callees
                    .iter()
                    .map(|(id, target)| (*id, target.clone()))
                    .collect::<Vec<_>>(),
                &fields,
                &mut control,
            );
            assert!(matches!(result, Err(CheckFailure::Stopped(_))));
            assert_eq!(count.get(), stop);
        }
    }
}
