//! 元ASTのlexical束縛を、既存の式変換と既出参照で閉じる。
use super::*;
use archsig_input::law::ast::{ExprKind, Pattern};

struct Builder<'a> {
    inputs: &'a CheckedInputs,
    original: &'a Original,
    parts: &'a mut Vec<Part>,
    base: usize,
    control: &'a Control,
}
impl Builder<'_> {
    fn ty(&mut self, expression: usize) -> Result<Type, ValidationFailure> {
        tick(self.control)?;
        self.inputs
            .law()
            .expr_type(expression)
            .ok_or(internal!("有限operandの元型がない"))?
            .erase_controlled::<archsig_common::control::CheckFailure<Box<archsig_common::issue::Issue>>>(
                self.control,
                Checkpoint::FiniteLawFunction,
            )
            .map_err(|e| match e {
                archsig_common::control::CheckFailure::Stopped(s) => ValidationFailure::Stop(s),
                archsig_common::control::CheckFailure::Input(_) => internal!("有限operandの原始型がない").into(),
            })
    }
    fn put(&mut self, part: Part) -> Result<NodeRef, ValidationFailure> {
        tick(self.control)?;
        push(self.parts, self.base, part)
    }
    fn closed(
        &mut self,
        expression: usize,
        locals: &[Binding],
    ) -> Result<(NodeRef, Type), ValidationFailure> {
        let ty = self.ty(expression)?;
        let span = self
            .inputs
            .law()
            .exprs()
            .get(expression)
            .ok_or(internal!("有限operandの元式がない"))?
            .span;
        let source = self.put(Part::Source {
            column: self.original.column,
            expression,
            location: Location::Law { span },
            ty: ty.clone(),
            parameters: locals
                .iter()
                .map(|b| (b.name.clone(), b.ty.clone()))
                .collect(),
            bindings: self.original.bindings.clone(),
        })?;
        if locals.is_empty() {
            return Ok((source, ty));
        }
        let result = self.put(Part::Transform {
            operation: Transform::Substitute,
            ty: ty.clone(),
            operands: vec![source],
            bindings: locals.to_vec(),
            position: None,
        })?;
        Ok((result, ty))
    }
    fn local(
        &mut self,
        locals: &mut Vec<Binding>,
        name: &str,
        expression: usize,
    ) -> Result<(), ValidationFailure> {
        if self
            .original
            .bindings
            .iter()
            .chain(locals.iter())
            .any(|b| b.name == name)
        {
            return Err(internal!("有限operandのlexical束縛名が重複する").into());
        }
        let (value, ty) = self.closed(expression, locals)?;
        locals.push(Binding {
            name: name.into(),
            value,
            ty,
        });
        Ok(())
    }
    fn pair(
        &mut self,
        body: usize,
    ) -> Result<((NodeRef, Type), (NodeRef, Type)), ValidationFailure> {
        let eq = super::super::environment::finite_law_valuations::equation(
            self.inputs,
            body,
            self.control,
        )?;
        let Some(eq) = eq else {
            // 一般条件の原bodyを保持し、恒真は固定のUnit等値として構成する。
            let unit = self.put(Part::Scalar(Scalar::Unit))?;
            let truth = self.put(Part::Transform {
                operation: Transform::Equal,
                ty: Type::Bool,
                operands: vec![unit, unit],
                bindings: vec![],
                position: None,
            })?;
            return Ok(((self.original.body, Type::Bool), (truth, Type::Bool)));
        };
        let mut locals = vec![];
        let mut current = body;
        while current != eq {
            tick(self.control)?;
            match &self
                .inputs
                .law()
                .exprs()
                .get(current)
                .ok_or(internal!("有限operandの外側式がない"))?
                .kind
            {
                ExprKind::Group(child) => current = *child,
                ExprKind::Let { name, value, body } => {
                    let (name, value, next) = (name.name.clone(), *value, *body);
                    self.local(&mut locals, &name, value)?;
                    current = next;
                }
                ExprKind::Match { scrutinee, arms } => {
                    let next = super::super::object_law_residuals::binding_match_body(
                        self.inputs,
                        *scrutinee,
                        arms,
                        self.control,
                    )
                    .map_err(|e| match e {
                        crate::construction::ConstructionFailure::Stopped(s) => {
                            ValidationFailure::Stop(s)
                        }
                        other => internal!(format!("有限operandの束縛match: {other:?}")).into(),
                    })?
                    .ok_or(internal!("有限operandのmatchが単一束縛でない"))?;
                    let source = *scrutinee;
                    match &arms[0].pattern {
                        Pattern::Name(name) => {
                            let name = name.name.clone();
                            self.local(&mut locals, &name, source)?;
                        }
                        Pattern::Wild(_) => {
                            self.closed(source, &locals)?;
                        }
                        _ => return Err(internal!("有限operandのmatch patternが違う").into()),
                    }
                    current = next;
                }
                _ => return Err(internal!("有限operandの元等式までの束縛が違う").into()),
            }
        }
        let ExprKind::Binary { lhs, rhs, .. } = self.inputs.law().exprs()[eq].kind else {
            return Err(internal!("有限operandの元等式がない").into());
        };
        let left = self.closed(lhs, &locals)?;
        let right = self.closed(rhs, &locals)?;
        if left.1 != right.1 {
            return Err(internal!("有限operandの左右の型が違う").into());
        }
        Ok((left, right))
    }
    fn project(
        &mut self,
        mut value: NodeRef,
        mut ty: Type,
        path: &[usize],
    ) -> Result<NodeRef, ValidationFailure> {
        for &position in path {
            tick(self.control)?;
            let Type::Tuple(items) = &ty else {
                return Err(internal!("有限operandの成分元がTupleでない").into());
            };
            let target = items
                .get(position)
                .ok_or(internal!("有限operandの成分が範囲外"))?
                .clone();
            value = self.put(Part::Transform {
                operation: Transform::Project,
                ty: target.clone(),
                operands: vec![value],
                bindings: vec![],
                position: Some(position),
            })?;
            ty = target;
        }
        Ok(value)
    }
}
pub(super) fn append(
    f: &AutomaticLawValuations,
    inputs: &CheckedInputs,
    originals: &[Original],
    columns: &[usize],
    components: &[(usize, Option<Vec<usize>>)],
    parts: &mut Vec<Part>,
    base: usize,
    c: &Control,
) -> Result<Vec<(NodeRef, NodeRef)>, ValidationFailure> {
    let mut pairs = std::collections::BTreeMap::new();
    for original in originals {
        tick(c)?;
        let column = f
            .columns()
            .get(original.column)
            .ok_or(internal!("有限operandの元columnがない"))?;
        let Signature::Law { body, .. } = column.declaration().signature else {
            return Err(internal!("有限operandの元宣言がLawでない").into());
        };
        let mut b = Builder {
            inputs,
            original,
            parts,
            base,
            control: c,
        };
        let pair = b.pair(body)?;
        if pairs.insert(original.column, pair).is_some() {
            return Err(internal!("有限operandの元columnが重複する").into());
        }
    }
    if columns.len() != components.len() {
        return Err(internal!("有限operandの元成分数が違う").into());
    }
    let mut result = vec![];
    for (&column, (instance, path)) in columns.iter().zip(components) {
        tick(c)?;
        let original = originals
            .iter()
            .find(|o| o.column == column && o.instance == *instance)
            .ok_or(internal!("有限operandの元instanceが違う"))?;
        let (left, right) = pairs
            .get(&column)
            .ok_or(internal!("有限operandの左右がない"))?;
        let mut b = Builder {
            inputs,
            original,
            parts,
            base,
            control: c,
        };
        let path = path.as_deref().unwrap_or(&[]);
        result.push((
            b.project(left.0, left.1.clone(), path)?,
            b.project(right.0, right.1.clone(), path)?,
        ));
    }
    tick(c)?;
    Ok(result)
}
