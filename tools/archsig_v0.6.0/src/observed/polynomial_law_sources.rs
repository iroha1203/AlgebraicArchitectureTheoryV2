//! 多項式の座標を元Law出現と、既存のsource/代入/射影へ結ぶ。
use super::*;
use crate::law::ast::{ExprKind, Pattern};

struct Builder<'a> {
    inputs: &'a CheckedInputs,
    original: &'a Original,
    parts: &'a mut Vec<Part>,
    base: usize,
    control: &'a mut Control,
}
impl Builder<'_> {
    fn ty(&mut self, expression: usize) -> Result<Type, ValidationFailure> {
        tick(self.control)?;
        self.inputs
            .law()
            .expr_type(expression)
            .ok_or("多項式operandの元型がない")?
            .erase_controlled::<super::super::control::CheckFailure<Box<crate::issue::Issue>>>(
                self.control,
                Checkpoint::EquationPresentation,
            )
            .map_err(|e| match e {
                super::super::control::CheckFailure::Stopped(s) => ValidationFailure::Stop(s),
                super::super::control::CheckFailure::Input(_) => {
                    "多項式operandの原始型がない".into()
                }
            })
    }
    fn put(&mut self, part: Part) -> Result<NodeRef, ValidationFailure> {
        tick(self.control)?;
        push(self.parts, self.base, part, self.control)
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
            .exprs
            .get(expression)
            .ok_or("多項式operandの元式がない")?
            .span;
        let source = self.put(Part::Source {
            quantifiers: self.original.quantifiers.clone(),
            instance: self.original.instance,
            row: self.original.row,
            expression,
            location: Location::Law { span },
            ty: ty.clone(),
            parameters: self
                .original
                .parameters
                .iter()
                .cloned()
                .chain(locals.iter().map(|b| (b.name.clone(), b.ty.clone())))
                .collect(),
            bindings: self.original.bindings.clone(),
        })?;
        if locals.is_empty() {
            return Ok((source, ty));
        }
        let result = self.put(Part::Transform {
            quantifiers: self.original.quantifiers.clone(),
            operation: Transform::Substitute,
            parameters: self.original.parameters.clone(),
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
        if self.original.parameters.iter().any(|(n, _)| n == name)
            || self
                .original
                .bindings
                .iter()
                .chain(locals.iter())
                .any(|b| b.name == name)
        {
            return Err("多項式operandのlexical束縛名が重複する".into());
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
                quantifiers: self.original.quantifiers.clone(),
                operation: Transform::Equal,
                parameters: self.original.parameters.clone(),
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
                .exprs
                .get(current)
                .ok_or("多項式operandの外側式がない")?
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
                        other => format!("多項式operandの束縛match: {other:?}").into(),
                    })?
                    .ok_or("多項式operandのmatchが単一束縛でない")?;
                    let source = *scrutinee;
                    match &arms[0].pattern {
                        Pattern::Name(name) => {
                            let name = name.name.clone();
                            self.local(&mut locals, &name, source)?;
                        }
                        Pattern::Wild(_) => {
                            self.closed(source, &locals)?;
                        }
                        _ => return Err("多項式operandのmatch patternが違う".into()),
                    }
                    current = next;
                }
                _ => return Err("多項式operandの元等式までの束縛が違う".into()),
            }
        }
        let ExprKind::Binary { lhs, rhs, .. } = self.inputs.law().exprs[eq].kind else {
            return Err("多項式operandの元等式がない".into());
        };
        let left = self.closed(lhs, &locals)?;
        let right = self.closed(rhs, &locals)?;
        if left.1 != right.1 {
            return Err("多項式operandの左右の型が違う".into());
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
                return Err("多項式operandの成分元がTupleでない".into());
            };
            let target = items
                .get(position)
                .ok_or("多項式operandの成分が範囲外")?
                .clone();
            value = self.put(Part::Transform {
                quantifiers: self.original.quantifiers.clone(),
                operation: Transform::Project,
                parameters: self.original.parameters.clone(),
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
fn erased(ty: &Type, c: &mut Control) -> Result<Type, ValidationFailure> {
    ty.erase_controlled::<super::super::control::CheckFailure<Box<crate::issue::Issue>>>(
        c,
        Checkpoint::EquationPresentation,
    )
    .map_err(|e| match e {
        super::super::control::CheckFailure::Stopped(s) => ValidationFailure::Stop(s),
        super::super::control::CheckFailure::Input(_) => "多項式Lawの元parameter型がない".into(),
    })
}
fn original(
    readings: &crate::construction::readings::ObjectReadingInstances,
    inputs: &CheckedInputs,
    actual: Option<&super::super::object_law_transport::LawReadingRow>,
    instance: usize,
    row: Option<usize>,
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<Original, ValidationFailure> {
    tick(c)?;
    let original = readings
        .instances()
        .get(instance)
        .ok_or("多項式Lawの元instanceがない")?;
    let declaration = inputs
        .law()
        .declarations
        .get(&original.declaration().name)
        .ok_or("多項式Lawの元宣言がない")?;
    let Signature::Law {
        role,
        params,
        guard,
        body,
    } = &declaration.signature
    else {
        return Err("多項式の元宣言がLawでない".into());
    };
    let mut bindings = vec![];
    let mut parameters = vec![];
    for parameter in params {
        tick(c)?;
        let refs = original
            .bindings()
            .iter()
            .filter(|b| b.parameter().name == parameter.name)
            .collect::<Vec<_>>();
        let values = actual
            .map(|r| {
                r.bindings()
                    .iter()
                    .filter(|(n, _)| n == &parameter.name)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let (value, ty) = match (refs.as_slice(), values.as_slice()) {
            ([binding], []) => {
                let entity = match &parameter.ty {
                    Type::Ref(t) | Type::Owned(t, _) => t.clone(),
                    _ => return Err("多項式Lawの参照束縛型が違う".into()),
                };
                let fact = binding.subject();
                (
                    Some(Scalar::Subject {
                        snapshot: fact.snapshot.clone(),
                        subject: fact.subject.clone(),
                        entity: entity.clone(),
                    }),
                    Type::Ref(entity),
                )
            }
            ([], [(_, value)]) => {
                let ty = erased(&parameter.ty, c)?;
                if value.ty() != ty {
                    return Err("多項式Lawの値束縛型が違う".into());
                };
                (Some(value.scalar().clone()), ty)
            }
            ([], []) => {
                let ty = erased(&parameter.ty, c)?;
                if actual.is_some() {
                    return Err("多項式Lawの実行の値束縛がない".into());
                };
                (None, ty)
            }
            _ => return Err("多項式Lawの束縛が重複した".into()),
        };
        if let Some(value) = value {
            let value = super::super::finite_law_diagram::canonical_value(&value, c)?;
            let value = push(parts, base, Part::Scalar(value), c)?;
            bindings.push(Binding {
                name: parameter.name.clone(),
                ty,
                value,
            });
        } else {
            parameters.push((parameter.name.clone(), ty));
        }
    }
    let mut quantifiers = vec![];
    if row.is_none() {
        for parameter in original.parameters() {
            tick(c)?;
            quantifiers.push(Quantifier {
                kind: crate::law::ast::QuantKind::Forall,
                name: parameter.name.clone(),
                ty: parameter.ty.clone(),
                domain: None,
                occurrence: parameter.span,
                context: None,
            });
        }
    }
    let mut source = |expression: usize| -> Result<NodeRef, ValidationFailure> {
        tick(c)?;
        if inputs.law().expr_type(expression) != Some(&Type::Bool) {
            return Err("多項式Lawのbody/guard型がBoolでない".into());
        }
        let ast = inputs
            .law()
            .exprs
            .get(expression)
            .ok_or("多項式Lawの元式がない")?;
        push(
            parts,
            base,
            Part::Source {
                quantifiers: quantifiers.clone(),
                instance,
                row,
                expression,
                location: Location::Law { span: ast.span },
                ty: Type::Bool,
                parameters: parameters.clone(),
                bindings: bindings.clone(),
            },
            c,
        )
    };
    let body = source(*body)?;
    let guard = guard.map(&mut source).transpose()?;
    let reference = push(
        parts,
        base,
        Part::LawInstance {
            quantifiers: quantifiers.clone(),
            instance,
            row,
            name: declaration.name.clone(),
            role: *role,
            occurrence: Location::Law {
                span: declaration.span,
            },
            bindings: bindings.clone(),
            guard,
            body,
        },
        c,
    )?;
    let mut result = Original {
        instance,
        row,
        bindings,
        parameters,
        parameter_domains: None,
        body,
        guard,
        reference,
        operands: None,
        quantifiers,
    };
    let mut builder = Builder {
        inputs,
        original: &result,
        parts,
        base,
        control: c,
    };
    let Signature::Law {
        body: body_expression,
        ..
    } = declaration.signature
    else {
        return Err("多項式Lawの元bodyがない".into());
    };
    let pair = builder.pair(body_expression)?;
    result.operands = Some(pair);
    Ok(result)
}
pub(super) fn append(
    core: &EquationPresentation,
    inputs: &CheckedInputs,
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<(Vec<Original>, Vec<(NodeRef, NodeRef, NodeRef)>), ValidationFailure> {
    let mut originals = vec![];
    // Noneは元の記号的instance。空parameter域を具体rowとして埋めない。
    for e in core
        .base()
        .base()
        .evaluations()
        .iter()
        .filter(|e| e.position().object == core.object())
    {
        tick(c)?;
        let instance = e.position().instance;
        let mut template = original(
            core.base().base().readings(),
            inputs,
            None,
            instance,
            None,
            parts,
            base,
            c,
        )?;
        if e.family().is_complete()
            && e.family().missing().is_empty()
            && e.family().domains().len() == template.parameters.len()
        {
            let mut domains = vec![];
            for (expected, domain) in template.parameters.iter().zip(e.family().domains()) {
                tick(c)?;
                let parameter = domain.parameter();
                let ty = erased(&parameter.ty, c)?;
                if expected != &(parameter.name.clone(), ty.clone()) || !domain.missing().is_empty() {
                    return Err("元Law族のparameter型域が違う".into());
                }
                let mut values = vec![];
                for value in domain.values() {
                    values.push(super::reading::domain_value(
                        value.scalar(),
                        parts,
                        base,
                        c,
                    )?);
                }
                let reference = push(
                    parts,
                    base,
                    Part::ReadingDomain {
                        ty: ty.clone(),
                        elements: Some(values.clone()),
                    },
                    c,
                )?;
                domains.push(ParameterDomain {
                    name: parameter.name.clone(),
                    ty,
                    occurrence: parameter.span,
                    reference,
                    values,
                });
            }
            template.parameter_domains = Some(domains);
        }
        originals.push(template);
        for row in 0..e.family().rows().len() {
            originals.push(original(
                core.base().base().readings(),
                inputs,
                e.family().rows().get(row),
                instance,
                Some(row),
                parts,
                base,
                c,
            )?);
        }
    }
    let mut result = vec![];
    for q in core.occurrences() {
        tick(c)?;
        let key = (q.position.instance, q.row);
        let original = originals
            .iter()
            .find(|o| (o.instance, o.row) == key)
            .ok_or("多項式座標の元Law行がない")?;
        let (left, right) = original.operands.clone().ok_or("多項式の元左右式がない")?;
        let mut b = Builder {
            inputs,
            original,
            parts,
            base,
            control: c,
        };
        let lhs = b.project(left.0, left.1, &q.component)?;
        let rhs = b.project(right.0, right.1, &q.component)?;
        result.push((original.reference, lhs, rhs));
    }
    tick(c)?;
    Ok((originals, result))
}

pub(super) fn symbolic(
    inputs: &CheckedInputs,
    readings: &crate::construction::readings::ObjectReadingInstances,
    parts: &mut Vec<Part>,
    base: usize,
    c: &mut Control,
) -> Result<Vec<Original>, ValidationFailure> {
    let mut result = vec![];
    for (instance, row) in readings.instances().iter().enumerate() {
        tick(c)?;
        if row.declaration().kind == "law" {
            result.push(original(
                readings, inputs, None, instance, None, parts, base, c,
            )?);
        }
    }
    tick(c)?;
    Ok(result)
}
