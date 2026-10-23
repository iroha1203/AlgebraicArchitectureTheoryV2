//! 固定した元Lawと束縛を、共有原始位置の有限候補上で読む。
use super::*;
use crate::law::model::{Declaration, Signature};
use crate::observed::{finite, input::InputSources};
use num_bigint::BigInt;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) enum FiniteLawState {
    Pending,
    Ready,
    OutsideFinite { position: Fact, ty: Type },
    Undetermined { location: Location, reason: String },
    ConditionFailed,
    Unavailable { location: Location, feature: String },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct FiniteLawComponent {
    pub path: Vec<usize>,
    pub ty: Type,
    pub left: Option<Scalar>,
    pub right: Option<Scalar>,
    pub equal: Option<bool>,
    pub indicator: Option<BigInt>,
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct FiniteLawRow {
    pub point: usize,
    /// 元instanceの適用と束縛の型条件。元Lawのguardとは別。
    pub application: Option<bool>,
    /// instanceとOwned束縛の適用を読む未観測位置。
    pub application_missing: Vec<Fact>,
    pub guard: Option<bool>,
    pub predicate: Option<bool>,
    pub operands: Option<(Type, Option<Scalar>, Option<Scalar>)>,
    pub components: Option<Vec<FiniteLawComponent>>,
    pub indicator: Option<BigInt>,
    pub condition_failed: bool,
    pub condition_pending: bool,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
#[derive(Clone)]
struct Selection {
    law: String,
    bindings: Vec<(String, Scalar)>,
}
pub(in crate::observed) struct FiniteLawValuations {
    sources: InputSources,
    selection: Arc<Selection>,
    declaration: Declaration,
    bindings: Vec<(String, Scalar)>,
    positions: Vec<Fact>,
    types: Vec<Type>,
    domain: Vec<Vec<Scalar>>,
    domain_complete: bool,
    observed_point: Option<usize>,
    rows: Vec<FiniteLawRow>,
    state: FiniteLawState,
}
pub(in crate::observed) struct FiniteLawFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteLawValuations>>,
}
impl std::fmt::Debug for FiniteLawFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FiniteLawFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.clone().checkpoint(Checkpoint::FiniteLawDomain)?;
    Ok(())
}
fn source(value: Scalar) -> SourceValue {
    SourceValue {
        condition_failed: false,
        condition_pending: false,
        symbolic: None,
        comparison: None,
        affine: None,
        scope: Scope::default(),
        known_value: Some(value),
        support: vec![],
        scalar_scope: Some(Scope::default()),
    }
}
impl FiniteLawValuations {
    pub fn declaration(&self) -> &Declaration {
        &self.declaration
    }
    pub fn bindings(&self) -> &[(String, Scalar)] {
        &self.bindings
    }
    pub fn positions(&self) -> &[Fact] {
        &self.positions
    }
    pub fn types(&self) -> &[Type] {
        &self.types
    }
    pub fn domain(&self) -> &[Vec<Scalar>] {
        &self.domain
    }
    pub fn domain_complete(&self) -> bool {
        self.domain_complete
    }
    pub fn observed_point(&self) -> Option<usize> {
        self.observed_point
    }
    pub fn rows(&self) -> &[FiniteLawRow] {
        &self.rows
    }
    pub fn state(&self) -> &FiniteLawState {
        &self.state
    }
    pub fn is_complete(&self) -> bool {
        self.state == FiniteLawState::Ready
    }
    pub fn recheck(&self, inputs: &CheckedInputs, c: &mut Control) -> Result<(), FiniteLawFailure> {
        let fail = |message: &str| FiniteLawFailure {
            cause: message.into(),
            partial: None,
        };
        if &self.sources != inputs.sources() {
            return Err(fail("有限Law表の元三入力が違う"));
        }
        let expected =
            finite_law_valuations(inputs, &self.selection.law, &self.selection.bindings, c)?;
        let result = (|| -> Result<bool, ValidationFailure> {
            tick(c)?;
            if self.declaration != expected.declaration
                || self.positions != expected.positions
                || self.types != expected.types
                || self.domain_complete != expected.domain_complete
                || self.observed_point != expected.observed_point
                || self.state != expected.state
                || self.bindings.len() != expected.bindings.len()
                || self.domain.len() != expected.domain.len()
                || self.rows.len() != expected.rows.len()
            {
                return Ok(false);
            }
            for ((n, a), (m, b)) in self.bindings.iter().zip(&expected.bindings) {
                tick(c)?;
                if n != m || !validation_identity::scalar(a, b, c)? {
                    return Ok(false);
                }
            }
            for (a, b) in self.domain.iter().zip(&expected.domain) {
                tick(c)?;
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if !validation_identity::scalar(a, b, c)? {
                        return Ok(false);
                    }
                }
            }
            for (a, b) in self.rows.iter().zip(&expected.rows) {
                tick(c)?;
                if a != b {
                    return Ok(false);
                }
            }
            tick(c)?;
            Ok(true)
        })();
        match result {
            Ok(true) => Ok(()),
            other => Err(FiniteLawFailure {
                cause: other
                    .err()
                    .unwrap_or_else(|| "有限Law表が元宣言・束縛・全候補・元評価と違う".into()),
                partial: Some(Box::new(expected)),
            }),
        }
    }
}

pub(in crate::observed) fn finite_law_valuations(
    inputs: &CheckedInputs,
    law: &str,
    bindings: &[(String, Scalar)],
    c: &mut Control,
) -> Result<FiniteLawValuations, FiniteLawFailure> {
    let selected = vec![(law.to_owned(), bindings.to_vec())];
    match finite_law_family_valuations(inputs, &selected, c) {
        Ok(family) => Ok(single(family)),
        Err(f) => Err(FiniteLawFailure {
            cause: f.cause,
            partial: f.partial.map(|r| Box::new(single(*r))),
        }),
    }
}
fn single(mut r: FiniteLawFamilyValuations) -> FiniteLawValuations {
    // 単一Law入口だけが呼ぶため、宣言選択後は必ず一列ある。
    let column = r.columns.remove(0);
    FiniteLawValuations {
        sources: r.sources,
        selection: Arc::clone(&r.selection[0]),
        declaration: column.declaration,
        bindings: column.bindings,
        positions: r.positions,
        types: r.types,
        domain: r.domain,
        domain_complete: r.domain_complete,
        observed_point: r.observed_point,
        rows: column.rows,
        state: r.state,
    }
}
/// 同じ原始代入を読む元Lawの一出現。列の順序・重複も元選択のまま保持する。
#[derive(Clone)]
pub(in crate::observed) struct FiniteLawColumn {
    declaration: Declaration,
    source_instance: Option<usize>,
    equation_type: Option<Type>,
    bindings: Vec<(String, Scalar)>,
    rows: Vec<FiniteLawRow>,
}
impl FiniteLawColumn {
    pub fn declaration(&self) -> &Declaration {
        &self.declaration
    }
    pub fn source_instance(&self) -> Option<usize> {
        self.source_instance
    }
    pub fn bindings(&self) -> &[(String, Scalar)] {
        &self.bindings
    }
    pub fn rows(&self) -> &[FiniteLawRow] {
        &self.rows
    }
    pub fn required(&self) -> bool {
        matches!(
            self.declaration.signature,
            Signature::Law {
                role: crate::law::ast::Role::Required,
                ..
            }
        )
    }
}
pub(in crate::observed) struct FiniteLawFamilyValuations {
    object: Option<Arc<object::Selection>>,
    column_objects: Option<object::Columns>,
    instance_mode: bool,
    sources: InputSources,
    selection: Vec<Arc<Selection>>,
    columns: Vec<FiniteLawColumn>,
    owner: Arc<()>,
    positions: Vec<Fact>,
    types: Vec<Type>,
    domain: Vec<Vec<Scalar>>,
    domain_complete: bool,
    observed_point: Option<usize>,
    state: FiniteLawState,
    required_zero: Option<Vec<usize>>,
}
pub(in crate::observed) struct FiniteLawFamilyFailure {
    pub cause: ValidationFailure,
    pub partial: Option<Box<FiniteLawFamilyValuations>>,
}
impl std::fmt::Debug for FiniteLawFamilyFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FiniteLawFamilyFailure")
            .field("cause", &self.cause)
            .field("has_partial", &self.partial.is_some())
            .finish()
    }
}
impl FiniteLawFamilyValuations {
    pub fn columns(&self) -> &[FiniteLawColumn] {
        &self.columns
    }
    pub fn positions(&self) -> &[Fact] {
        &self.positions
    }
    pub fn types(&self) -> &[Type] {
        &self.types
    }
    pub fn domain(&self) -> &[Vec<Scalar>] {
        &self.domain
    }
    pub fn domain_complete(&self) -> bool {
        self.domain_complete
    }
    pub fn observed_point(&self) -> Option<usize> {
        self.observed_point
    }
    pub fn state(&self) -> &FiniteLawState {
        &self.state
    }
    pub fn is_complete(&self) -> bool {
        self.state == FiniteLawState::Ready
    }
    /// Z^D のrequired指示関数が同時に零である座標。未完成/未決ではNone。
    pub fn required_zero(&self) -> Option<&[usize]> {
        self.required_zero.as_deref()
    }
    pub fn recheck(
        &self,
        inputs: &CheckedInputs,
        c: &mut Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        if &self.sources != inputs.sources() {
            return Err(FiniteLawFamilyFailure {
                cause: "有限Law族の元三入力が違う".into(),
                partial: None,
            });
        }
        let selected = self
            .selection
            .iter()
            .map(|s| (s.law.clone(), s.bindings.clone()))
            .collect::<Vec<_>>();
        let instances = if self.instance_mode {
            Some(self.columns.iter().map(|column| {
                column.source_instance.ok_or_else(|| FiniteLawFamilyFailure {
                    cause: "元Law列にinstance位置がない".into(),
                    partial: None,
                })
            }).collect::<Result<Vec<_>, _>>()?)
        } else {
            if self.columns.iter().any(|column| column.source_instance.is_some()) {
                return Err(FiniteLawFamilyFailure {
                    cause: "通常のLaw列へ元instanceを追加した".into(),
                    partial: None,
                });
            }
            None
        };
        let expected = family_with_instances(
            inputs,
            &selected,
            self.object.clone(),
            self.column_objects.clone(),
            instances,
            c,
        )?;
        self.check_expected(expected, c)
    }
    fn check_expected(
        &self,
        expected: Self,
        c: &mut Control,
    ) -> Result<(), FiniteLawFamilyFailure> {
        let result = (|| -> Result<bool, ValidationFailure> {
            tick(c)?;
            if self.sources != expected.sources
                || self.object != expected.object
                || self.column_objects != expected.column_objects
                || self.instance_mode != expected.instance_mode
                || self.positions != expected.positions
                || self.types != expected.types
                || self.domain_complete != expected.domain_complete
                || self.observed_point != expected.observed_point
                || self.state != expected.state
                || self.required_zero != expected.required_zero
                || self.domain.len() != expected.domain.len()
                || self.columns.len() != expected.columns.len()
                || self.selection.len() != expected.selection.len()
            {
                return Ok(false);
            }
            for (a, b) in self.domain.iter().zip(&expected.domain) {
                tick(c)?;
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if !validation_identity::scalar(a, b, c)? {
                        return Ok(false);
                    }
                }
            }
            for (a, b) in self.selection.iter().zip(&expected.selection) {
                tick(c)?;
                if a.law != b.law || a.bindings.len() != b.bindings.len() {
                    return Ok(false);
                }
                for ((name, a), (other, b)) in a.bindings.iter().zip(&b.bindings) {
                    if name != other || !validation_identity::scalar(a, b, c)? {
                        return Ok(false);
                    }
                }
            }
            for (a, b) in self.columns.iter().zip(&expected.columns) {
                tick(c)?;
                if a.declaration != b.declaration
                    || a.source_instance != b.source_instance
                    || a.equation_type != b.equation_type
                    || a.bindings.len() != b.bindings.len()
                    || a.rows != b.rows
                {
                    return Ok(false);
                }
                for ((n, a), (m, b)) in a.bindings.iter().zip(&b.bindings) {
                    tick(c)?;
                    if n != m || !validation_identity::scalar(a, b, c)? {
                        return Ok(false);
                    }
                }
            }
            tick(c)?;
            Ok(true)
        })();
        match result {
            Ok(true) => Ok(()),
            other => Err(FiniteLawFamilyFailure {
                cause: other.err().unwrap_or_else(|| {
                    "有限Law族が元選択・共有D・全列・required零座標と違う".into()
                }),
                partial: Some(Box::new(expected)),
            }),
        }
    }
}
pub(in crate::observed) fn finite_law_family_valuations(
    inputs: &CheckedInputs,
    selected: &[(String, Vec<(String, Scalar)>)],
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    family_with_object(inputs, selected, None, c)
}
fn family_with_object(
    inputs: &CheckedInputs,
    selected: &[(String, Vec<(String, Scalar)>)],
    object: Option<Arc<object::Selection>>,
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    family_with_column_objects(inputs, selected, object, None, c)
}
fn family_with_column_objects(
    inputs: &CheckedInputs,
    selected: &[(String, Vec<(String, Scalar)>)],
    object: Option<Arc<object::Selection>>,
    column_objects: Option<object::Columns>,
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    family_with_instances(inputs, selected, object, column_objects, None, c)
}
fn family_with_instances(
    inputs: &CheckedInputs,
    selected: &[(String, Vec<(String, Scalar)>)],
    object: Option<Arc<object::Selection>>,
    column_objects: Option<object::Columns>,
    instance_indices: Option<Vec<usize>>,
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    family_with_instance_domain(
        inputs,
        selected,
        object,
        column_objects,
        instance_indices,
        &[],
        c,
    )
}
fn family_with_instance_domain(
    inputs: &CheckedInputs,
    selected: &[(String, Vec<(String, Scalar)>)],
    object: Option<Arc<object::Selection>>,
    column_objects: Option<object::Columns>,
    instance_indices: Option<Vec<usize>>,
    positions: &[Fact],
    c: &mut Control,
) -> Result<FiniteLawFamilyValuations, FiniteLawFamilyFailure> {
    if instance_indices.as_ref()
        .is_some_and(|indices| indices.len() != selected.len() || column_objects.is_none())
    {
        return Err(FiniteLawFamilyFailure {
            cause: "元instanceとLaw列の対応が違う".into(),
            partial: None,
        });
    }
    if column_objects.as_ref()
        .is_some_and(|objects| objects.columns.len() != selected.len())
        || (object.is_some() && column_objects.is_some())
    {
        return Err(FiniteLawFamilyFailure {
            cause: "有限Lawの列と対象族の対応が違う".into(),
            partial: None,
        });
    }
    if let Some(objects) = &column_objects {
        if objects.columns.iter().any(|object| !object.belongs_to(&objects.readings)) {
            return Err(FiniteLawFamilyFailure {
                cause: "有限Law列の対象が共通の元readingsと違う".into(),
                partial: None,
            });
        }
        objects.readings.recheck(inputs, c).map_err(|cause| FiniteLawFamilyFailure {
            cause: object::failure(cause),
            partial: None,
        })?;
    }
    for object in object.iter().chain(
        column_objects.iter().flat_map(|objects| objects.columns.iter()),
    ) {
        object.recheck(inputs, c).map_err(|cause| FiniteLawFamilyFailure {
            cause,
            partial: None,
        })?;
    }
    let mut columns = vec![];
    let mut selection = vec![];
    for (index, (law, bindings)) in selected.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteLawSelection)
            .map_err(|cause| FiniteLawFamilyFailure {
                cause: cause.into(),
                partial: None,
            })?;
        let decl = inputs
            .law()
            .declarations
            .get(law)
            .ok_or_else(|| FiniteLawFamilyFailure {
                cause: "有限Lawの元宣言がない".into(),
                partial: None,
            })?;
        if !matches!(decl.signature, Signature::Law { .. }) {
            return Err(FiniteLawFamilyFailure {
                cause: "有限Lawの選択がLawでない".into(),
                partial: None,
            });
        }
        if column_objects.as_ref()
            .and_then(|objects| objects.columns.get(index))
            .or(object.as_ref())
            .is_some_and(|o| o.identity().reading() != decl.reading)
        {
            return Err(FiniteLawFamilyFailure {
                cause: "有限Lawのreadingが選択対象と違う".into(),
                partial: None,
            });
        }
        if let Some(indices) = &instance_indices {
            let objects = column_objects.as_ref().ok_or_else(|| FiniteLawFamilyFailure {
                cause: "元instanceの対象族がない".into(),
                partial: None,
            })?;
            object::instance::validate_selection(
                inputs, objects, index, indices[index], law, bindings, c,
            ).map_err(|cause| FiniteLawFamilyFailure { cause, partial: None })?;
        }
        let Signature::Law { body, .. } = decl.signature else {
            return Err(FiniteLawFamilyFailure {
                cause: "元Lawがない".into(),
                partial: None,
            });
        };
        let equation_type = equation(inputs, body, c)
            .and_then(|eq| {
                eq.map(|id| match inputs.law().exprs[id].kind {
                    ExprKind::Binary { lhs, .. } => inputs
                        .law()
                        .expr_type(lhs)
                        .cloned()
                        .ok_or_else(|| "元等式の型がない".into()),
                    _ => Err("元等式の出現が違う".into()),
                })
                .transpose()
            })
            .map_err(|cause| FiniteLawFamilyFailure {
                cause,
                partial: None,
            })?;
        columns.push(FiniteLawColumn {
            declaration: decl.clone(),
            source_instance: instance_indices.as_ref().map(|indices| indices[index]),
            equation_type,
            bindings: vec![],
            rows: vec![],
        });
        selection.push(Arc::new(Selection {
            law: law.clone(),
            bindings: bindings.clone(),
        }));
    }
    let mut result = FiniteLawFamilyValuations {
        object,
        column_objects,
        instance_mode: instance_indices.is_some(),
        sources: inputs.sources().clone(),
        selection,
        columns,
        owner: Arc::new(()),
        positions: vec![],
        types: vec![],
        domain: vec![],
        domain_complete: false,
        observed_point: None,
        state: FiniteLawState::Pending,
        required_zero: None,
    };
    match populate_family(inputs, &mut result, positions, c) {
        Ok(()) => Ok(result),
        Err(cause) => Err(FiniteLawFamilyFailure {
            cause,
            partial: Some(Box::new(result)),
        }),
    }
}
fn validate_bindings(
    e: &Environment<'_>,
    decl: &Declaration,
    supplied: &[(String, Scalar)],
) -> Result<Vec<(String, Scalar)>, ValidationFailure> {
    let Signature::Law { params, .. } = &decl.signature else {
        return Err("元Law署名がない".into());
    };
    let mut named = BTreeMap::new();
    for (name, value) in supplied {
        tick(&e.control)?;
        if named.insert(name.as_str(), value).is_some() {
            return Err("有限Lawの束縛名が重複する".into());
        }
    }
    if named.len() != params.len() {
        return Err("有限Lawの完全束縛と元署名の個数が違う".into());
    }
    let mut result = vec![];
    for p in params {
        tick(&e.control)?;
        let value = named
            .remove(p.name.as_str())
            .ok_or("有限Lawの元parameterが未束縛")?;
        if value.ty() != p.ty.erase() {
            return Err("有限Lawの束縛型が元parameterと違う".into());
        }
        data::check(value, e.inputs.law(), &e.control)?;
        validate_binding_value(e, decl, &p.ty, value)?;
        result.push((p.name.clone(), value.clone()));
    }
    if !named.is_empty() {
        return Err("有限Lawに未知の束縛がある".into());
    }
    Ok(result)
}
fn validate_binding_value(
    e: &Environment<'_>,
    decl: &Declaration,
    ty: &Type,
    value: &Scalar,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![(ty, value)];
    while let Some((ty, v)) = pending.pop() {
        tick(&e.control)?;
        match (ty, v) {
            (
                _,
                Scalar::Subject {
                    snapshot,
                    subject,
                    entity,
                },
            ) => {
                if e.subject(snapshot, subject)?.ty != *entity {
                    return Err("有限Lawの参照束縛が登録型と違う".into());
                }
            }
            (Type::Tuple(types), Scalar::Tuple(values)) => pending.extend(types.iter().zip(values)),
            (Type::List(ty), Scalar::List { items, .. })
            | (Type::Set(ty), Scalar::Set { items, .. }) => {
                pending.extend(items.iter().map(|v| (ty.as_ref(), v)));
            }
            (Type::Option(ty), Scalar::Option { value: Some(v), .. }) => {
                pending.push((ty.as_ref(), v))
            }
            (
                Type::Data(family),
                Scalar::Data {
                    constructor, args, ..
                },
            ) => {
                let ctor = data::constructor(e.inputs.law(), family, constructor, &e.control)?;
                pending.extend(ctor.arguments.iter().zip(args));
            }
            (Type::Map(from, to), Scalar::Map { pairs, .. }) => {
                if let Type::Ref(entity) = from.as_ref() {
                    let mut keys = vec![];
                    let mut expected = vec![];
                    for (key, _) in pairs {
                        tick(&e.control)?;
                        keys.push(key.clone());
                    }
                    for subject in e.subjects.values().filter(|s| s.ty == *entity) {
                        tick(&e.control)?;
                        expected.push(Scalar::Subject {
                            snapshot: subject.snapshot.clone(),
                            subject: subject.id.clone(),
                            entity: subject.ty.clone(),
                        });
                    }
                    let actual = data::set(from.erase(), &keys, &e.control)?;
                    let required = data::set(from.erase(), &expected, &e.control)?;
                    if !data::equal(&actual, &required, &e.control)? {
                        return Err("有限LawのMap束縛が元の登録始域を覆わない".into());
                    }
                }
                for (key, image) in pairs {
                    tick(&e.control)?;
                    pending.extend([(from.as_ref(), key), (to.as_ref(), image)]);
                }
            }
            (_, Scalar::Path(path)) => validate_binding_path(e, decl, path)?,
            (_, Scalar::Term(term)) => validate_binding_term(e, term)?,
            _ => {}
        }
    }
    Ok(())
}
fn validate_binding_term(
    e: &Environment<'_>,
    term: &crate::observed::term::Term,
) -> Result<(), ValidationFailure> {
    use crate::observed::control::CheckFailure;
    // 閉じた値は、選択Law以外のreadingや原始fieldからも来る。
    // 現在入力のscopeで本文を再検査し、保持した全実行情報と一致するものを要求する。
    let mut readings = BTreeSet::new();
    for d in e.inputs.law().declarations.values() {
        tick(&e.control)?;
        readings.insert(d.reading.clone());
    }
    let scopes = readings.into_iter().map(|n| (false, n)).chain(
        e.inputs
            .definitions()
            .vocabularies
            .keys()
            .cloned()
            .map(|n| (true, n)),
    );
    for (definition, name) in scopes {
        tick(&e.control)?;
        let checked = if definition {
            crate::law::check_definition_term_body_inner::<CheckFailure<Box<crate::issue::Issue>>>(
                e.inputs.definitions(),
                &name,
                &term.params,
                &term.returns,
                &term.body,
                &mut e.control.clone(),
            )
        } else {
            crate::law::check_reading_term_body::<CheckFailure<Box<crate::issue::Issue>>>(
                e.inputs.sources().law().bytes(),
                e.inputs.definitions(),
                &name,
                &term.params,
                &term.returns,
                &term.body,
                &mut e.control.clone(),
            )
        };
        let checked = match checked {
            Ok(v) => v,
            Err(CheckFailure::Stopped(s)) => return Err(ValidationFailure::Stop(s)),
            Err(CheckFailure::Input(_)) => continue,
        };
        let original = crate::archmap::value::TermValue {
            params: term.params.iter().map(|(n, _)| n.clone()).collect(),
            body: term.body.clone(),
            checked,
        };
        let args = term
            .params
            .iter()
            .map(|(_, t)| t.clone())
            .collect::<Vec<_>>();
        let reparsed =
            crate::observed::term::Term::from_input(&original, &args, &term.returns, &e.control)?;
        if term.same_input_program(&reparsed, &e.control)? {
            return Ok(());
        }
    }
    Err("有限LawのTerm束縛の本文・型・実行ASTが現在入力のscopeで一致しない".into())
}
fn validate_binding_path(
    e: &Environment<'_>,
    decl: &Declaration,
    path: &crate::observed::path_value::PathValue,
) -> Result<(), ValidationFailure> {
    let source = e.subject(&path.snapshot, &path.subject)?;
    if source.ty != path.entity {
        return Err("有限LawのPath束縛の端点型が違う".into());
    }
    if !e
        .inputs
        .law()
        .declarations
        .values()
        .any(|d| d.reading == path.reading)
    {
        return Err("有限LawのPath束縛の元readingがない".into());
    }
    let Some(step) = &path.step else {
        return Ok(());
    };
    let Signature::Law { body, .. } = &decl.signature else {
        return Err("元Lawがない".into());
    };
    let mut rebuilt = None;
    for generator in std::iter::once(&step.generator).chain(&step.word_tail) {
        tick(&e.control)?;
        let result = e.internal_path(*body, std::slice::from_ref(generator))?;
        if result.failure.is_some() {
            return Err("有限LawのPath束縛の生成作用が元入力で成立しない".into());
        }
        let Some(Scalar::Path(actual)) = &result.value else {
            return Err("有限LawのPath束縛の元作用が未確定".into());
        };
        rebuilt = Some(match rebuilt {
            None => (**actual).clone(),
            Some(left) => crate::observed::path_compose::compose_retained(
                &left,
                &actual,
                &path.reading,
                &e.control,
                |_, _| {},
            )
            .map_err(|f| f.cause)?
            .value
            .ok_or("有限LawのPath束縛の生成語が合成できない")?,
        });
    }
    let mut rebuilt = rebuilt.ok_or("有限LawのPath束縛に元生成語がない")?;
    rebuilt.reading = path.reading.clone();
    if !path.same_program(&rebuilt, &e.control)? {
        return Err("有限LawのPath束縛が元入力の生成語・作用と違う".into());
    }
    Ok(())
}
fn type_dependencies(
    e: &Environment<'_>,
    position: &Fact,
    ty: &Type,
    found: &mut BTreeSet<Fact>,
) -> Result<(), ValidationFailure> {
    let mut pending = vec![ty.clone()];
    let mut data_seen = BTreeSet::new();
    while let Some(ty) = pending.pop() {
        tick(&e.control)?;
        match &ty {
            Type::Owned(entity, name) => {
                let holder = e.subject(&position.snapshot, &position.subject)?;
                let field = e.field(
                    &holder.snapshot,
                    &holder.id,
                    &format!("{}.{}", holder.ty, name),
                )?;
                found.insert(Fact {
                    snapshot: holder.snapshot.clone(),
                    subject: holder.id.clone(),
                    field: Some(field.name.clone()),
                    atom: None,
                });
                for s in e.subjects.values().filter(|s| s.ty == *entity) {
                    tick(&e.control)?;
                    let field = e.field(&s.snapshot, &s.id, &format!("{}.owner", s.ty))?;
                    found.insert(Fact {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        field: Some(field.name.clone()),
                        atom: None,
                    });
                }
            }
            Type::Tuple(items) => pending.extend(items.iter().cloned()),
            Type::List(t) | Type::Set(t) | Type::Option(t) => pending.push((**t).clone()),
            Type::Map(a, b) => pending.extend([(**a).clone(), (**b).clone()]),
            Type::Data(family) if data_seen.insert(family.clone()) => {
                for ctor in data::constructors(e.inputs.law(), &family)? {
                    pending.extend(ctor.arguments.iter().cloned());
                }
            }
            _ => {}
        }
    }
    Ok(())
}
fn domains(
    e: &Environment<'_>,
    positions: &[Fact],
) -> Result<Option<(Vec<Type>, Vec<Vec<Scalar>>)>, ValidationFailure> {
    let mut types = vec![];
    let mut product = vec![vec![]];
    for position in positions {
        tick(&e.control)?;
        let field = e.field(
            &position.snapshot,
            &position.subject,
            position
                .field
                .as_deref()
                .ok_or("有限Law位置のfieldがない")?,
        )?;
        let domain = finite::field_candidates_if_finite(
            &field.ty.erase(),
            e.inputs.law(),
            &e.control,
            &mut |entity| {
                let mut out = finite::Enumeration::default();
                for s in e.subjects.values().filter(|s| s.ty == entity) {
                    tick(&e.control)?;
                    out.values.push(Scalar::Subject {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        entity: s.ty.clone(),
                    });
                    out.support.push(Fact {
                        snapshot: s.snapshot.clone(),
                        subject: s.id.clone(),
                        field: None,
                        atom: None,
                    });
                }
                Ok(out)
            },
        )?;
        let Some(domain) = domain else {
            return Ok(None);
        };
        types.push(field.ty.clone());
        let mut next = vec![];
        for row in &product {
            for value in &domain.enumeration.values {
                tick(&e.control)?;
                let mut candidate = row.clone();
                candidate.push(value.clone());
                next.push(candidate);
                tick(&e.control)?;
            }
        }
        product = next;
    }
    Ok(Some((types, product)))
}
fn components(
    e: &Environment<'_>,
    ty: &Type,
    left: &Option<Scalar>,
    right: &Option<Scalar>,
    guard: Option<bool>,
    blocked: bool,
) -> Result<Vec<FiniteLawComponent>, ValidationFailure> {
    let mut pending = vec![(vec![], ty.clone(), left.clone(), right.clone())];
    let mut result = vec![];
    while let Some((path, ty, left, right)) = pending.pop() {
        e.control
            .clone()
            .checkpoint(Checkpoint::FiniteLawComponent)?;
        for value in left.iter().chain(&right) {
            if value.ty() != ty.erase() {
                return Err("元等式の成分値と型が違う".into());
            }
        }
        if let Type::Tuple(items) = &ty {
            let project = |value: &Option<Scalar>,
                           index: usize|
             -> Result<Option<Scalar>, ValidationFailure> {
                match value {
                    None => Ok(None),
                    Some(Scalar::Tuple(values)) if values.len() == items.len() => {
                        Ok(Some(values[index].clone()))
                    }
                    _ => Err("元等式の積の成分数が違う".into()),
                }
            };
            for (index, item) in items.iter().enumerate().rev() {
                e.control
                    .clone()
                    .checkpoint(Checkpoint::FiniteLawComponent)?;
                let mut next = path.clone();
                next.push(index);
                pending.push((
                    next,
                    item.clone(),
                    project(&left, index)?,
                    project(&right, index)?,
                ));
            }
        } else {
            let equal = match (&left, &right) {
                (Some(a), Some(b)) => {
                    crate::observed::value_equality::equal(a, b, e.inputs.law(), &e.control)?
                }
                _ => None,
            };
            let indicator = if blocked {
                None
            } else {
                guard.zip(equal).map(|(g, p)| BigInt::from((g && !p) as u8))
            };
            result.push(FiniteLawComponent {
                path,
                ty,
                left,
                right,
                equal,
                indicator,
            });
        }
        e.control
            .clone()
            .checkpoint(Checkpoint::FiniteLawComponent)?;
    }
    Ok(result)
}
/// 元等式の出現を保ったまま、値を選ばないlexical wrapperだけをたどる。
pub(in crate::observed) fn equation(
    inputs: &CheckedInputs,
    mut id: usize,
    c: &mut Control,
) -> Result<Option<usize>, ValidationFailure> {
    loop {
        c.checkpoint(Checkpoint::FiniteLawOperand)?;
        match &inputs.law().exprs[id].kind {
            ExprKind::Group(child) | ExprKind::Let { body: child, .. } => id = *child,
            ExprKind::Match { scrutinee, arms } => {
                let child = crate::observed::object_law_residuals::binding_match_body(
                    inputs, *scrutinee, arms, c,
                )
                .map_err(|f| match f {
                    crate::construction::ConstructionFailure::Stopped(s) => {
                        ValidationFailure::Stop(s)
                    }
                    f => ValidationFailure::Internal(format!("元等式の束縛match: {f:?}")),
                })?;
                match child {
                    Some(child) => id = child,
                    None => return Ok(None),
                }
            }
            ExprKind::Binary { op: BinOp::Eq, .. } => return Ok(Some(id)),
            _ => return Ok(None),
        }
    }
}
fn operands(
    e: &Environment<'_>,
    body: usize,
    variables: &BTreeMap<String, SourceValue>,
    scope: &Scope,
    reading: &str,
) -> Result<Option<(Type, Option<Scalar>, Option<Scalar>)>, ValidationFailure> {
    let Some(eq) = equation(e.inputs, body, &mut e.control.clone())? else {
        return Ok(None);
    };
    let ExprKind::Binary { lhs, rhs, .. } = e.inputs.law().exprs[eq].kind else {
        return Err("元等式の出現が違う".into());
    };
    let ty = e
        .inputs
        .law()
        .expr_type(lhs)
        .ok_or("元等式の型がない")?
        .clone();
    let mut local = e.copy_variables(variables)?;
    let mut id = body;
    while id != eq {
        e.control.clone().checkpoint(Checkpoint::FiniteLawOperand)?;
        match &e.inputs.law().exprs[id].kind {
            ExprKind::Group(child) => id = *child,
            ExprKind::Let { name, value, body } => {
                let rhs = e.scoped_ast(*value, &local, scope, reading)?;
                if local.insert(name.name.clone(), rhs).is_some() {
                    return Err("元等式のlet名が重複する".into());
                }
                id = *body;
            }
            ExprKind::Match { scrutinee, arms } => {
                let input = e.scoped_ast(*scrutinee, &local, scope, reading)?;
                let Some(arm) =
                    data::select(e.inputs.law(), id, input.known_value.as_ref(), &e.control)?
                else {
                    return Ok(Some((ty, None, None)));
                };
                let input_value = input.known_value.as_ref().ok_or("元matchの値がない")?;
                for (name, value) in
                    data::bindings(e.inputs.law(), id, arm, input_value, &e.control)?
                {
                    let mut bound = source(value);
                    bound.scope = input.scope.clone();
                    bound.scalar_scope = Some(input.scope.clone());
                    bound.support = input.support.clone();
                    if local.insert(name, bound).is_some() {
                        return Err("元等式のpattern名が重複する".into());
                    }
                }
                id = arms[arm].body;
            }
            _ => return Err("元等式のlexical経路が違う".into()),
        }
    }
    let left = e.scoped_ast(lhs, &local, scope, reading)?;
    let right = e.scoped_ast(rhs, &local, scope, reading)?;
    Ok(Some((ty, left.known_value, right.known_value)))
}
struct Probe {
    row: FiniteLawRow,
    admissible: bool,
    blocked: bool,
}
fn probe(
    e: &Environment<'_>,
    decl: &Declaration,
    bindings: &[(String, Scalar)],
    point: usize,
) -> Result<Probe, ValidationFailure> {
    probe_mode(e, decl, bindings, point, false)
}
fn probe_mode(
    e: &Environment<'_>,
    decl: &Declaration,
    bindings: &[(String, Scalar)],
    point: usize,
    conditional: bool,
) -> Result<Probe, ValidationFailure> {
    let Signature::Law {
        params,
        guard,
        body,
        ..
    } = &decl.signature
    else {
        return Err("元Law署名がない".into());
    };
    let vars = bindings
        .iter()
        .map(|(n, v)| (n.clone(), source(v.clone())))
        .collect::<BTreeMap<_, _>>();
    let mut values = BTreeMap::new();
    let mut checks = owned_call::Checks::default();
    for (p, (_, v)) in params.iter().zip(bindings) {
        tick(&e.control)?;
        e.owned_call_value_check(
            &p.ty,
            &super::super::term::affine::Value::Known(v.clone()),
            &values,
            &decl.reading,
            decl.span,
            &mut checks,
        )?;
        values.insert(p.name.as_str(), Some(v));
    }
    let mut row = FiniteLawRow {
        point,
        application: if checks.failure.is_some() {
            Some(false)
        } else if checks.blocked {
            None
        } else {
            Some(true)
        },
        application_missing: checks.missing,
        guard: None,
        predicate: None,
        operands: None,
        components: None,
        indicator: None,
        condition_failed: false,
        condition_pending: false,
        support: checks.support,
        scope: checks.scope,
    };
    if checks.failure.is_some() || checks.blocked {
        return Ok(Probe {
            row,
            admissible: checks.failure.is_none(),
            blocked: checks.blocked,
        });
    }
    let mut scope = Scope::default();
    scope.readings.insert(decl.reading.clone());
    let g = match guard {
        Some(id) => Some(e.scoped_ast(*id, &vars, &scope, &decl.reading)?),
        None => None,
    };
    row.guard = match &g {
        None => Some(true),
        Some(g) => match &g.known_value {
            Some(Scalar::Bool(v)) => Some(*v),
            None => None,
            _ => return Err("元Law guardがBoolでない".into()),
        },
    };
    if conditional && row.guard == Some(false)
        && g.as_ref().is_none_or(|g| !g.condition_failed && !g.condition_pending)
    {
        if let Some(g) = g {
            row.support.extend(g.support);
            row.scope.merge(&g.scope);
        }
        object::instance::zero_indicator(e, decl, &mut row)?;
        return Ok(Probe {
            row,
            admissible: true,
            blocked: false,
        });
    }
    let b = e.scoped_ast(*body, &vars, &scope, &decl.reading)?;
    row.predicate = match &b.known_value {
        Some(Scalar::Bool(v)) => Some(*v),
        None => None,
        _ => return Err("元Law述語がBoolでない".into()),
    };
    row.operands = operands(e, *body, &vars, &scope, &decl.reading)?;
    if let Some((_, a, b)) = &row.operands {
        for value in a.iter().chain(b) {
            data::check(value, e.inputs.law(), &e.control)?;
        }
    }
    for v in g.iter().chain(std::iter::once(&b)) {
        row.support.extend(v.support.iter().cloned());
        row.scope.merge(&v.scope);
        row.condition_failed |= v.condition_failed;
        row.condition_pending |= v.condition_pending;
    }
    row.support.sort();
    row.support.dedup();
    if !row.condition_failed {
        if let (Some(g), Some(p)) = (row.guard, row.predicate) {
            row.indicator = Some(BigInt::from((g && !p) as u8));
        }
    }
    let b_body_pending = b.condition_pending;
    if let Some((ty, a, b)) = &row.operands {
        // lexical wrapperの所属が未決なら、等値な成分も確定residualにしない。
        let leaves = components(
            e,
            ty,
            a,
            b,
            row.guard,
            row.condition_failed || b_body_pending,
        )?;
        if let Some(whole) = &row.indicator {
            if leaves.iter().all(|p| p.indicator.is_some()) {
                let any = BigInt::from(
                    leaves
                        .iter()
                        .any(|p| p.indicator.as_ref() == Some(&BigInt::from(1)))
                        as u8,
                );
                if whole != &any {
                    return Err("元等式全体と成分の零性が違う".into());
                }
            }
        }
        row.components = Some(leaves);
    }
    Ok(Probe {
        row,
        admissible: true,
        blocked: false,
    })
}
fn populate_family(
    inputs: &CheckedInputs,
    r: &mut FiniteLawFamilyValuations,
    seed_positions: &[Fact],
    c: &mut Control,
) -> Result<(), ValidationFailure> {
    tick(c)?;
    let mut template = r.in_object(Environment::new(inputs, c)?);
    for index in 0..r.columns.len() {
        r.select_column_object(&mut template, index)?;
        let column = &mut r.columns[index];
        column.bindings = validate_bindings(
            &template, &column.declaration, &r.selection[index].bindings,
        )?;
    }
    // 原始fieldの型域は対象量化と独立。同じ全域を全列で共有する。
    template = r.in_object(template);
    if let Some(location) = r.object.iter()
        .chain(r.column_objects.iter().flat_map(|objects| objects.columns.iter()))
        .filter(|_| !r.instance_mode)
        .find_map(|object| object.pending_membership())
    {
        r.state = FiniteLawState::Undetermined {
            location,
            reason: "選択部分対象の所属が未観測".into(),
        };
        return Ok(());
    }
    let mut positions: BTreeSet<Fact> = seed_positions.iter().cloned().collect();
    loop {
        tick(c)?;
        loop {
            let mut expanded = positions.clone();
            for p in &positions {
                let f = template.field(
                    &p.snapshot,
                    &p.subject,
                    p.field.as_deref().ok_or("有限Law fieldがない")?,
                )?;
                type_dependencies(&template, p, &f.ty, &mut expanded)?;
            }
            if expanded == positions {
                break;
            }
            positions = expanded;
        }
        r.positions = positions.iter().cloned().collect();
        let Some((types, candidates)) = domains(&template, &r.positions)? else {
            // 個々の位置を再走査して、列挙できない元位置・型を保持する。
            for p in &r.positions {
                if domains(&template, std::slice::from_ref(p))?.is_none() {
                    let f = template.field(
                        &p.snapshot,
                        &p.subject,
                        p.field.as_deref().ok_or("finite fieldがない")?,
                    )?;
                    r.state = FiniteLawState::OutsideFinite {
                        position: p.clone(),
                        ty: f.ty.clone(),
                    };
                    return Ok(());
                }
            }
            return Err("有限Law域の非有限位置を特定できない".into());
        };
        let mut discovered = positions.clone();
        let mut admissible = vec![];
        let mut blocked = false;
        let mut failure = None;
        for candidate in candidates {
            tick(c)?;
            let values = r
                .positions
                .iter()
                .cloned()
                .zip(candidate.iter().cloned())
                .collect::<Vec<_>>();
            let mut e = r.in_object(Environment::primitive_dependency_probe(inputs, &values, c)?);
            *e.primitive_reads.borrow_mut() = Some(BTreeSet::new());
            let mut candidate_admissible = true;
            let mut candidate_blocked = false;
            let mut candidate_failure = None;
            for index in 0..r.columns.len() {
                tick(c)?;
                r.select_column_object(&mut e, index)?;
                match r.probe_column(&e, index, 0) {
                    Ok(p) => {
                        candidate_admissible &= p.admissible;
                        candidate_blocked |= p.blocked;
                    }
                    Err(ValidationFailure::Stop(stop)) => {
                        return Err(ValidationFailure::Stop(stop));
                    }
                    Err(f) => {
                        if candidate_failure.is_none() {
                            candidate_failure = Some(f);
                        }
                    }
                }
            }
            if let Some(reads) = e.primitive_reads.borrow().as_ref() {
                discovered.extend(reads.iter().cloned());
            }
            // 全Lawの読取りを先に集める。新位置を含むpassの判定は捨てる。
            if Environment::try_primitive_valuation(inputs, &values, c)?.is_none()
                || !candidate_admissible
            {
                continue;
            }
            blocked |= candidate_blocked;
            if let Some(f) = candidate_failure {
                if failure.is_none() {
                    failure = Some(f);
                }
            } else if !candidate_blocked {
                admissible.push(candidate);
            }
            tick(c)?;
        }
        if discovered != positions {
            positions = discovered;
            continue;
        }
        if let Some(failure) = failure {
            match failure {
                ValidationFailure::UnsupportedExpression { location, feature } => {
                    r.state = FiniteLawState::Unavailable { location, feature };
                    return Ok(());
                }
                f => return Err(f),
            }
        }
        if blocked {
            r.state = FiniteLawState::Undetermined {
                location: Location::Law {
                    span: r
                        .columns
                        .first()
                        .ok_or("空Law族の所属判定が未決")?
                        .declaration
                        .span,
                },
                reason: "元の完全束縛の所属条件が未決".into(),
            };
            return Ok(());
        }
        r.types = types;
        r.domain = admissible;
        r.domain_complete = true;
        tick(c)?;
        break;
    }
    let mut observed = vec![];
    let mut all_known = true;
    for p in &r.positions {
        tick(c)?;
        let f = template.field(
            &p.snapshot,
            &p.subject,
            p.field.as_deref().ok_or("元fieldがない")?,
        )?;
        match &f.slot {
            Slot::Known { value, .. } => observed
                .push(scalar_from(value, &f.ty, inputs.law(), c)?.ok_or("元原始値が読めない")?),
            Slot::Missing => all_known = false,
        }
    }
    if all_known {
        for (i, point) in r.domain.iter().enumerate() {
            tick(c)?;
            let mut equal = point.len() == observed.len();
            for (a, b) in point.iter().zip(&observed) {
                equal &= data::equal(a, b, c)?;
            }
            if equal {
                if r.observed_point.replace(i).is_some() {
                    return Err("元観測点が有限域で重複する".into());
                }
            }
        }
    }
    for (point, candidate) in r.domain.iter().enumerate() {
        c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        let values = r
            .positions
            .iter()
            .cloned()
            .zip(candidate.iter().cloned())
            .collect::<Vec<_>>();
        let mut e = r.in_object(Environment::with_primitive_valuation(inputs, &values, c)?);
        for index in 0..r.columns.len() {
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
            r.select_column_object(&mut e, index)?;
            let p = r.probe_column(&e, index, point)?;
            if !p.admissible || p.blocked {
                return Err("完成Dの元束縛条件が変わった".into());
            }
            r.columns[index].rows.push(p.row);
            c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
        }
    }
    c.checkpoint(Checkpoint::FiniteLawEvaluation)?;
    r.state = if r
        .columns
        .iter()
        .any(|q| q.rows.iter().any(|p| p.condition_failed))
    {
        FiniteLawState::ConditionFailed
    } else if let Some(q) = r.columns.iter().find(|q| {
        q.rows.iter().any(|row| {
            row.components.as_ref().is_some_and(|cs| {
                cs.iter()
                    .any(|p| p.left.is_some() && p.right.is_some() && p.equal.is_none())
            })
        })
    }) {
        FiniteLawState::Unavailable {
            location: Location::Law {
                span: q.declaration.span,
            },
            feature: "元等式の成分外延比較に必要な算法".into(),
        }
    } else if let Some(q) = r.columns.iter().find(|q| {
        q.rows.iter().any(|p| {
            p.indicator.is_none()
                || p.components
                    .as_ref()
                    .is_some_and(|cs| cs.iter().any(|p| p.indicator.is_none()))
        })
    }) {
        FiniteLawState::Undetermined {
            location: Location::Law {
                span: q.declaration.span,
            },
            reason: "元guardまたは述語の値が未決".into(),
        }
    } else {
        FiniteLawState::Ready
    };
    // 参照域の所属未決で読取り位置を尽くせないとき、既知の候補列を全Dとしない。
    if r.object.iter()
        .chain(r.column_objects.iter().flat_map(|objects| objects.columns.iter()))
        .any(|object| object.has_reference_conditions())
        && r.columns.iter().any(|column| {
            column.rows.iter().any(|row| row.scope.completions && row.indicator.is_none())
        })
    {
        r.domain_complete = false;
    }
    if r.is_complete() {
        r.state = FiniteLawState::Pending;
        let mut zero = vec![];
        for point in 0..r.domain.len() {
            c.checkpoint(Checkpoint::FiniteLawRequired)?;
            let mut holds = true;
            for q in &r.columns {
                c.checkpoint(Checkpoint::FiniteLawRequired)?;
                if q.required() {
                    let row = &q.rows[point];
                    holds &= match &row.components {
                        Some(cs) => cs
                            .iter()
                            .all(|p| p.indicator.as_ref() == Some(&BigInt::from(0))),
                        None => row.indicator.as_ref() == Some(&BigInt::from(0)),
                    };
                }
            }
            if holds {
                zero.push(point);
            }
        }
        c.checkpoint(Checkpoint::FiniteLawRequired)?;
        r.required_zero = Some(zero);
        r.state = FiniteLawState::Ready;
    }
    Ok(())
}

#[cfg(test)]
#[path = "finite_law_valuations_tests.rs"]
mod tests;

#[path = "finite_law_quotient.rs"]
pub(in crate::observed) mod quotient;

#[cfg(test)]
#[path = "finite_law_lexical_tests.rs"]
mod lexical_tests;

#[path = "finite_object_law.rs"]
pub(in crate::observed) mod object;
