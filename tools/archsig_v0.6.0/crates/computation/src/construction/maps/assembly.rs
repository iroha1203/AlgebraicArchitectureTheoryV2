//! 局所モデルの組立てが生成した個体対応を、通常のConfiguration写像へ延長する。
use super::*;
use std::sync::Arc;

/// 元構成と個体対応に閉じた導出。完成した作用表を外部入力として受け取らない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssemblyMap {
    pub(super) source: Arc<ConfigurationConstruction>,
    pub(super) target: Arc<ConfigurationConstruction>,
    subjects: BTreeMap<FactPointer, FactPointer>,
}
pub(crate) fn assembled_map(
    inputs: &CheckedInputs,
    source: Arc<ConfigurationConstruction>,
    target: Arc<ConfigurationConstruction>,
    subjects: BTreeMap<FactPointer, FactPointer>,
    control: &Control,
) -> Result<Option<ConfigurationMap>, ConstructionFailure> {
    compute_checked(
        inputs,
        &Arc::new(AssemblyMap {
            source,
            target,
            subjects,
        }),
        control,
    )
}
pub(super) fn recompute(
    inputs: &CheckedInputs,
    recipe: &Arc<AssemblyMap>,
    control: &Control,
) -> Result<Option<ConfigurationMap>, ConstructionFailure> {
    check(control)?;
    for construction in [&recipe.source, &recipe.target] {
        construction.recheck(
            inputs,
            construction.reading(),
            &construction.root().snapshot,
            &construction.root().subject,
            control,
        )?;
    }
    compute_checked(inputs, recipe, control)
}
// Both endpoints were constructed against this immutable input in the caller.
fn compute_checked(
    inputs: &CheckedInputs,
    recipe: &Arc<AssemblyMap>,
    control: &Control,
) -> Result<Option<ConfigurationMap>, ConstructionFailure> {
    check(control)?;
    let source = &recipe.source;
    let target = &recipe.target;
    let (Some(sc), Some(tc)) = (source.base().configuration(), target.base().configuration())
    else {
        return Ok(None);
    };
    if source.universe() != target.universe() || source.reading() != target.reading() {
        return Ok(None);
    }
    let family: BTreeSet<_> = sc.family().iter().collect();
    let mut images = Vec::new();
    let mut action = BTreeMap::new();
    let mut left = BTreeMap::new();
    let mut right = BTreeMap::new();
    for (a, b) in &recipe.subjects {
        check(control)?;
        left.insert(
            (a.snapshot.clone(), a.subject.clone()),
            (b.snapshot.clone(), b.subject.clone()),
        );
    }
    if let Some(transport) = source.transport() {
        for (a, b) in transport {
            check(control)?;
            let b = recipe.subjects.get(b).unwrap_or(b);
            left.insert(
                (a.snapshot.clone(), a.subject.clone()),
                (b.snapshot.clone(), b.subject.clone()),
            );
        }
    }
    if let Some(transport) = target.transport() {
        for (a, b) in transport {
            check(control)?;
            right.insert(
                (a.snapshot.clone(), a.subject.clone()),
                (b.snapshot.clone(), b.subject.clone()),
            );
        }
    }
    for fact in source.universe() {
        check(control)?;
        let image = if !family.contains(fact) {
            target.root().clone()
        } else {
            let original = FactPointer::from(archsig_input::archmap::FactData {
                snapshot: fact.snapshot.clone(),
                subject: fact.subject.clone(),
                field: None,
                atom: None,
            });
            let Some(to) = recipe.subjects.get(&original) else {
                return Ok(None);
            };
            let a = subject(inputs, &original.snapshot, &original.subject, control)?;
            let b = subject(inputs, &to.snapshot, &to.subject, control)?;
            if a.ty != b.ty {
                return Ok(None);
            }
            if let Some(name) = &fact.field {
                let Some(af) = field(a, name, control)? else {
                    return Ok(None);
                };
                let Some(bf) = field(b, name, control)? else {
                    return Ok(None);
                };
                let (
                    Slot::Known { value: av, .. },
                    Slot::Known {
                        atom, value: bv, ..
                    },
                ) = (&af.slot, &bf.slot)
                else {
                    return Ok(None);
                };
                if reference_shape(av, &left, control)? != reference_shape(bv, &right, control)? {
                    return Ok(None);
                }
                let mut image = slot(b, &bf.name);
                image.atom = Some(atom.clone());
                image
            } else {
                exists(b)
            }
        };
        action.insert(fact.clone(), image.clone());
        images.push(image);
    }
    if !preservation_counterexamples(sc, tc, true, &action, control)?.is_empty() {
        return Ok(None);
    }
    let candidate = MapCandidate {
        origin: MapOrigin::Assembly(recipe.clone()),
        source_root: source.root().clone(),
        target_root: target.root().clone(),
        reading: source.reading().into(),
        to_reading: target.reading().into(),
        source_configuration: sc.clone(),
        target_configuration: tc.clone(),
        universe: source.shared_universe(),
        images,
    };
    check(control)?;
    Ok(Some(ConfigurationMap { candidate }))
}
