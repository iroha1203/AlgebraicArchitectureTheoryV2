use archsig::{
    construction::{
        ConstructionFailure, construct,
        readings::{InstanceApplication, ObjectReadingInstances, object_reading_instances},
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
    types::Type,
};
use std::{cell::Cell, rc::Rc};
const D: &[u8] = include_bytes!("fixtures/object-instances.atoms.json");
const L: &str = include_str!("fixtures/object-instances.law");
const A: &str = include_str!("fixtures/object-instances.archmap.json");
fn inputs(law: &str, a: &str) -> CheckedInputs {
    let d = archsig::definition::check_definitions(&[("definition0", D)]).unwrap();
    let digest = &d.vocabularies["Instances"].digest;
    check_inputs(
        InputSources::from_bytes(
            vec![D.to_vec()],
            law.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
            a.replace("@INSTANCES_DIGEST@", digest).into_bytes(),
        ),
        &mut Control::unlimited(),
    )
    .unwrap_or_else(|f| panic!("{:?}", f.issues()))
}
fn instances(i: &CheckedInputs) -> ObjectReadingInstances {
    let c = construct(i, "Selected", "v", "A", &mut Control::unlimited()).unwrap();
    object_reading_instances(i, &c, &mut Control::unlimited()).unwrap()
}
fn rows<'a>(
    r: &'a ObjectReadingInstances,
    name: &str,
) -> Vec<&'a archsig::construction::readings::ObjectInstance> {
    r.instances()
        .iter()
        .filter(|i| i.declaration().name == format!("Selected.{name}"))
        .collect()
}
fn bindings(r: &archsig::construction::readings::ObjectInstance) -> Vec<(&str, &str, &str)> {
    r.bindings()
        .iter()
        .map(|b| {
            (
                b.parameter().name.as_str(),
                b.subject().snapshot.as_str(),
                b.subject().subject.as_str(),
            )
        })
        .collect()
}
#[test]
fn root_owned_and_external_bindings_match_independent_object_domains() {
    let r = instances(&inputs(L, A));
    assert_eq!(
        r.objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["A", "p", "r"]
    );
    assert!(r.objects().iter().all(|o| o.conditions().is_empty()));
    assert_eq!(
        rows(&r, "amount")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [vec![("c", "v", "p")], vec![("c", "v", "r")]]
    );
    assert_eq!(
        rows(&r, "root")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [vec![("a", "v", "A")]]
    );
    assert_eq!(
        rows(&r, "link")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [vec![("e", "v", "e")]]
    );
    assert_eq!(
        rows(&r, "paired")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [
            vec![("c", "v", "p"), ("x", "v", "x")],
            vec![("c", "v", "p"), ("x", "v", "y")],
            vec![("c", "v", "r"), ("x", "v", "x")],
            vec![("c", "v", "r"), ("x", "v", "y")]
        ]
    );
    let yes = InstanceApplication::Applicable { conditions: vec![] };
    let no = InstanceApplication::NotApplicable;
    assert_eq!(
        rows(&r, "amount")[0].applications(),
        [yes.clone(), yes.clone(), no.clone()]
    );
    assert_eq!(
        rows(&r, "amount")[1].applications(),
        [yes.clone(), no.clone(), yes.clone()]
    );
    assert_eq!(
        rows(&r, "root")[0].applications(),
        [yes.clone(), no.clone(), no.clone()]
    );
    assert_eq!(rows(&r, "link")[0].applications(), [yes, no.clone(), no]);
    assert_eq!(
        rows(&r, "owner")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [
            vec![("a", "v", "A"), ("c", "v", "p")],
            vec![("a", "v", "A"), ("c", "v", "r")]
        ]
    );
    assert!(rows(&r, "outside").is_empty());
    assert!(
        r.instances()
            .iter()
            .all(|i| i.declaration().name.starts_with("Selected."))
    );
    assert_eq!(r.declarations().len(), 10);
    assert_eq!(r.instances().len(), 17);
}
fn remove_atom(a: &str, id: &str) -> String {
    let marker = format!("\"id\":\"{id}\"");
    assert_eq!(a.lines().filter(|l| l.contains(&marker)).count(), 1);
    a.lines()
        .filter(|l| !l.contains(&marker))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n]", "\n]")
}
fn append_snapshot(a: &str, snapshot: &str) -> String {
    let prefix = a.strip_suffix("}]\n}\n").unwrap();
    format!("{prefix}}},{snapshot}]\n}}\n")
}
#[test]
fn all_value_parameter_domains_and_original_metadata_remain_symbolic() {
    let i = inputs(L, A);
    let r = instances(&i);
    let value_rows = rows(&r, "values");
    assert_eq!(value_rows.len(), 1);
    let value = value_rows[0];
    assert_eq!(bindings(value), [("a", "v", "A")]);
    assert_eq!(
        value
            .parameters()
            .iter()
            .map(|p| (p.name.as_str(), p.ty.clone()))
            .collect::<Vec<_>>(),
        [
            ("n", Type::Z),
            ("b", Type::Bool),
            ("xs", Type::List(Box::new(Type::Z))),
            ("f", Type::Term(vec![Type::Z], Box::new(Type::Z))),
            (
                "p",
                Type::Path("Instances.Part".into(), "Instances.Part".into())
            ),
            (
                "members",
                Type::Set(Box::new(Type::Owned("Instances.Part".into(), "a".into())))
            ),
        ]
    );
    for param in value.parameters() {
        assert_eq!(
            &i.sources().law().bytes()[param.span.0..param.span.1],
            param.name.as_bytes()
        );
    }
    let bounded = rows(&r, "bounded")[0];
    assert_eq!(
        bounded.declaration().role,
        Some(archsig::law::ast::Role::Required)
    );
    assert_eq!(bounded.parameters().len(), 1);
    assert_eq!(bounded.parameters()[0].ty, Type::Z);
    assert_eq!(bounded.parameters()[0].name, "delta");
    assert_eq!(bounded.declaration().expressions.len(), 2);
    let root = rows(&r, "root")[0];
    assert!(
        root.declaration()
            .dependencies
            .iter()
            .any(|d| d == "Helper.external")
    );
    assert!(
        root.declaration()
            .references
            .iter()
            .any(|(_, d)| d == "Helper.external")
    );
    assert!(rows(&r, "outside").is_empty());
    assert!(
        r.declarations()
            .iter()
            .any(|d| d.name == "Selected.outside")
    );
    assert!(
        !r.declarations()
            .iter()
            .any(|d| d.name.starts_with("Helper.") || d.name.starts_with("Other."))
    );
    for instance in r.instances() {
        assert_eq!(
            instance.declaration(),
            i.law()
                .infos
                .iter()
                .find(|info| info.name == instance.declaration().name)
                .unwrap()
        );
    }
    r.recheck(&i, &mut Control::unlimited()).unwrap();
}
#[test]
fn missing_quantity_keeps_existing_instances_and_applicability() {
    let r = instances(&inputs(L, A));
    let missing = instances(&inputs(L, &remove_atom(A, "p-quantity")));
    assert_eq!(r.instances(), missing.instances());
    assert_eq!(r.objects(), missing.objects());
    assert_eq!(rows(&missing, "amount").len(), 2);
    assert!(
        missing
            .construction()
            .base()
            .known()
            .requirements()
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Instances.Part.quantity"))
    );
    assert!(
        !missing
            .construction()
            .base()
            .known()
            .family()
            .iter()
            .any(|f| f.subject == "p" && f.field.as_deref() == Some("Instances.Part.quantity"))
    );
}
#[test]
fn unknown_owner_retains_conditional_objects_and_reuses_the_same_slot_condition() {
    let r = instances(&inputs(L, &remove_atom(A, "q-owner")));
    assert_eq!(
        r.objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["A", "p", "q", "r"]
    );
    let object = &r.objects()[2];
    assert_eq!(object.conditions().len(), 1);
    let condition = &object.conditions()[0];
    assert_eq!(condition.slot().subject, "q");
    assert_eq!(
        condition.slot().field.as_deref(),
        Some("Instances.Part.owner")
    );
    assert_eq!(condition.slot().atom, None);
    assert_eq!(condition.owner(), r.construction().root());
    let q = rows(&r, "amount")
        .into_iter()
        .find(|i| bindings(i) == [("c", "v", "q")])
        .unwrap();
    assert_eq!(
        q.applications(),
        [
            InstanceApplication::Applicable {
                conditions: vec![condition.clone()]
            },
            InstanceApplication::NotApplicable,
            InstanceApplication::Applicable {
                conditions: vec![condition.clone()]
            },
            InstanceApplication::NotApplicable,
        ]
    );
    let owned = rows(&r, "owner")
        .into_iter()
        .find(|i| i.bindings().last().unwrap().subject().subject == "q")
        .unwrap();
    assert_eq!(
        owned.applications()[0],
        InstanceApplication::Applicable {
            conditions: vec![condition.clone()]
        }
    );
    assert!(
        owned.applications()[1..]
            .iter()
            .all(|a| matches!(a, InstanceApplication::NotApplicable))
    );
    assert_eq!(rows(&r, "bounded").len(), 3);
    let changed = inputs(L, A);
    assert!(matches!(
        r.recheck(&changed, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
}
#[test]
fn shared_external_unknown_owner_never_gets_two_conflicting_values() {
    let r = instances(&inputs(L, A));
    let shared = rows(&r, "sharing");
    assert_eq!(
        shared.iter().map(|i| bindings(i)).collect::<Vec<_>>(),
        [
            vec![
                ("a", "v", "A"),
                ("g", "v", "g"),
                ("h", "v", "g"),
                ("c", "v", "u"),
                ("d", "v", "u")
            ],
            vec![
                ("a", "v", "A"),
                ("g", "v", "h"),
                ("h", "v", "h"),
                ("c", "v", "u"),
                ("d", "v", "u")
            ],
        ]
    );
    for (i, owner) in shared.iter().zip(["g", "h"]) {
        let InstanceApplication::Applicable { conditions } = &i.applications()[0] else {
            panic!("base applies")
        };
        assert_eq!(conditions.len(), 1);
        assert_eq!(conditions[0].slot().subject, "u");
        assert_eq!(
            conditions[0].slot().field.as_deref(),
            Some("Instances.Member.owner")
        );
        assert_eq!(conditions[0].owner().subject, owner);
    }
    let known = A.replace("\"atoms\":[\n", "\"atoms\":[\n{\"id\":\"u-owner\",\"subject\":\"u\",\"field\":\"Instances.Member.owner\",\"value\":[\"v\",\"g\"],\"origin\":\"model\"},\n");
    let known = instances(&inputs(L, &known));
    let shared = rows(&known, "sharing");
    assert_eq!(shared.len(), 1);
    assert_eq!(
        bindings(shared[0]),
        [
            ("a", "v", "A"),
            ("g", "v", "g"),
            ("h", "v", "g"),
            ("c", "v", "u"),
            ("d", "v", "u")
        ]
    );
    assert_eq!(
        shared[0].applications()[0],
        InstanceApplication::Applicable { conditions: vec![] }
    );
}
#[test]
fn other_roots_and_snapshots_stay_outside_local_binders_but_external_refs_are_fixed() {
    let a = append_snapshot(
        A,
        r#"{"id":"w","origin":"model","subjects":[{"id":"A","type":"Instances.Root","origin":"model"},{"id":"p","type":"Instances.Part","origin":"model"},{"id":"x","type":"Instances.External","origin":"model"}],"atoms":[{"id":"w-owner","subject":"p","field":"Instances.Part.owner","value":["w","A"],"origin":"model"}]}"#,
    );
    let r = instances(&inputs(L, &a));
    assert_eq!(
        rows(&r, "root")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [vec![("a", "v", "A")]]
    );
    assert_eq!(
        rows(&r, "amount")
            .iter()
            .map(|i| bindings(i))
            .collect::<Vec<_>>(),
        [vec![("c", "v", "p")], vec![("c", "v", "r")]]
    );
    let paired = rows(&r, "paired");
    assert_eq!(paired.len(), 6);
    assert_eq!(bindings(paired[2]), [("c", "v", "p"), ("x", "w", "x")]);
    assert_eq!(bindings(paired[5]), [("c", "v", "r"), ("x", "w", "x")]);
    assert_eq!(r.objects().len(), 3);
    assert!(
        r.construction()
            .base()
            .known()
            .family()
            .iter()
            .any(|f| f.subject == "x" && f.snapshot == "v" && f.field.is_none())
    );
    assert!(
        !r.construction()
            .local_domain()
            .known()
            .iter()
            .any(|f| f.subject == "x")
    );
}
#[test]
fn plain_cross_snapshot_membership_does_not_erase_owned_same_snapshot_requirement() {
    let a = append_snapshot(
        A,
        r#"{"id":"w","origin":"model","subjects":[{"id":"t","type":"Instances.Part","origin":"model"}],"atoms":[{"id":"t-owner","subject":"t","field":"Instances.Part.owner","value":["v","A"],"origin":"model"}]}"#,
    );
    let r = instances(&inputs(L, &a));
    assert_eq!(rows(&r, "amount").len(), 3);
    assert_eq!(bindings(rows(&r, "amount")[2]), [("c", "w", "t")]);
    assert_eq!(rows(&r, "owner").len(), 2);
    assert_eq!(rows(&r, "owned").len(), 2);
    assert_eq!(
        r.objects().last().unwrap().identity().subject().snapshot,
        "w"
    );
}
#[test]
fn fixed_instance_stops_latch_without_further_primitive_probes() {
    let i = inputs(L, A);
    let r = instances(&i);
    let c = r.construction();
    let count = Rc::new(Cell::new(0usize));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::ObjectInstances {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    object_reading_instances(&i, c, &mut control).unwrap();
    let total = count.get();
    assert!(total > 100);
    for at in [1, total / 2, total] {
        for mode in 0..4 {
            let count = Rc::new(Cell::new(0usize));
            let seen = count.clone();
            let mut control = Control::new(
                Limits {
                    time_ms: (mode == 0).then_some(1),
                    memory_mib: (mode == 1).then_some(1),
                },
                move |p| {
                    if p == Checkpoint::ObjectInstances {
                        seen.set(seen.get() + 1);
                    }
                    let stop = seen.get() >= at;
                    Usage {
                        elapsed_ms: if stop && mode == 0 { 1 } else { 0 },
                        memory_mib: if stop && mode == 1 { 1 } else { 0 },
                        signal: if stop {
                            match mode {
                                2 => Some(Signal::Int),
                                3 => Some(Signal::Term),
                                _ => None,
                            }
                        } else {
                            None
                        },
                    }
                },
            );
            let failure = object_reading_instances(&i, c, &mut control).unwrap_err();
            assert_eq!(
                failure,
                ConstructionFailure::Stopped(control.stop_reason().unwrap())
            );
            assert_eq!(count.get(), at);
            assert_eq!(r.recheck(&i, &mut control).unwrap_err(), failure);
            assert_eq!(count.get(), at);
        }
    }
}
#[test]
fn conditional_arrow_stays_in_base_domain_without_adding_an_object() {
    let r = instances(&inputs(L, &remove_atom(A, "e-owner")));
    assert_eq!(
        r.objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["A", "p", "r"]
    );
    let arrow = rows(&r, "link");
    assert_eq!(arrow.len(), 1);
    assert_eq!(bindings(arrow[0]), [("e", "v", "e")]);
    let InstanceApplication::Applicable { conditions } = &arrow[0].applications()[0] else {
        panic!("conditional arrow")
    };
    assert_eq!(conditions.len(), 1);
    assert_eq!(
        conditions[0].slot().field.as_deref(),
        Some("Instances.Link.owner")
    );
    assert_eq!(conditions[0].owner(), r.construction().root());
    assert!(
        arrow[0].applications()[1..]
            .iter()
            .all(|a| matches!(a, InstanceApplication::NotApplicable))
    );
}
#[test]
fn empty_owned_domain_keeps_root_instances_and_distinguishes_other_selected_roots() {
    let i = inputs(L, A);
    let c = construct(&i, "Selected", "v", "B", &mut Control::unlimited()).unwrap();
    let r = object_reading_instances(&i, &c, &mut Control::unlimited()).unwrap();
    assert_eq!(
        r.objects()
            .iter()
            .map(|o| o.identity().subject().subject.as_str())
            .collect::<Vec<_>>(),
        ["B", "q"]
    );
    assert_eq!(bindings(rows(&r, "amount")[0]), [("c", "v", "q")]);
    assert_eq!(bindings(rows(&r, "root")[0]), [("a", "v", "B")]);
    assert!(rows(&r, "link").is_empty());
    let a = A.replace(
        "\"subjects\":[\n",
        "\"subjects\":[\n{\"id\":\"C\",\"type\":\"Instances.Root\",\"origin\":\"model\"},\n",
    );
    let i = inputs(L, &a);
    let c = construct(&i, "Selected", "v", "C", &mut Control::unlimited()).unwrap();
    let r = object_reading_instances(&i, &c, &mut Control::unlimited()).unwrap();
    assert_eq!(r.objects().len(), 1);
    assert_eq!(bindings(rows(&r, "root")[0]), [("a", "v", "C")]);
    assert_eq!(rows(&r, "values").len(), 1);
    assert!(rows(&r, "amount").is_empty());
    assert!(rows(&r, "bounded").is_empty());
    assert!(rows(&r, "owner").is_empty());
    assert!(
        r.declarations()
            .iter()
            .any(|d| d.name == "Selected.bounded")
    );
}
#[test]
fn current_metadata_is_rechecked_while_quantity_changes_do_not_claim_value_equality() {
    let i = inputs(L, A);
    let r = instances(&i);
    let changed_law = inputs(
        &L.replace("law required bounded", "law optional bounded"),
        A,
    );
    r.construction()
        .recheck(
            &changed_law,
            "Selected",
            "v",
            "A",
            &mut Control::unlimited(),
        )
        .unwrap();
    assert!(matches!(
        r.recheck(&changed_law, &mut Control::unlimited()),
        Err(ConstructionFailure::Inconsistent(_))
    ));
    let changed_values = inputs(L, &A.replace("\"value\":\"2\"", "\"value\":\"17\""));
    r.recheck(&changed_values, &mut Control::unlimited())
        .unwrap();
    // この計画の署名・参照束縛・適用条件は数量値から独立している。
    assert_eq!(instances(&changed_values), r);
}
#[test]
fn primitive_array_order_keeps_object_and_instance_identity_order() {
    fn reverse(a: &str, key: &str) -> String {
        let marker = format!("\"{key}\":[\n");
        let start = a.find(&marker).unwrap() + marker.len();
        let end = start + a[start..].find("\n]").unwrap();
        let mut rows: Vec<_> = a[start..end]
            .lines()
            .map(|l| l.trim_end_matches(','))
            .collect();
        rows.reverse();
        format!("{}{}{}", &a[..start], rows.join(",\n"), &a[end..])
    }
    let a = remove_atom(A, "q-owner");
    let r = instances(&inputs(L, &a));
    let reversed = reverse(&reverse(&a, "subjects"), "atoms");
    assert_ne!(a, reversed);
    assert_eq!(r, instances(&inputs(L, &reversed)));
}
#[test]
fn original_body_guard_and_helper_bytes_cannot_be_reattributed_by_equal_metadata() {
    let original = inputs(L, A);
    let r = instances(&original);
    assert_eq!(r.source_law(), original.sources().law());
    for (from, to) in [
        ("c.quantity + delta >= 0", "c.quantity + delta <= 0"),
        ("when delta >= 0", "when delta <= 0"),
        ("= x.quantity;", "= -123456789;"),
    ] {
        assert_eq!(from.len(), to.len());
        let changed = L.replacen(from, to, 1);
        assert_ne!(changed, L);
        let changed = inputs(&changed, A);
        let fresh = instances(&changed);
        assert_eq!(
            r.instances(),
            fresh.instances(),
            "the original failure needs equal metadata/positions"
        );
        assert_eq!(r.objects(), fresh.objects());
        assert_ne!(r.source_law(), fresh.source_law());
        assert_ne!(r, fresh);
        r.construction()
            .recheck(&changed, "Selected", "v", "A", &mut Control::unlimited())
            .unwrap();
        assert!(
            matches!(
                r.recheck(&changed, &mut Control::unlimited()),
                Err(ConstructionFailure::Inconsistent(_))
            ),
            "source change {from}"
        );
        fresh.recheck(&changed, &mut Control::unlimited()).unwrap();
        assert_eq!(r.source_law(), original.sources().law());
    }
}
