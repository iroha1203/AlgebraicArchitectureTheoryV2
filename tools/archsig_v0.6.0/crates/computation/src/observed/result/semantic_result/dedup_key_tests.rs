use super::*;
use crate::observed::{
    construction_result::ConstructionType as T,
    result::{Rule, Scope},
};
use archsig_common::types::Type;
use std::{cell::Cell, rc::Rc};

// Frozen previous canonical-String loop; enclosing arguments/return and the
// test module's ConstructionType alias differ.
fn legacy_share(
    projected: BTreeMap<usize, Json>,
    native: &[Node],
    ids: &mut BTreeMap<String, String>,
    control: &Control,
    point: Checkpoint,
) -> Result<Vec<Json>, Signal> {
    let mut values = BTreeMap::<String, String>::new();
    let mut nodes = Vec::new();
    // 到達順でなく元の数値 index 順が canonical 共有の代表と番号を決める。
    for (index, mut node) in projected {
        control.checkpoint(point)?;
        let old_id = format!("n{index}");
        rename(&mut node, ids, control, point)?;
        // 環・基底・関係を含む表示全体の一致だけを共有する。同型は推測しない。
        let shared = matches!(
            native[index].ty,
            NodeType::Value(_)
                | NodeType::Vector(_)
                | NodeType::ModuleMap(_, _)
                | NodeType::Domain
                | NodeType::Construction(T::StateMap | T::Ring | T::Module)
        );
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.remove("id");
        let key = shared.then(|| node.canonical());
        if let Some(existing) = key.as_ref().and_then(|key| values.get(key)) {
            ids.insert(old_id, existing.clone());
            continue;
        }
        let Json::Obj(fields) = &mut node else {
            unreachable!()
        };
        fields.insert("id".into(), Json::str(&old_id));
        if let Some(key) = key {
            values.insert(key, old_id.clone());
        }
        nodes.push(node);
    }
    Ok(nodes)
}

fn record(index: usize, value: Json) -> Json {
    Json::obj([
        ("id", Json::str(format!("n{index}"))),
        ("type", Json::str("fixture")),
        ("state", Json::str("value")),
        ("value", value),
    ])
}
fn fixture_node(ty: NodeType) -> Node {
    // This fixture tests the saved sharing layer, not kernel admissibility.
    Node {
        ty,
        payload: None,
        rule: Rule::Construction("fixture"),
        arguments: vec![],
        support: vec![].into(),
        scope: Scope::default(),
        reasons: vec![],
        evidence: vec![],
        judgment: None,
    }
}
fn ids(projected: &BTreeMap<usize, Json>) -> BTreeMap<String, String> {
    projected
        .keys()
        .map(|n| {
            let id = format!("n{n}");
            (id.clone(), id)
        })
        .collect()
}
fn without_id(mut value: Json) -> Json {
    let Json::Obj(fields) = &mut value else {
        panic!()
    };
    fields.remove("id");
    value
}
fn plain(indices: &[usize]) -> Json {
    Json::Arr(indices.iter().map(|n| NodeRef(*n).wire()).collect())
}

#[test]
fn fingerprint_follows_canonical_bytes_independently_of_chunks_and_compact_refs() {
    for value in [
        Json::NodeReferences(vec![]),
        Json::NodeReferences(vec![2, 10, 2]),
        Json::str("é日本語😀\"\\\n\u{0001}".repeat(300)),
        Json::obj([("z", Json::Nat(u64::MAX)), ("a", Json::Bool(false))]),
    ] {
        let bytes = value.canonical().into_bytes();
        let expected = canonical_fingerprint(&value);
        for width in [1, 2, 7, 256, bytes.len().max(1)] {
            let mut writer = FingerprintWriter(DefaultHasher::new());
            for chunk in bytes.chunks(width) {
                writer.write_all(chunk).unwrap();
            }
            assert_eq!(writer.0.finish(), expected);
        }
    }
    for indices in [vec![], vec![2, 10, 2]] {
        let compact = Json::NodeReferences(indices.clone());
        let expanded = plain(&indices);
        assert_eq!(compact, expanded);
        assert_eq!(compact.canonical(), expanded.canonical());
        assert_eq!(
            canonical_fingerprint(&compact),
            canonical_fingerprint(&expanded)
        );
    }
}

#[test]
fn forced_collisions_require_full_records_and_ignore_only_root_id() {
    let nodes = vec![
        record(0, Json::obj([("id", Json::str("nested-A"))])),
        record(1, Json::obj([("id", Json::str("nested-B"))])),
        record(2, Json::NodeReferences(vec![4, 2, 4])),
        record(3, Json::Bool(true)),
        record(4, Json::NodeReferences(vec![4])),
    ];
    // A single artificial fingerprint bucket containing distinct full records.
    let bucket = vec![0, 1, 2, 3, 4];
    assert_eq!(
        shared_position(
            bucket.iter().copied(),
            &nodes,
            &without_id(record(100, Json::obj([("id", Json::str("nested-B"))])))
        ),
        Some(1)
    );
    assert_eq!(
        shared_position(
            bucket.iter().copied(),
            &nodes,
            &without_id(record(100, plain(&[4, 2, 4])))
        ),
        Some(2)
    );
    assert_eq!(
        shared_position(
            bucket.iter().copied(),
            &nodes,
            &without_id(record(100, plain(&[2, 4, 4])))
        ),
        None
    );
    for (key, value) in [
        ("type", Json::str("different type")),
        ("state", Json::str("different state")),
        ("conditions", Json::Arr(vec![Json::Bool(true)])),
        ("reasons", Json::Arr(vec![Json::str("different reason")])),
    ] {
        let mut different = record(100, Json::Bool(true));
        let Json::Obj(fields) = &mut different else {
            panic!()
        };
        fields.insert(key.into(), value);
        assert_eq!(
            shared_position(bucket.iter().copied(), &nodes, &without_id(different)),
            None
        );
    }
    for malformed in [
        Json::obj([("node", Json::str("n04"))]),
        Json::obj([("node", Json::str("n4")), ("extra", Json::Bool(true))]),
    ] {
        assert_eq!(
            shared_position(
                bucket.iter().copied(),
                &nodes,
                &without_id(record(100, Json::Arr(vec![malformed])))
            ),
            None
        );
    }
    let repeated = vec![record(8, Json::Bool(true)), record(9, Json::Bool(true))];
    assert_eq!(
        shared_position(
            [0, 1].into_iter(),
            &repeated,
            &without_id(record(12, Json::Bool(true)))
        ),
        Some(0)
    );
}

#[test]
fn sharing_matches_legacy_first_seen_and_prior_reference_renaming() {
    let native = (0..6)
        .map(|i| {
            fixture_node(if i == 4 {
                NodeType::Construction(T::FiniteFunction)
            } else {
                NodeType::Value(Type::Bool)
            })
        })
        .collect::<Vec<_>>();
    let projected = BTreeMap::from([
        (0, record(0, Json::Bool(true))),
        (1, record(1, Json::Bool(true))),
        (2, record(2, Json::NodeReferences(vec![0]))),
        (3, record(3, plain(&[1]))),
        (4, record(4, plain(&[0]))),
        (5, record(5, Json::obj([("id", Json::str("nested"))]))),
    ]);
    let mut old_ids = ids(&projected);
    let mut new_ids = old_ids.clone();
    let old = legacy_share(
        projected.clone(),
        &native,
        &mut old_ids,
        &Control::unlimited(),
        Checkpoint::Expression,
    )
    .unwrap();
    let new = share_projected(
        projected,
        &native,
        &mut new_ids,
        &Control::unlimited(),
        Checkpoint::Expression,
    )
    .unwrap();
    assert_eq!(Json::Arr(new).canonical(), Json::Arr(old).canonical());
    assert_eq!(new_ids, old_ids);
    assert_eq!(new_ids["n1"], "n0");
    assert_eq!(new_ids["n3"], "n2");
    assert_eq!(new_ids["n4"], "n4");
    // BTreeMap numeric order, not insertion order or lexical "n10" order.
    let native = (0..11)
        .map(|_| fixture_node(NodeType::Value(Type::Bool)))
        .collect::<Vec<_>>();
    let projected = BTreeMap::from([
        (10, record(10, Json::Bool(true))),
        (2, record(2, Json::Bool(true))),
    ]);
    let mut ids = ids(&projected);
    let nodes = share_projected(
        projected,
        &native,
        &mut ids,
        &Control::unlimited(),
        Checkpoint::Expression,
    )
    .unwrap();
    assert_eq!(nodes.len(), 1);
    assert_eq!(ids["n10"], "n2");
}

#[test]
fn expression_is_the_only_change_to_the_shared_type_boundary() {
    for (ty, shared) in [
        (NodeType::Value(Type::Bool), true),
        (NodeType::Vector(NodeRef(0)), true),
        (NodeType::ModuleMap(NodeRef(0), NodeRef(1)), true),
        (NodeType::Domain, true),
        (NodeType::Construction(T::StateMap), true),
        (NodeType::Construction(T::Ring), true),
        (NodeType::Construction(T::Module), true),
        (NodeType::Construction(T::FiniteFunction), false),
        (NodeType::Expression(Type::Bool), true),
        (NodeType::Evaluation(Type::Bool), false),
        (NodeType::Proposition, false),
        (NodeType::LawInstance, false),
        (NodeType::Evidence, false),
        (NodeType::ObservationPlan, false),
    ] {
        let is_expression = matches!(ty, NodeType::Expression(_));
        let native = vec![fixture_node(ty.clone()), fixture_node(ty)];
        let projected = BTreeMap::from([
            (0, record(0, Json::Bool(true))),
            (1, record(1, Json::Bool(true))),
        ]);
        let mut old_ids = ids(&projected);
        let mut new_ids = old_ids.clone();
        let old = legacy_share(
            projected.clone(),
            &native,
            &mut old_ids,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        let new = share_projected(
            projected,
            &native,
            &mut new_ids,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .unwrap();
        assert_eq!(new.len(), if shared { 1 } else { 2 });
        if is_expression {
            assert_eq!(old.len(), 2);
            assert_eq!(new_ids["n1"], new_ids["n0"]);
        } else {
            assert_eq!(Json::Arr(new), Json::Arr(old));
            assert_eq!(new_ids, old_ids);
        }
    }
}

#[test]
fn sharing_keeps_every_existing_checkpoint_and_stop() {
    let native = vec![
        fixture_node(NodeType::Value(Type::Bool)),
        fixture_node(NodeType::Value(Type::Bool)),
    ];
    let projected = BTreeMap::from([
        (0, record(0, Json::Bool(true))),
        (1, record(1, plain(&[0]))),
    ]);
    fn count(operation: impl FnOnce(&Control)) -> usize {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        operation(&Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        }));
        count.get()
    }
    let old_count = count(|c| {
        legacy_share(
            projected.clone(),
            &native,
            &mut ids(&projected),
            c,
            Checkpoint::Expression,
        )
        .unwrap();
    });
    let new_count = count(|c| {
        share_projected(
            projected.clone(),
            &native,
            &mut ids(&projected),
            c,
            Checkpoint::Expression,
        )
        .unwrap();
    });
    assert_eq!(new_count, old_count);
    for signal in [Signal::Int, Signal::Term] {
        for at in 1..=old_count {
            let mut visits = 0;
            let c = Control::new(move |_| {
                visits += 1;
                (visits == at).then_some(signal)
            });
            assert_eq!(
                share_projected(
                    projected.clone(),
                    &native,
                    &mut ids(&projected),
                    &c,
                    Checkpoint::Expression
                ),
                Err(signal)
            );
        }
    }
}
