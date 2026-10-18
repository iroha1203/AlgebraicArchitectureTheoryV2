//! 元Owned TypeAstと実ownerを保つ有限型量化の三入力byte API検査。
mod common;
use archsig::{
    archmap::{Mode, Slot},
    canonical::{Json, sha256_digest},
    definition::check_definitions_controlled,
    law::ast::{Builtin, ExprKind, QuantDomain, QuantSplit, TypeAst},
    observed::{
        ObservedEvaluation,
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
};
use std::collections::{BTreeMap, BTreeSet};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object {j:?}")
    };
    v
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array {j:?}")
    };
    v
}
fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    &obj(j)[key]
}
fn val(j: &Json) -> &Json {
    assert_eq!(f(j, "state"), &Json::str("value"));
    f(j, "value")
}
fn ty(k: &str, t: Json) -> Json {
    Json::Arr(vec![Json::str(k), t])
}
fn reference(snapshot: &str, id: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(id)])
}
fn option(v: Option<Json>) -> Json {
    v.map_or_else(
        || Json::obj([("none", Json::Bool(true))]),
        |v| Json::obj([("some", v)]),
    )
}
fn normalized(t: &Json, v: &Json) -> Json {
    if let Json::Arr(types) = t {
        match types.first().map(text) {
            Some("Set") => {
                let mut items: Vec<_> = arr(v).iter().map(|v| normalized(&types[1], v)).collect();
                items.sort_by_key(Json::canonical);
                return Json::Arr(items);
            }
            Some("Tuple") => {
                return Json::Arr(
                    types[1..]
                        .iter()
                        .zip(arr(v))
                        .map(|(t, v)| normalized(t, v))
                        .collect(),
                );
            }
            Some("Option") => {
                return if let Some(v) = obj(v).get("some") {
                    option(Some(normalized(&types[1], v)))
                } else {
                    option(None)
                };
            }
            _ => {}
        }
    }
    v.clone()
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let n = |j: &Json| match j {
        Json::Nat(n) => *n as usize,
        _ => panic!("Nat"),
    };
    (n(&a[0]), n(&a[1]))
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
fn index(w: &Json) -> BTreeMap<&str, &Json> {
    arr(f(w, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, r: &Json, t: &Json) -> &'a Json {
    assert_eq!(obj(r).len(), 1);
    let n = ns[text(f(r, "node"))];
    assert_eq!(f(n, "type"), t);
    n
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn reachable(ns: &BTreeMap<&str, &Json>, root: &Json) -> BTreeSet<String> {
    let mut todo = vec![];
    refs(root, &mut todo);
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    seen
}
fn fixture(
    script: &str,
    omit: Option<&str>,
    negative: Option<&str>,
    second: bool,
    moved: bool,
) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let root = entity_json("T.Root", "[]", "[]");
    let child = entity_json(
        "T.E",
        &format!("[{}]", field_json("owner", r#"["Ref","T.Root"]"#)),
        &format!("[{}]", field_json("ok", r#""Bool""#)),
    );
    let hop = format!(
        r#"{{"kind":"arrow","name":"T.Hop","meaning":"小さい所属操作。","parameters":[{},{},{}],"fields":[],"alignments":[]}}"#,
        field_json("owner", r#"["Ref","T.Root"]"#),
        field_json("from", r#"["Owned","T.E","owner"]"#),
        field_json("to", r#"["Owned","T.E","owner"]"#)
    );
    let movement = entity_json(
        "T.Move",
        "[]",
        &format!("[{}]", field_json("from", r#"["Ref","T.Root"]"#)),
    );
    let boxed = data_json(
        "T.RootBox",
        &format!("[{}]", constructor_json("At", r#"[["Ref","T.Root"]]"#)),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "T",
            &format!("[{root},{child},{hop},{movement},{boxed}]"),
            "[]"
        )
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["T"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading Inspect {{use vocabulary T version "1" digest "{digest}";{script}}}"#
    );
    let mut origins = vec![];
    let mut snapshots = vec![];
    for snapshot in if second { vec!["v", "w"] } else { vec!["v"] } {
        let mode = if snapshot == "v" {
            "specification"
        } else {
            "proposed"
        };
        let shift = if moved { 20 } else { 0 };
        for (kind, start) in [("subjects", 1), ("owners", 3), ("values", 5)] {
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}","mode":"{mode}","method":"小さい有限型量化の原始入力。","locations":[{{"source":"scan","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1));
        }
        let subjects = [
            ("A", "Root"),
            ("B", "Root"),
            ("Z", "Root"),
            ("p", "E"),
            ("q", "E"),
            ("r", "E"),
            ("hA", "Hop"),
            ("hB", "Hop"),
            ("m", "Move"),
        ]
        .map(|(id, t)| format!(r#"{{"id":"{id}","type":"T.{t}","origin":"{snapshot}_subjects"}}"#))
        .join(",");
        let (a, b) = if snapshot == "v" {
            ("A", "B")
        } else {
            ("B", "A")
        };
        let mut atoms = vec![];
        for (id, entity, field, value) in [
            ("p", "E", "owner", reference(snapshot, a)),
            ("q", "E", "owner", reference(snapshot, b)),
            ("r", "E", "owner", reference(snapshot, a)),
            ("p", "E", "ok", Json::Bool(negative != Some("p-ok"))),
            ("q", "E", "ok", Json::Bool(true)),
            ("r", "E", "ok", Json::Bool(negative != Some("r-ok"))),
            ("hA", "Hop", "owner", reference(snapshot, a)),
            ("hA", "Hop", "from", reference(snapshot, "p")),
            ("hA", "Hop", "to", reference(snapshot, "p")),
            ("hB", "Hop", "owner", reference(snapshot, b)),
            ("hB", "Hop", "from", reference(snapshot, "q")),
            ("hB", "Hop", "to", reference(snapshot, "q")),
            ("m", "Move", "from", reference(snapshot, a)),
        ] {
            let atom = format!("{id}-{field}");
            if snapshot == "v" && omit == Some(atom.as_str()) {
                continue;
            }
            let kind = if field == "owner" { "owners" } else { "values" };
            atoms.push(format!(r#"{{"id":"{atom}","subject":"{id}","field":"T.{entity}.{field}","value":{},"origin":"{snapshot}_{kind}"}}"#,value.canonical()));
        }
        snapshots.push(format!(r#"{{"id":"{snapshot}","origin":"{snapshot}_subjects","subjects":[{subjects}],"atoms":[{}]}}"#,atoms.join(",")));
    }
    let (uri, revision) = if moved {
        ("urn:fixture:owned-type:moved", "r2")
    } else {
        ("urn:fixture:owned-type", "r1")
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"T","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn unchanged(a: &CheckedInputs, b: &CheckedInputs) {
    assert_eq!(a.sources(), b.sources());
    assert_eq!(a.inputs(), b.inputs());
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(b.definitions(), &b.law().definitions);
    assert_eq!(a.law().exprs, b.law().exprs);
    assert_eq!(a.law().expr_types, b.law().expr_types);
    assert_eq!(a.law().declarations, b.law().declarations);
    assert_eq!(a.law().infos, b.law().infos);
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_eq!(
        b.law().bytes_digest,
        sha256_digest(b.sources().law().bytes())
    );
    assert_eq!(a.archmap().snapshots, b.archmap().snapshots);
    assert_eq!(a.archmap().origins, b.archmap().origins);
    assert_eq!(a.archmap().sources, b.archmap().sources);
    assert_eq!(a.archmap().vocabularies, b.archmap().vocabularies);
    assert_eq!(a.archmap().model_digest, b.archmap().model_digest);
    assert_eq!(
        b.archmap().bytes_digest,
        sha256_digest(b.sources().archmap().bytes())
    );
}
fn erased(original: &TypeAst, checked: &CheckedInputs) -> Json {
    match original {
        TypeAst::Named { name, .. } => {
            let target = checked
                .law()
                .infos
                .iter()
                .flat_map(|d| &d.references)
                .find(|(at, _)| *at == name.span())
                .unwrap();
            ty("Ref", Json::str(&target.1))
        }
        TypeAst::Builtin(Builtin::Bool, _) => Json::str("Bool"),
        TypeAst::Tuple(items, _) => Json::Arr(
            std::iter::once(Json::str("Tuple"))
                .chain(items.iter().map(|t| erased(t, checked)))
                .collect(),
        ),
        TypeAst::Option(t, _) => ty("Option", erased(t, checked)),
        TypeAst::Set(t, _) => ty("Set", erased(t, checked)),
        t => panic!("この小例の型 {t:?}"),
    }
}
fn original_names(original: &TypeAst, checked: &CheckedInputs) {
    let law = checked.sources().law().bytes();
    match original {
        TypeAst::Named {
            name,
            index: Some(owner),
            ..
        } => {
            assert_eq!(&law[owner.span.0..owner.span.1], owner.name.as_bytes());
            assert_eq!(&law[name.span().0..name.span().1], name.text().as_bytes());
            assert!(
                checked
                    .law()
                    .infos
                    .iter()
                    .flat_map(|d| &d.references)
                    .any(|(at, target)| *at == name.span()
                        && matches!(target.as_str(), "T.E" | "T.Hop"))
            );
        }
        TypeAst::Tuple(items, _) => items.iter().for_each(|t| original_names(t, checked)),
        TypeAst::Option(t, _) | TypeAst::Set(t, _) => original_names(t, checked),
        _ => {}
    }
}
fn owner_leaves<'a>(
    t: &'a TypeAst,
    out: &mut Vec<(&'a archsig::law::ast::QName, &'a archsig::law::ast::Ident)>,
) {
    match t {
        TypeAst::Named {
            name,
            index: Some(owner),
            ..
        } => out.push((name, owner)),
        TypeAst::Tuple(items, _) => items.iter().for_each(|t| owner_leaves(t, out)),
        TypeAst::Option(t, _) | TypeAst::Set(t, _) => owner_leaves(t, out),
        _ => {}
    }
}
fn audit(w: &Json, checked: &CheckedInputs) {
    let ns = index(w);
    let mut earlier = BTreeSet::new();
    for n in arr(f(w, "nodes")) {
        for q in arr(f(f(n, "scope"), "quantifiers")) {
            if let Some(r) = obj(q).get("domain") {
                let domain = target(&ns, r, &Json::str("Domain"));
                assert_eq!(f(val(domain), "type"), f(q, "type"));
            }
        }
        let mut links = vec![];
        refs(n, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "既出Ref {link}");
        }
        assert!(earlier.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut links = vec![];
            refs(v, &mut links);
            for link in links {
                assert_ne!(f(ns[link.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[link.as_str()]).contains_key("partial"));
            }
        }
        assert_eq!(
            f(f(n, "scope"), "readings"),
            &Json::Arr(vec![Json::str("Inspect")])
        );
        assert!(arr(f(f(n, "scope"), "assumptions")).is_empty());
        for fact in arr(f(n, "support")) {
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let (origin, kind, start) = if let Some(field) = obj(fact).get("field") {
                let Slot::Known {
                    atom,
                    origin,
                    pointer,
                    ..
                } = &subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap()
                    .slot
                else {
                    panic!("欠測をsupportにしない")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/") && pointer.ends_with("/value"));
                if text(field).ends_with(".owner") {
                    (origin, "owners", 3)
                } else {
                    (origin, "values", 5)
                }
            } else {
                (&subject.origin, "subjects", 1)
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert_eq!(
                origin.mode,
                if snapshot.id == "v" {
                    Mode::Specification
                } else {
                    Mode::Proposed
                }
            );
            let location = &origin.locations[0];
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == location.source)
                .unwrap();
            let moved = source.revision == "r2";
            let shift = if moved { 20 } else { 0 };
            assert_eq!(location.path, format!("{}.{kind}.model", snapshot.id));
            assert_eq!(location.span, Some((start + shift, start + shift + 1)));
            assert_eq!(
                source.uri,
                if moved {
                    "urn:fixture:owned-type:moved"
                } else {
                    "urn:fixture:owned-type"
                }
            );
        }
        if f(n, "type") == &Json::str("Evidence")
            && f(val(n), "kind") == &Json::str("finite_exhaustion")
        {
            let data = f(val(n), "data");
            let domain = target(&ns, f(data, "domain"), &Json::str("Domain"));
            assert_eq!(
                f(data, "checked"),
                &Json::Nat(arr(f(data, "instances")).len() as u64)
            );
            assert_eq!(
                arr(f(val(domain), "elements")).len(),
                arr(f(data, "instances")).len()
            );
        }
        if f(n, "type") == &Json::str("Domain") && f(val(n), "kind") == &Json::str("finite") {
            for r in arr(f(val(n), "elements")) {
                target(&ns, r, f(val(n), "type"));
            }
        }
    }
    for a in arr(f(w, "answers")) {
        let mut links = vec![];
        refs(a, &mut links);
        assert!(links.iter().all(|r| ns.contains_key(r.as_str())));
        if let Some(claim) = obj(a).get("claim") {
            assert_eq!(
                f(
                    f(target(&ns, claim, &Json::str("Proposition")), "judgment"),
                    "status"
                ),
                f(a, "status")
            );
        }
    }
}
fn run(inputs: InputSources, asks: &[&str]) -> ObservedEvaluation {
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let result = evaluate_observed_bytes(inputs, asks, &mut quiet()).unwrap();
    unchanged(&checked, result.prepared().inputs());
    audit(&result.wire(), result.prepared().inputs());
    result
}
fn output(w: &Json, id: &str, expected: Json) {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert_eq!(
        val(target(
            &index(w),
            f(f(a, "outputs"), "value"),
            &Json::str("Bool")
        )),
        &expected
    );
}
// expectedは各小fixtureの原owner配置からliteralで与える。出力memberから構成しない。
fn domains(result: &ObservedEvaluation, id: &str, binder: &str, wanted: &[Vec<Json>]) {
    let w = result.wire();
    let ns = index(&w);
    let checked = result.prepared().inputs();
    let reached = reachable(&ns, answer(&w, id));
    let mut actual = BTreeSet::new();
    let mut found = 0;
    let mut domain_type = None;
    for domain in arr(f(&w, "nodes")).iter().filter(|n| {
        f(n, "type") == &Json::str("Domain")
            && reached.contains(text(f(n, "id")))
            && f(val(n), "kind") == &Json::str("finite")
    }) {
        let Some(source_ref) = arr(f(domain, "arguments")).first() else {
            continue;
        };
        if f(ns[text(f(source_ref, "node"))], "type") != &Json::str("Expression") {
            continue;
        }
        let source = target(&ns, source_ref, &Json::str("Expression"));
        if !arr(f(source, "reasons")).is_empty() {
            continue;
        } // 欠測を持つCompletionSeedのassignment域は元型Domainと区別する。
        let position = span(f(val(source), "location"));
        let Some(expr) = checked.law().exprs.iter().find(|e| e.span == position) else {
            continue;
        };
        let ExprKind::Quant {
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::Type(original),
                    body,
                },
            ..
        } = &expr.kind
        else {
            continue;
        };
        if var.name != binder {
            continue;
        }
        original_names(original, checked);
        assert_eq!(f(val(domain), "type"), &erased(original, checked));
        let t = f(val(domain), "type");
        if let Some(prior) = &domain_type {
            assert_eq!(prior, t);
        } else {
            domain_type = Some(t.clone());
        }
        assert_eq!(
            &checked.sources().law().bytes()[var.span.0..var.span.1],
            var.name.as_bytes()
        );
        let elements = arr(f(val(domain), "elements"));
        let mut leaves = vec![];
        owner_leaves(original, &mut leaves);
        let source_args = arr(f(source, "arguments"));
        assert!(source_args.len() >= leaves.len());
        let owners = &source_args[source_args.len() - leaves.len()..];
        let prefix: Vec<_> = std::iter::once(source_ref.clone())
            .chain(owners.iter().cloned())
            .collect();
        assert_eq!(
            arr(f(domain, "arguments")),
            [prefix.as_slice(), elements].concat().as_slice()
        );
        for r in elements {
            assert_eq!(arr(f(target(&ns, r, t), "arguments")), prefix.as_slice());
        }
        for ((name, index_name), owner_ref) in leaves.into_iter().zip(owners) {
            let producer = ns[text(f(owner_ref, "node"))];
            if f(producer, "type") == &ty("Ref", Json::str("T.Root")) {
                if let Some(binding) = arr(f(val(source), "bindings"))
                    .iter()
                    .find(|b| f(b, "name") == &Json::str(&index_name.name))
                {
                    assert_eq!(
                        f(binding, "value"),
                        owner_ref,
                        "宣言parameterの元Binding producer"
                    );
                } else {
                    assert!(
                        arr(f(&w, "nodes"))
                            .iter()
                            .any(|n| f(n, "type") == &Json::str("Domain")
                                && f(val(n), "kind") == &Json::str("finite")
                                && arr(f(val(n), "elements")).contains(owner_ref)),
                        "外側量化の現在member Scalar"
                    );
                }
            } else {
                assert_eq!(f(producer, "type"), &Json::str("Evaluation"));
                let origin = target(
                    &ns,
                    f(val(producer), "expression"),
                    &Json::str("Expression"),
                );
                let origin_span = span(f(val(origin), "location"));
                let lexical = checked.law().exprs.iter().find_map(|e| match &e.kind {
                    ExprKind::Let { name, value, body }
                        if name.name == index_name.name
                            && checked.law().exprs[*body].span.0 <= expr.span.0
                            && expr.span.1 <= checked.law().exprs[*body].span.1 =>
                    {
                        Some(*value)
                    }
                    _ => None,
                });
                if let Some(rhs) = lexical {
                    assert_eq!(
                        origin_span,
                        checked.law().exprs[rhs].span,
                        "letの元field RHS producer"
                    );
                } else if let Some(scrutinee) =
                    checked.law().exprs.iter().find_map(|e| match &e.kind {
                        ExprKind::Match { scrutinee, .. }
                            if e.span.0 <= expr.span.0 && expr.span.1 <= e.span.1 =>
                        {
                            Some(*scrutinee)
                        }
                        _ => None,
                    })
                {
                    assert_eq!(
                        origin_span,
                        checked.law().exprs[scrutinee].span,
                        "patternの元scrutinee producer"
                    );
                } else {
                    assert!(
                        source_args[..source_args.len() - owners.len()].contains(owner_ref),
                        "通常call/内包の現在producerを元Context引数へ戻す"
                    );
                    assert!(checked.law().exprs.iter().any(|e| e.span == origin_span));
                }
            }
            let entity = &checked
                .law()
                .infos
                .iter()
                .flat_map(|d| &d.references)
                .find(|(at, _)| *at == name.span())
                .unwrap()
                .1;
            for snapshot in checked
                .archmap()
                .snapshots
                .iter()
                .filter(|s| arr(f(f(domain, "scope"), "snapshots")).contains(&Json::str(&s.id)))
            {
                for subject in snapshot.subjects.iter().filter(|s| &s.ty == entity) {
                    let field = subject
                        .fields
                        .iter()
                        .find(|f| f.name == format!("{entity}.owner"))
                        .unwrap();
                    let Slot::Known { atom, .. } = &field.slot else {
                        panic!("未知owner域を完成Domainにしない")
                    };
                    let fact = Json::obj([
                        ("snapshot", Json::str(&snapshot.id)),
                        ("subject", Json::str(&subject.id)),
                        ("field", Json::str(&field.name)),
                        ("atom", Json::str(atom)),
                    ]);
                    assert!(
                        arr(f(domain, "support")).contains(&fact),
                        "所属/非所属ownerFactと空族の支持"
                    );
                }
            }
        }
        let values: Vec<_> = elements
            .iter()
            .map(|r| val(target(&ns, r, f(val(domain), "type"))).clone())
            .collect();
        assert_eq!(
            values.len(),
            values
                .iter()
                .map(|v| normalized(t, v).canonical())
                .collect::<BTreeSet<_>>()
                .len()
        );
        let mut key: Vec<_> = values
            .iter()
            .map(|v| normalized(t, v).canonical())
            .collect();
        key.sort();
        actual.insert(key);
        found += 1;
        let evaluations: Vec<_> = arr(f(&w, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && f(val(n), "expression") == source_ref
                    && arr(f(val(n), "parts")).len() == 1
                    && arr(f(n, "arguments")).first() == Some(source_ref)
            })
            .collect();
        assert_eq!(evaluations.len(), 1, "元Contextの量化評価");
        let evaluation = evaluations[0];
        let children = arr(f(&arr(f(val(evaluation), "parts"))[0], "children"));
        assert_eq!(children.len(), elements.len());
        for (child, member) in children.iter().zip(elements) {
            let child = target(&ns, child, &Json::str("Evaluation"));
            let expression = target(&ns, f(val(child), "expression"), &Json::str("Expression"));
            assert_eq!(
                span(f(val(expression), "location")),
                checked.law().exprs[*body].span
            );
            assert!(
                arr(f(expression, "arguments")).contains(member),
                "binderの元memberproducer"
            );
        }
    }
    let expected: BTreeSet<_> = wanted
        .iter()
        .map(|values| {
            let mut key: Vec<_> = values
                .iter()
                .map(|v| normalized(domain_type.as_ref().expect("実Domain型"), v).canonical())
                .collect();
            key.sort();
            key
        })
        .collect();
    assert!(found > 0, "実Domainを保持");
    assert_eq!(actual, expected);
}
fn simple(script: &str, ask: &str, binder: &str, values: Vec<Json>, value: bool) {
    let r = run(fixture(script, None, None, false, false), &[ask]);
    output(&r.wire(), "out", Json::Bool(value));
    domains(&r, "out", binder, &[values]);
}

#[test]
fn owned_type_entity_forall_and_exists_keep_owner_and_concrete_ref_domains() {
    let script = "view test(a:Root):Bool=forall x:E[a] . x.ok;view witness(a:Root):Bool=exists y:E[a] . y.ok;";
    let r = run(
        fixture(script, None, None, false, false),
        &[
            "out=evaluate(Inspect.test,a=@v/A)",
            "hit=evaluate(Inspect.witness,a=@v/B)",
        ],
    );
    let w = r.wire();
    output(&w, "out", Json::Bool(true));
    output(&w, "hit", Json::Bool(true));
    domains(
        &r,
        "out",
        "x",
        &[vec![reference("v", "p"), reference("v", "r")]],
    );
    domains(&r, "hit", "y", &[vec![reference("v", "q")]]);
}
#[test]
fn owned_type_arrow_quantifier_uses_same_snapshot_and_owner() {
    simple(
        "view test(a:Root):Bool=forall h:Hop[a] . true;",
        "out=evaluate(Inspect.test,a=@v/A)",
        "h",
        vec![reference("v", "hA")],
        true,
    );
}
#[test]
fn owned_type_short_and_full_names_keep_each_original_type_occurrence() {
    let r = run(
        fixture(
            "view short_name(a:Root):Bool=forall x:E[a] . true;view full_name(a:Root):Bool=forall y:T.E[a] . true;",
            None,
            None,
            false,
            false,
        ),
        &[
            "out=evaluate(Inspect.short_name,a=@v/A)",
            "named=evaluate(Inspect.full_name,a=@v/A)",
        ],
    );
    for (id, binder) in [("out", "x"), ("named", "y")] {
        output(&r.wire(), id, Json::Bool(true));
        domains(
            &r,
            id,
            binder,
            &[vec![reference("v", "p"), reference("v", "r")]],
        );
    }
}
#[test]
fn owned_type_same_ids_in_other_snapshot_keep_distinct_owned_domains() {
    simple(
        "view test(a:Root):Bool=forall x:E[a] . true;",
        "out=evaluate(Inspect.test,a=@v/B)",
        "x",
        vec![reference("v", "q")],
        true,
    );
    let r = run(
        fixture(
            "view test(a:Root):Bool=forall x:E[a] . true;",
            None,
            None,
            true,
            false,
        ),
        &["out=evaluate(Inspect.test,a=@w/A)"],
    );
    output(&r.wire(), "out", Json::Bool(true));
    domains(&r, "out", "x", &[vec![reference("w", "q")]]);
}
#[test]
fn owned_type_tuple_keeps_same_entity_with_two_different_owner_indices() {
    simple(
        "view test(a:Root,b:Root):Bool=forall pair:(E[a],E[b]) . pair.0!=pair.1;",
        "out=evaluate(Inspect.test,a=@v/A,b=@v/B)",
        "pair",
        vec![
            Json::Arr(vec![reference("v", "p"), reference("v", "q")]),
            Json::Arr(vec![reference("v", "r"), reference("v", "q")]),
        ],
        true,
    );
}
#[test]
fn owned_type_option_has_none_and_each_owned_some() {
    simple(
        "view test(a:Root):Bool=forall item:Option<E[a]> . true;",
        "out=evaluate(Inspect.test,a=@v/A)",
        "item",
        vec![
            option(None),
            option(Some(reference("v", "p"))),
            option(Some(reference("v", "r"))),
        ],
        true,
    );
}
#[test]
fn owned_type_set_has_exact_small_power_set() {
    simple(
        "view test(a:Root):Bool=forall group:Set<E[a]> . count(group)>=0;",
        "out=evaluate(Inspect.test,a=@v/A)",
        "group",
        vec![
            Json::Arr(vec![]),
            Json::Arr(vec![reference("v", "p")]),
            Json::Arr(vec![reference("v", "r")]),
            Json::Arr(vec![reference("v", "p"), reference("v", "r")]),
        ],
        true,
    );
}
#[test]
fn owned_type_option_set_nesting_keeps_five_concrete_members() {
    simple(
        "view test(a:Root):Bool=forall item:Option<Set<E[a]>> . true;",
        "out=evaluate(Inspect.test,a=@v/A)",
        "item",
        vec![
            option(None),
            option(Some(Json::Arr(vec![]))),
            option(Some(Json::Arr(vec![reference("v", "p")]))),
            option(Some(Json::Arr(vec![reference("v", "r")]))),
            option(Some(Json::Arr(vec![
                reference("v", "p"),
                reference("v", "r"),
            ]))),
        ],
        true,
    );
}
#[test]
fn owned_type_empty_forall_and_exists_keep_zero_members() {
    let script = "view universal(a:Root):Bool=forall x:E[a] . true;view witness(a:Root):Bool=exists y:E[a] . true;";
    let r = run(
        fixture(script, None, None, false, false),
        &[
            "out=evaluate(Inspect.universal,a=@v/Z)",
            "hit=evaluate(Inspect.witness,a=@v/Z)",
        ],
    );
    let w = r.wire();
    output(&w, "out", Json::Bool(true));
    output(&w, "hit", Json::Bool(false));
    domains(&r, "out", "x", &[vec![]]);
    domains(&r, "hit", "y", &[vec![]]);
}
#[test]
fn owned_type_empty_option_and_set_each_keep_one_member() {
    let script = "view wrapped(a:Root):Bool=forall opt:Option<E[a]> . true;view subsets(a:Root):Bool=forall group:Set<E[a]> . true;";
    let r = run(
        fixture(script, None, None, false, false),
        &[
            "opt=evaluate(Inspect.wrapped,a=@v/Z)",
            "sub=evaluate(Inspect.subsets,a=@v/Z)",
        ],
    );
    for id in ["opt", "sub"] {
        output(&r.wire(), id, Json::Bool(true));
    }
    domains(&r, "opt", "opt", &[vec![option(None)]]);
    domains(&r, "sub", "group", &[vec![Json::Arr(vec![])]]);
}
#[test]
fn owned_type_let_owner_reads_original_field_producer() {
    simple(
        "view test(m:Move):Bool=let a=m.from in forall x:E[a] . x.ok;",
        "out=evaluate(Inspect.test,m=@v/m)",
        "x",
        vec![reference("v", "p"), reference("v", "r")],
        true,
    );
}
#[test]
fn owned_type_pattern_owner_keeps_selected_constructor_and_binder() {
    simple(
        "view test(a:Root):Bool=match RootBox.At(a){At(x)=>forall item:E[x] . true;};",
        "out=evaluate(Inspect.test,a=@v/A)",
        "item",
        vec![reference("v", "p"), reference("v", "r")],
        true,
    );
}
#[test]
fn owned_type_plain_view_call_keeps_current_actual_owner() {
    simple(
        "view inner(a:Root):Bool=forall item:E[a] . true;view test(root:Root):Bool=inner(root);",
        "out=evaluate(Inspect.test,root=@v/A)",
        "item",
        vec![reference("v", "p"), reference("v", "r")],
        true,
    );
}
#[test]
fn owned_type_outer_quantifier_keeps_each_iteration_owner() {
    let r = run(
        fixture(
            "view test():Bool=forall root:Root . forall item:E[root] . true;",
            None,
            None,
            false,
            false,
        ),
        &["out=evaluate(Inspect.test)"],
    );
    output(&r.wire(), "out", Json::Bool(true));
    domains(
        &r,
        "out",
        "item",
        &[
            vec![reference("v", "p"), reference("v", "r")],
            vec![reference("v", "q")],
            vec![],
        ],
    );
}
#[test]
fn owned_type_comprehension_owner_keeps_current_input_member() {
    let r = run(
        fixture(
            "view test(root:Root):Set<Bool> = set{(forall item:E[a] . true)|a in list<Root>[root]};",
            None,
            None,
            false,
            false,
        ),
        &["out=evaluate(Inspect.test,root=@v/A)"],
    );
    let w = r.wire();
    assert_eq!(f(answer(&w, "out"), "status"), &Json::str("established"));
    assert_eq!(
        val(target(
            &index(&w),
            f(f(answer(&w, "out"), "outputs"), "value"),
            &ty("Set", Json::str("Bool"))
        )),
        &Json::Arr(vec![Json::Bool(true)])
    );
    domains(
        &r,
        "out",
        "item",
        &[vec![reference("v", "p"), reference("v", "r")]],
    );
}
fn missing(w: &Json, id: &str, subject: &str, field: &str) {
    let a = answer(w, id);
    let reason = arr(f(a, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    assert_eq!(
        f(reason, "missing"),
        &Json::Arr(vec![Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str(subject)),
            ("field", Json::str(field))
        ])])
    );
    assert!(!arr(f(reason, "dependencies")).is_empty());
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
}
fn body_missing(omit: &str, negative: &str, subject: &str) {
    let r = run(
        fixture(
            "law required test(a:Root):forall item:E[a] . item.ok;",
            Some(omit),
            Some(negative),
            false,
            false,
        ),
        &["out=check(Inspect.test,a=@v/A)"],
    );
    let w = r.wire();
    assert_eq!(f(answer(&w, "out"), "status"), &Json::str("refuted"));
    missing(&w, "out", subject, "T.E.ok");
    domains(
        &r,
        "out",
        "item",
        &[vec![reference("v", "p"), reference("v", "r")]],
    );
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample"))
    );
    let ns = index(&w);
    let false_subject = negative.strip_suffix("-ok").unwrap();
    let fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(false_subject)),
        ("field", Json::str("T.E.ok")),
        ("atom", Json::str(negative)),
    ]);
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .filter(|n| f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample"))
            .any(|n| {
                let data = f(val(n), "data");
                arr(f(data, "facts")).contains(&fact)
                    && arr(f(data, "bindings")).iter().any(|b| {
                        f(b, "name") == &Json::str("item")
                            && val(target(&ns, f(b, "value"), &ty("Ref", Json::str("T.E"))))
                                == &reference("v", false_subject)
                    })
            }),
        "元既知反例と型付きbinderを保持する"
    );
}
#[test]
fn owned_type_missing_body_before_counterexample_keeps_domain_members() {
    body_missing("p-ok", "r-ok", "p");
}
#[test]
fn owned_type_missing_body_after_counterexample_keeps_domain_members() {
    body_missing("r-ok", "p-ok", "r");
}
fn completed_unknown(
    omit: &str,
    script: &str,
    ask: &str,
    subject: &str,
    field: &str,
    wanted: &[Vec<Json>],
) {
    let r = run(fixture(script, Some(omit), None, false, false), &[ask]);
    let w = r.wire();
    output(&w, "out", Json::Bool(true));
    missing(&w, "out", subject, field);
    assert_eq!(
        f(f(answer(&w, "out"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    assert!(
        !arr(f(answer(&w, "out"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
    let checked = r.prepared().inputs();
    let quantifier = checked
        .law()
        .exprs
        .iter()
        .find(|e| matches!(e.kind, ExprKind::Quant { .. }))
        .unwrap();
    let ExprKind::Quant {
        split:
            QuantSplit::Fixed {
                domain: QuantDomain::Type(original),
                ..
            },
        ..
    } = &quantifier.kind
    else {
        unreachable!()
    };
    let ns = index(&w);
    let t = erased(original, checked);
    let mut actual = BTreeSet::new();
    let mut count = 0;
    for domain in arr(f(&w, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Domain") && f(val(n), "type") == &t)
    {
        let source = target(
            &ns,
            &arr(f(domain, "arguments"))[0],
            &Json::str("Expression"),
        );
        if span(f(val(source), "location")) != quantifier.span {
            continue;
        }
        assert!(arr(f(source, "reasons")).is_empty());
        let mut values: Vec<_> = arr(f(val(domain), "elements"))
            .iter()
            .map(|r| normalized(&t, val(target(&ns, r, &t))).canonical())
            .collect();
        values.sort();
        assert_eq!(values.len(), values.iter().collect::<BTreeSet<_>>().len());
        actual.insert(values);
        count += 1;
    }
    let expected: BTreeSet<_> = wanted
        .iter()
        .map(|vs| {
            let mut vs: Vec<_> = vs.iter().map(|v| normalized(&t, v).canonical()).collect();
            vs.sort();
            vs
        })
        .collect();
    assert_eq!(actual, expected);
    assert_eq!(count, 3, "A/B/Zの元owner候補を全部評価する");
    let reason = arr(f(answer(&w, "out"), "reasons"))
        .iter()
        .find(|r| {
            f(r, "code") == &Json::str("missing_observation")
                && span(f(r, "location")) == original.span()
        })
        .expect("元TypeAst位置の欠測理由");
    assert_eq!(span(f(reason, "location")), original.span());
    audit(&w, checked);
}
#[test]
fn owned_type_missing_candidate_owner_keeps_exact_slot_and_each_complete_domain() {
    completed_unknown(
        "r-owner",
        "view test(a:Root):Bool=forall item:E[a] . true;",
        "out=evaluate(Inspect.test,a=@v/A)",
        "r",
        "T.E.owner",
        &[
            vec![reference("v", "p"), reference("v", "r")],
            vec![reference("v", "p")],
        ],
    );
}
#[test]
fn owned_type_missing_lexical_owner_keeps_original_field_and_type_location() {
    completed_unknown(
        "m-from",
        "view test(m:Move):Bool=let a=m.from in forall item:Option<E[a]> . true;",
        "out=evaluate(Inspect.test,m=@v/m)",
        "m",
        "T.Move.from",
        &[
            vec![
                option(None),
                option(Some(reference("v", "p"))),
                option(Some(reference("v", "r"))),
            ],
            vec![option(None), option(Some(reference("v", "q")))],
            vec![option(None)],
        ],
    );
}
#[test]
fn owned_type_empty_domain_does_not_skip_static_body_rejection() {
    let inputs = fixture(
        "view test(a:Root):Bool=forall item:E[a] . item.absent;",
        None,
        None,
        false,
        false,
    );
    let err = evaluate_observed_bytes(
        inputs.clone(),
        &["out=evaluate(Inspect.test,a=@v/Z)"],
        &mut quiet(),
    )
    .unwrap_err();
    let w = err.wire().unwrap();
    assert_eq!(f(&w, "status"), &Json::str("invalid"));
    assert!(arr(f(&w, "nodes")).is_empty());
    assert!(arr(f(&w, "answers")).is_empty());
    assert!(arr(f(&w, "issues")).iter().any(|i| {
        let p = span(f(i, "location"));
        inputs.law().bytes()[p.0..p.1]
            .windows(6)
            .any(|s| s == b"absent")
    }));
}
#[test]
fn owned_type_provenance_move_preserves_domain_and_current_owner_sources() {
    let script = "view test(a:Root):Bool=forall item:E[a] . true;";
    let asks = ["out=evaluate(Inspect.test,a=@v/A)"];
    let a = run(fixture(script, None, None, false, false), &asks);
    let b = run(fixture(script, None, None, false, true), &asks);
    for r in [&a, &b] {
        output(&r.wire(), "out", Json::Bool(true));
        domains(
            r,
            "out",
            "item",
            &[vec![reference("v", "p"), reference("v", "r")]],
        );
    }
    let a = a.prepared().inputs();
    let b = b.prepared().inputs();
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_eq!(a.archmap().snapshots, b.archmap().snapshots);
    assert_ne!(a.archmap().model_digest, b.archmap().model_digest);
}
#[test]
fn owned_type_unselected_if_branch_preserves_eager_order_and_single_lexical_producer() {
    let r = run(
        fixture(
            "view test(m:Move):Bool=if true then true else let a=m.from in forall item:E[a] . true;",
            None,
            None,
            false,
            false,
        ),
        &["out=evaluate(Inspect.test,m=@v/m)"],
    );
    let w = r.wire();
    output(&w, "out", Json::Bool(true));
    domains(
        &r,
        "out",
        "item",
        &[vec![reference("v", "p"), reference("v", "r")]],
    );
    let checked = r.prepared().inputs();
    let ns = index(&w);
    let conditional = checked
        .law()
        .exprs
        .iter()
        .find(|e| matches!(e.kind, ExprKind::If { .. }))
        .unwrap();
    let ExprKind::If {
        cond,
        then_branch,
        else_branch,
    } = &conditional.kind
    else {
        unreachable!()
    };
    let ExprKind::Let {
        value: rhs,
        body: quantifier,
        ..
    } = &checked.law().exprs[*else_branch].kind
    else {
        panic!("elseの元let")
    };
    let root = target(
        &ns,
        f(f(answer(&w, "out"), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let root_parts = arr(f(val(root), "parts"));
    assert_eq!(root_parts.len(), 1);
    assert_eq!(span(f(&root_parts[0], "location")), conditional.span);
    let branches = arr(f(&root_parts[0], "children"));
    assert_eq!(branches.len(), 3);
    let branch_evaluations: Vec<_> = branches
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evaluation")))
        .collect();
    for (evaluation, id) in branch_evaluations
        .iter()
        .zip([*cond, *then_branch, *else_branch])
    {
        let expression = target(
            &ns,
            f(val(evaluation), "expression"),
            &Json::str("Expression"),
        );
        assert_eq!(
            span(f(val(expression), "location")),
            checked.law().exprs[id].span
        );
        for fact in arr(f(evaluation, "support")) {
            assert!(
                arr(f(root, "support")).contains(fact),
                "cond/両枝の支持を保持する"
            );
        }
    }
    let else_parts = arr(f(val(branch_evaluations[2]), "parts"));
    assert_eq!(else_parts.len(), 1);
    let else_children = arr(f(&else_parts[0], "children"));
    assert_eq!(else_children.len(), 2);
    let rhs_eval = target(&ns, &else_children[0], &Json::str("Evaluation"));
    let quant_eval = target(&ns, &else_children[1], &Json::str("Evaluation"));
    for (evaluation, id) in [(rhs_eval, *rhs), (quant_eval, *quantifier)] {
        let expression = target(
            &ns,
            f(val(evaluation), "expression"),
            &Json::str("Expression"),
        );
        assert_eq!(
            span(f(val(expression), "location")),
            checked.law().exprs[id].span
        );
    }
    let quant_source = target(
        &ns,
        f(val(quant_eval), "expression"),
        &Json::str("Expression"),
    );
    assert_eq!(
        arr(f(quant_source, "arguments")).last(),
        Some(&else_children[0]),
        "添字は実行済みの単一RHS producerへ戻る"
    );
    let nodes = arr(f(&w, "nodes"));
    let position = |evaluation: &Json| {
        nodes
            .iter()
            .position(|n| f(n, "id") == f(evaluation, "id"))
            .unwrap()
    };
    let order = [
        position(branch_evaluations[0]),
        position(branch_evaluations[1]),
        position(rhs_eval),
        position(quant_eval),
        position(branch_evaluations[2]),
        position(root),
    ];
    assert!(
        order.windows(2).all(|pair| pair[0] < pair[1]),
        "cond→then→else RHS→Owned量化の実評価順"
    );
    let rhs_evaluations: Vec<_> = nodes
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation") && {
                let expression = target(&ns, f(val(n), "expression"), &Json::str("Expression"));
                f(val(expression), "kind") == &Json::str("source")
                    && span(f(val(expression), "location")) == checked.law().exprs[*rhs].span
            }
        })
        .collect();
    assert_eq!(
        rhs_evaluations.len(),
        1,
        "Source準備はlet RHSを先行/重複実評価しない"
    );
    for (subject, field, atom) in [
        ("m", "T.Move.from", "m-from"),
        ("p", "T.E.owner", "p-owner"),
        ("q", "T.E.owner", "q-owner"),
        ("r", "T.E.owner", "r-owner"),
    ] {
        let fact = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str(subject)),
            ("field", Json::str(field)),
            ("atom", Json::str(atom)),
        ]);
        assert!(
            arr(f(root, "support")).contains(&fact),
            "未選択elseの既知所属/非所属支持も保持"
        );
    }
}
