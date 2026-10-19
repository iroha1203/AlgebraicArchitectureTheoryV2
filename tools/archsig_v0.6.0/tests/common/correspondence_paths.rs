use archsig::{
    canonical::Json,
    json::{JNode, JValue, parse},
    observed::input::InputSources,
};
pub const SCRIPT: &str = r#"
view step(m:Migration):Path<System,System> =path(m);
view keep(p:Path<System,System>):Path<System,System> =p;
view maybe(m:Migration):Option<Path<System,System>> =some(step(m));
view nested(m:Migration):Option<List<(Bool,Path<System,System>)>> =some(list<(Bool,Path<System,System>)>[(true,path(m)),(false,let p=step(m) in if true then p else path(m))]);
view first(m:Migration):System=source(path(m));
view last(m:Migration):System=target(path(m));
view same(m:Migration,n:Migration):Bool=path(m)=path(n);
view self_action(m:Migration):Bool=path(m)=identity(source(path(m)));
view join(m:Migration,n:Migration):Path<System,System> =then(path(m),path(n));
view left(m:Migration):Bool=then(identity(source(path(m))),path(m))=path(m);
view right(m:Migration):Bool=then(path(m),identity(target(path(m))))=path(m);
view different_word(i:Migration,m:Migration):Bool=then(path(i),path(m))=path(m);
view unknown_same(m:Migration):Bool=path(m)=path(m);
view seed():Z=1;
law required prior():false;
"#;
pub fn convert(n: &JNode) -> Json {
    match &n.value {
        JValue::Str(s) => Json::str(s),
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Arr(xs) => Json::Arr(xs.iter().map(convert).collect()),
        JValue::Obj(xs) => Json::Obj(xs.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
        JValue::Null => panic!(),
    }
}
fn r(s: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(s)])
}
pub fn input(mode: &str, revision: &str) -> InputSources {
    let definitions = include_bytes!("../fixtures/reservations.atoms.json");
    let law = std::str::from_utf8(include_bytes!("../fixtures/reservations.law")).unwrap();
    let law = law.replacen(
        "reading Reservations {",
        &format!("reading Reservations {{{SCRIPT}"),
        1,
    );
    assert!(law.contains(SCRIPT));
    let mut map = convert(&parse(include_bytes!("../fixtures/reservations.archmap.json")).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    root.insert(
        "sources".into(),
        Json::Arr(vec![Json::obj([
            ("id", Json::str("scan")),
            ("uri", Json::str("urn:fixture:correspondence-path")),
            ("revision", Json::str(revision)),
            (
                "digest",
                Json::str(
                    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                ),
            ),
        ])]),
    );
    let Json::Arr(origins) = root.get_mut("origins").unwrap() else {
        panic!()
    };
    let Json::Obj(origin) = &mut origins[0] else {
        panic!()
    };
    origin.insert(
        "locations".into(),
        Json::Arr(vec![Json::obj([
            ("source", Json::str("scan")),
            ("path", Json::str("model.rs")),
            (
                "span",
                Json::Arr(vec![
                    Json::Nat(if revision == "r1" { 0 } else { 10 }),
                    Json::Nat(if revision == "r1" { 1 } else { 11 }),
                ]),
            ),
        ])]),
    );
    let Json::Arr(snaps) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let Json::Obj(snap) = &mut snaps[0] else {
        panic!()
    };
    let Json::Arr(subjects) = snap.get_mut("subjects").unwrap() else {
        panic!()
    };
    for id in ["alias", "self"] {
        subjects.push(Json::obj([
            ("id", Json::str(id)),
            ("type", Json::str("Reservations.Migration")),
            ("origin", Json::str("model")),
        ]));
    }
    let Json::Arr(atoms) = snap.get_mut("atoms").unwrap() else {
        panic!()
    };
    let originals = atoms.clone();
    for (id, identity) in [("alias", false), ("self", true)] {
        for a in &originals {
            let Json::Obj(a) = a else { panic!() };
            if a["subject"] != Json::str("m") {
                continue;
            }
            let mut a = a.clone();
            let Json::Str(old) = &a["id"] else { panic!() };
            a.insert(
                "id".into(),
                Json::str(&old.replacen("m-", &format!("{id}-"), 1)),
            );
            a.insert("subject".into(), Json::str(id));
            if identity {
                let Json::Str(field) = &a["field"] else {
                    panic!()
                };
                let value = match field.rsplit('.').next().unwrap() {
                    "to" => r("A"),
                    "states" => Json::Arr(vec![
                        Json::Arr(vec![r("p"), r("p")]),
                        Json::Arr(vec![r("q"), r("q")]),
                    ]),
                    "reserves" => Json::Arr(vec![Json::Arr(vec![r("e"), r("e")])]),
                    _ => a["value"].clone(),
                };
                a.insert("value".into(), value);
            }
            atoms.push(Json::Obj(a));
        }
    }
    let remove = match mode {
        "missing_map" => Some("m-states"),
        "missing_arrow_map" => Some("m-reserves"),
        "missing_to" => Some("m-to"),
        "missing_owner" => Some("p-owner"),
        "missing_field" => Some("r-free"),
        _ => None,
    };
    if let Some(id) = remove {
        atoms.retain(|a| {
            let Json::Obj(a) = a else { panic!() };
            a["id"] != Json::str(id)
        });
    }
    if mode == "bad_endpoint" {
        for a in atoms.iter_mut() {
            let Json::Obj(a) = a else { panic!() };
            if a["id"] == Json::str("f-to") {
                a.insert("value".into(), r("r"));
            }
        }
    }
    assert!(matches!(
        mode,
        "normal"
            | "bad_endpoint"
            | "missing_map"
            | "missing_arrow_map"
            | "missing_to"
            | "missing_owner"
            | "missing_field"
    ));
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
