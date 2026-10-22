// relationの観測・定義・元式。期待値は各試験が独立に記述する。
use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
mod base {
    use super::fixture_archsig as archsig;
    include!("public_path_compose.rs");
}
pub use base::{C, E, F};
pub const ALIAS: &str = "alias=evaluate(Walk.step,e=@v/alias)";
pub const ALIAS_RELATION: &str = "relation aliasing(e:Hop,f:Hop) when source(path(e))=source(path(f)) and target(path(e))=target(path(f)):path(e)=path(f);";
pub fn input(extra: &str, missing: bool) -> InputSources {
    let original = base::input(false, "relation-sources");
    let law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
    let at = law.rfind('}').unwrap();
    let sources = InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        format!("{}{}{}", &law[..at], extra, &law[at..]).into_bytes(),
        original.archmap().bytes().to_vec(),
    );
    if missing {
        with_missing_guard(sources)
    } else {
        sources
    }
}

pub fn partial_domain_input(outside: bool, body: &str) -> InputSources {
    use fixture_archsig::canonical::Json;
    let original = base::visibility_input();
    let mut map = fixture_json(&fixture_archsig::json::parse(original.archmap().bytes()).unwrap());
    let Json::Arr(snapshots) = field_mut(&mut map, "snapshots") else {
        panic!()
    };
    if outside {
        let Json::Arr(subjects) = field_mut(&mut snapshots[0], "subjects") else {
            panic!()
        };
        subjects.push(Json::obj([
            ("id", Json::str("C")),
            ("type", Json::str("Reservations.System")),
            ("origin", Json::str("model")),
        ]));
    } else {
        fn to_w(value: &mut Json) {
            match value {
                Json::Str(text) if text == "v" => *text = "w".into(),
                Json::Arr(values) => values.iter_mut().for_each(to_w),
                Json::Obj(fields) => fields.values_mut().for_each(to_w),
                _ => {}
            }
        }
        let mut w = snapshots[0].clone();
        to_w(&mut w);
        let Json::Arr(atoms) = field_mut(&mut snapshots[0], "atoms") else {
            panic!()
        };
        atoms.retain(|atom| {
            let Json::Obj(fields) = atom else { panic!() };
            fields["id"] != Json::str("e-owner")
        });
        snapshots.push(w);
    }
    let parameters = if outside {
        "root:System,xs:List<State[root]>,e:Reserve"
    } else {
        "root:System,e:Reserve[root]"
    };
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replacen(
            "view route(e:Reserve)",
            &format!("relation mixed({parameters}):{body};\nview route(e:Reserve)"),
            1,
        );
    InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
fn fixture_json(node: &fixture_archsig::json::JNode) -> fixture_archsig::canonical::Json {
    use fixture_archsig::{canonical::Json, json::JValue};
    match &node.value {
        JValue::Bool(value) => Json::Bool(*value),
        JValue::Str(value) => Json::str(value),
        JValue::Num(value) => Json::Nat(value.parse().unwrap()),
        JValue::Arr(values) => Json::Arr(values.iter().map(fixture_json).collect()),
        JValue::Obj(fields) => Json::Obj(
            fields
                .iter()
                .map(|(name, value)| (name.clone(), fixture_json(value)))
                .collect(),
        ),
        JValue::Null => panic!("この原始fixtureにnullはない"),
    }
}
fn field_mut<'a>(
    node: &'a mut fixture_archsig::canonical::Json,
    name: &str,
) -> &'a mut fixture_archsig::canonical::Json {
    let fixture_archsig::canonical::Json::Obj(fields) = node else {
        panic!()
    };
    fields.get_mut(name).unwrap()
}
fn with_missing_guard(sources: InputSources) -> InputSources {
    use fixture_archsig::canonical::Json;
    assert_eq!(sources.definitions().len(), 1);
    let original = fixture_archsig::definition::check_definitions(&[(
        "definition0",
        sources.definitions()[0].bytes(),
    )])
    .unwrap();
    let old = &original.vocabularies["Paths"].digest;
    let mut definitions =
        fixture_json(&fixture_archsig::json::parse(sources.definitions()[0].bytes()).unwrap());
    let Json::Arr(vocabularies) = field_mut(&mut definitions, "vocabularies") else {
        panic!()
    };
    let Json::Arr(declarations) = field_mut(&mut vocabularies[0], "declarations") else {
        panic!()
    };
    declarations.push(Json::obj([
        ("kind", Json::str("entity")),
        ("name", Json::str("Paths.Guard")),
        ("meaning", Json::str("Pathの構成とは独立した適用条件。")),
        ("parameters", Json::Arr(vec![])),
        ("alignments", Json::Arr(vec![])),
        (
            "fields",
            Json::Arr(vec![Json::obj([
                ("name", Json::str("flag")),
                ("type", Json::str("Bool")),
                ("meaning", Json::str("未観測の適用条件。")),
            ])]),
        ),
    ]));
    let definitions = definitions.canonical().into_bytes();
    let checked =
        fixture_archsig::definition::check_definitions(&[("definition0", &definitions)]).unwrap();
    let digest = &checked.vocabularies["Paths"].digest;
    let mut map = fixture_json(&fixture_archsig::json::parse(sources.archmap().bytes()).unwrap());
    let Json::Arr(snapshots) = field_mut(&mut map, "snapshots") else {
        panic!()
    };
    let Json::Arr(subjects) = field_mut(&mut snapshots[0], "subjects") else {
        panic!()
    };
    subjects.push(Json::obj([
        ("id", Json::str("guard")),
        ("type", Json::str("Paths.Guard")),
        ("origin", Json::str("v")),
    ]));
    InputSources::from_bytes(
        vec![definitions],
        String::from_utf8(sources.law().bytes().to_vec())
            .unwrap()
            .replace(old, digest)
            .into_bytes(),
        map.canonical().replace(old, digest).into_bytes(),
    )
}
pub fn composition_refutation() -> InputSources {
    use fixture_archsig::canonical::Json;
    let script = "relation shortcut(e:Hop,f:Hop,g:Hop) when target(path(e))=source(path(f)) and source(path(e))=source(path(g)) and target(path(f))=target(path(g)):then(path(e),path(f))=path(g);";
    let sources = input(script, false);
    let mut map = fixture_json(&fixture_archsig::json::parse(sources.archmap().bytes()).unwrap());
    let Json::Arr(snapshots) = field_mut(&mut map, "snapshots") else {
        panic!()
    };
    let Json::Arr(subjects) = field_mut(&mut snapshots[0], "subjects") else {
        panic!()
    };
    subjects.retain(|subject| {
        let Json::Obj(fields) = subject else { panic!() };
        fields["id"] != Json::str("alias") && fields["id"] != Json::str("self")
    });
    let Json::Arr(atoms) = field_mut(&mut snapshots[0], "atoms") else {
        panic!()
    };
    atoms.retain(|atom| {
        let Json::Obj(fields) = atom else { panic!() };
        fields["subject"] != Json::str("alias") && fields["subject"] != Json::str("self")
    });
    InputSources::from_bytes(
        sources
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        sources.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
pub const PENDING_RELATION: &str = "relation unknown_guard(g:Guard,e:Hop,f:Hop) when g.flag and source(path(e))=source(path(f)) and target(path(e))=target(path(f)):path(e)=path(f);";
pub fn known_guard(value: bool) -> InputSources {
    use fixture_archsig::canonical::Json;
    let sources = input(PENDING_RELATION, true);
    let mut map = fixture_json(&fixture_archsig::json::parse(sources.archmap().bytes()).unwrap());
    let Json::Arr(snapshots) = field_mut(&mut map, "snapshots") else {
        panic!()
    };
    let Json::Arr(atoms) = field_mut(&mut snapshots[0], "atoms") else {
        panic!()
    };
    atoms.push(Json::obj([
        ("id", Json::str("guard-flag")),
        ("subject", Json::str("guard")),
        ("field", Json::str("Paths.Guard.flag")),
        ("value", Json::Bool(value)),
        ("origin", Json::str("v")),
    ]));
    InputSources::from_bytes(
        sources
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        sources.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
