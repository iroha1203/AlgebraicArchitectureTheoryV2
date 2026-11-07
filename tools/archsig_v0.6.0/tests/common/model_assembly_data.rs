// 局所モデル組立ての原始入力。期待する全体モデルや写像は入力しない。
use archsig_common::{
    canonical::Json,
    json::{JNode, JValue},
};
use archsig_input::input::InputSources;
pub const ASSEMBLE: &str = "a=assemble(Assembly.fragments,on=@v/G,along=Assembly.interfaces,a=@v/A,b=@v/B,ma=@v/ma,mb=@v/mb)";
pub fn input(edit: impl FnOnce(String) -> String) -> InputSources {
    sources(
        include_bytes!("../fixtures/model-assembly.atoms.json"),
        edit(include_str!("../fixtures/model-assembly.archmap.json").to_owned()),
    )
}
fn sources(definition: &[u8], map: String) -> InputSources {
    let definitions =
        archsig_input::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &definitions.vocabularies()["Assemble"].digest;
    let law = include_str!("../fixtures/model-assembly.law").replace("@ASSEMBLE_DIGEST@", digest);
    InputSources::from_bytes(
        vec![definition.to_vec()],
        law.into_bytes(),
        map.replace("@ASSEMBLE_DIGEST@", digest).into_bytes(),
    )
}
pub fn with_second_snapshot() -> InputSources {
    input(|map| {
        let mut map = owned(&archsig_common::json::parse(map.as_bytes()).unwrap());
        let snapshots = items(fields(&mut map).get_mut("snapshots").unwrap());
        let second = snapshots[0].canonical().replace("\"v\"", "\"w\"");
        snapshots.push(owned(
            &archsig_common::json::parse(second.as_bytes()).unwrap(),
        ));
        map.canonical()
    })
}
pub fn with_term() -> InputSources {
    let mut d = owned(
        &archsig_common::json::parse(include_bytes!("../fixtures/model-assembly.atoms.json"))
            .unwrap(),
    );
    let vocabulary = &mut items(fields(&mut d).get_mut("vocabularies").unwrap())[0];
    let part = &mut items(fields(vocabulary).get_mut("declarations").unwrap())[1];
    items(fields(part).get_mut("fields").unwrap()).push(Json::obj([
        ("name", Json::str("opaque")),
        (
            "type",
            Json::Arr(vec![
                Json::str("Term"),
                Json::Arr(vec![Json::str("Z")]),
                Json::str("Z"),
            ]),
        ),
        ("meaning", Json::str("担当が保持する関数値。")),
    ]));
    let mut map = owned(
        &archsig_common::json::parse(include_bytes!("../fixtures/model-assembly.archmap.json"))
            .unwrap(),
    );
    let snapshot = &mut items(fields(&mut map).get_mut("snapshots").unwrap())[0];
    for p in ["a", "ma", "mb", "b"] {
        items(fields(snapshot).get_mut("atoms").unwrap()).push(Json::obj([
            ("id", Json::str(format!("{p}-opaque"))),
            ("subject", Json::str(p)),
            ("field", Json::str("Assemble.Part.opaque")),
            (
                "value",
                Json::obj([
                    ("params", Json::Arr(vec![Json::str("x")])),
                    ("body", Json::str("x")),
                ]),
            ),
            ("origin", Json::str("model")),
        ]));
    }
    sources(d.canonical().as_bytes(), map.canonical())
}

fn owned(n: &JNode) -> Json {
    match &n.value {
        JValue::Str(s) => Json::str(s),
        JValue::Bool(v) => Json::Bool(*v),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Arr(a) => Json::Arr(a.iter().map(owned).collect()),
        JValue::Obj(o) => Json::Obj(o.iter().map(|(k, v)| (k.clone(), owned(v))).collect()),
        JValue::Null => panic!("fixtureにnullはない"),
    }
}
fn fields(j: &mut Json) -> &mut archsig_common::canonical::JsonObject {
    let Json::Obj(f) = j else { panic!("object") };
    f
}
fn items(j: &mut Json) -> &mut Vec<Json> {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
pub fn atom(map: String, id: &str, value: Option<Json>) -> String {
    let mut map = owned(&archsig_common::json::parse(map.as_bytes()).unwrap());
    let snapshots = items(fields(&mut map).get_mut("snapshots").unwrap());
    let atoms = items(fields(&mut snapshots[0]).get_mut("atoms").unwrap());
    let index = atoms
        .iter()
        .position(|a| matches!(a,Json::Obj(f) if f.get("id")==Some(&Json::str(id))))
        .unwrap();
    if let Some(value) = value {
        fields(&mut atoms[index]).insert("value".into(), value);
    } else {
        atoms.remove(index);
    }
    map.canonical()
}

pub fn without_arrows(map: String) -> String {
    let mut map = owned(&archsig_common::json::parse(map.as_bytes()).unwrap());
    let snapshot = &mut items(fields(&mut map).get_mut("snapshots").unwrap())[0];
    items(fields(snapshot).get_mut("subjects").unwrap()).retain(|subject|
        !matches!(subject, Json::Obj(f) if ["left", "right"].iter().any(|id| f.get("id") == Some(&Json::str(*id))))
    );
    items(fields(snapshot).get_mut("atoms").unwrap()).retain(|atom|
        !matches!(atom, Json::Obj(f) if ["left", "right"].iter().any(|id| f.get("subject") == Some(&Json::str(*id))))
    );
    map.canonical()
}
