// 文書から独立した原始入力と、選択根ごとの評価を比べるLaw。
use archsig::observed::input::InputSources;
pub const EXTRA: &str = r#"
view smallStates():Bool=forall s:State . s.free+s.held=2;
view no():Bool=false;
law required small(s:State):s.free+s.held=2;
law required roots(x:System):x=x;
law required symbolic(s:State,z:Z):z=z;
"#;
pub fn input(extra: &str, map: Option<&str>) -> InputSources {
    let law = include_str!("../fixtures/public-compose.law").replace(
        "  view holdings",
        &format!("{EXTRA}\n{extra}\n  view holdings"),
    );
    InputSources::from_bytes(
        vec![include_bytes!("../fixtures/reservations.atoms.json").to_vec()],
        law.into_bytes(),
        map.unwrap_or(include_str!(
            "../fixtures/configuration-operation.archmap.json"
        ))
        .as_bytes()
        .to_vec(),
    )
}
pub const MAP: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";

// 原始事実だけを変える負例・別snapshot。期待値を出力から作らない。
pub fn owned(node: &archsig::json::JNode) -> archsig::canonical::Json {
    use archsig::{canonical::Json, json::JValue};
    match &node.value {
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Str(s) => Json::str(s),
        JValue::Arr(a) => Json::Arr(a.iter().map(owned).collect()),
        JValue::Obj(o) => Json::Obj(o.iter().map(|(k, v)| (k.clone(), owned(v))).collect()),
        JValue::Null => panic!("fixtureにnullはない"),
    }
}
pub fn field<'a>(
    j: &'a mut archsig::canonical::Json,
    name: &str,
) -> &'a mut archsig::canonical::Json {
    let archsig::canonical::Json::Obj(o) = j else {
        panic!("object")
    };
    o.get_mut(name).unwrap()
}
pub fn changed_map(change: impl FnOnce(&mut archsig::canonical::Json)) -> String {
    let mut j = owned(
        &archsig::json::parse(include_bytes!(
            "../fixtures/configuration-operation.archmap.json"
        ))
        .unwrap(),
    );
    change(&mut j);
    j.canonical()
}
pub fn atoms(j: &mut archsig::canonical::Json) -> &mut Vec<archsig::canonical::Json> {
    use archsig::canonical::Json;
    let Json::Arr(s) = field(j, "snapshots") else {
        panic!("snapshots")
    };
    let Json::Arr(a) = field(&mut s[0], "atoms") else {
        panic!("atoms")
    };
    a
}
pub fn remove_atom(id: &str) -> String {
    changed_map(|j| {
        atoms(j).retain(|a|!matches!(a,archsig::canonical::Json::Obj(o) if o.get("id")==Some(&archsig::canonical::Json::str(id))))
    })
}
