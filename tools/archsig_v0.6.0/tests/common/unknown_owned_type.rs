use archsig as fixture_archsig;
use archsig::{
    canonical::Json,
    json::{JNode, JValue, parse},
    observed::input::InputSources,
};
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("unknown_map_domain.rs");
}
pub const SCRIPT: &str = r#"
view typeEvery(a:Root,b:Root):Bool=forall f:Map<Item[a],Item[b]> . f=f;
view typeAny(a:Root,b:Root):Bool=exists f:Map<Item[a],Item[b]> . true;
view typeFalse(a:Root,b:Root):Bool=forall f:Map<Item[a],Item[b]> . false;
view typeOption(a:Root,b:Root):Bool=forall f:Option<Map<Item[a],Item[b]>> . f=f;
view typeTuple(a:Root,b:Root):Bool=forall f:(Unit,Map<Item[a],Item[b]>) . f=f;
view typeSet(a:Root,b:Root):Bool=forall f:Set<Map<Item[a],Item[b]>> . f=f;
view typeRef(a:Root):Bool=forall p:Item[a] . p=p;
view typeLexical(h:Holder):Bool=let a=h.owner in forall f:Map<Item[a],Item[a]> . f=f;
view typeCaptured(a:Root):Bool=forall f:Map<Item[a],Item[a]> . f=f;
view typeCall(h:Holder):Bool=typeCaptured(h.owner);
"#;
fn convert(n: &JNode) -> Json {
    match &n.value {
        JValue::Bool(v) => Json::Bool(*v),
        JValue::Str(v) => Json::str(v),
        JValue::Num(v) => Json::Nat(v.parse().unwrap()),
        JValue::Arr(v) => Json::Arr(v.iter().map(convert).collect()),
        JValue::Obj(v) => Json::Obj(v.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
        JValue::Null => panic!("null"),
    }
}
pub fn input(mode: &str, revision: &str) -> InputSources {
    assert!(matches!(mode, "plain" | "two" | "lexical"));
    let i = base::input("varying", revision);
    let mut map = convert(&parse(i.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    assert_eq!(snapshots.len(), 1);
    let Json::Obj(s) = &mut snapshots[0] else {
        panic!()
    };
    if mode != "lexical" {
        let Json::Arr(subjects) = s.get_mut("subjects").unwrap() else {
            panic!()
        };
        let before = subjects.len();
        subjects.retain(|x| !matches!(x,Json::Obj(o)if o["id"]==Json::str("h")));
        assert_eq!(subjects.len() + 1, before);
        if mode == "two" {
            subjects.push(Json::obj([
                ("id", Json::str("q")),
                ("type", Json::str("MapCall.Item")),
                ("origin", Json::str("model")),
            ]));
        }
        let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
            panic!()
        };
        assert_eq!(atoms.len(), 1);
        atoms.clear();
    }
    let law = String::from_utf8(i.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT));
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
#[allow(dead_code)]
mod numeric {
    include!("finite_map.rs");
}
pub fn numeric_input() -> InputSources {
    let d = archsig::definition::check_definitions(&[(
        "definition0",
        numeric::OWNED_DEFINITIONS.as_bytes(),
    )])
    .unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    let law=numeric::owned_law(digest).replace(numeric::OWNED_SCRIPT,&(numeric::OWNED_SCRIPT.to_owned()+"view numeric(a:System,b:System,p:State):Bool=forall f:Map<State[a],State[b]> . f=f and p.free-p.free=0;"));
    let map = numeric::owned_archmap(true)
        .lines()
        .filter(|l| !l.contains("\"id\": \"p-free\""))
        .collect::<Vec<_>>()
        .join("\n");
    InputSources::from_bytes(
        vec![numeric::OWNED_DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
