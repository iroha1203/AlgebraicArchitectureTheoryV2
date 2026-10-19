use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("answer_dependent_family.rs");
}
pub const SCRIPT: &str = r#"
view obChild(p:State):State=p;
view obPair(a:System,p:State):(System,State)=(a,p);
view obUse(a:System,p:State[a]):State=p;
view obCall(a:System,p:State[a]):State=obUse(a,p);
view obTyped(a:System,p:State[a]):State[a]=p;
view obEmpty():List<State> =list<State>[];
view obOpaqueOwner(a:System,b:System):System=if adOpaque() then a else b;
law required obEq(a:System,p:State[a]):p=p;
law required obFalse(a:System,p:State[a]):false;
law required obFinite(a:System,p:State[a],flag:Bool):flag;
law required obFamily(a:System,p:State[a],f:Option<State[a]>):f=f;
"#;
pub fn input(unknown: bool, second: bool, revision: &str) -> InputSources {
    let input = base::input(unknown, second, revision);
    let law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
            .into_bytes(),
        input.archmap().bytes().to_vec(),
    )
}

pub fn completion_input(mode: &str, revision: &str) -> InputSources {
    use archsig::{
        canonical::Json,
        json::{JNode, JValue, parse},
    };
    fn convert(n: &JNode) -> Json {
        match &n.value {
            JValue::Str(s) => Json::str(s),
            JValue::Bool(b) => Json::Bool(*b),
            JValue::Num(n) => Json::Nat(n.parse().unwrap()),
            JValue::Arr(xs) => Json::Arr(xs.iter().map(convert).collect()),
            JValue::Obj(xs) => Json::Obj(xs.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
            JValue::Null => panic!(),
        }
    }
    fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
        let Json::Obj(m) = j else { panic!() };
        &m[k]
    }
    let input = input(true, false, revision);
    let mut map = convert(&parse(input.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let Json::Obj(snapshot) = &mut snapshots[0] else {
        panic!()
    };
    if mode == "single" {
        let Json::Arr(subjects) = snapshot.get_mut("subjects").unwrap() else {
            panic!()
        };
        subjects.retain(|s| {
            ["A", "p", "q"]
                .iter()
                .any(|id| f(s, "id") == &Json::str(*id))
        });
        let Json::Arr(atoms) = snapshot.get_mut("atoms").unwrap() else {
            panic!()
        };
        atoms.retain(|a| f(a, "subject") == &Json::str("q"));
    } else if mode == "forceA" || mode == "forceB" {
        let Json::Arr(subjects) = snapshot.get_mut("subjects").unwrap() else {
            panic!()
        };
        subjects.push(Json::obj([
            ("id", Json::str("m")),
            ("type", Json::str("Reservations.Migration")),
            ("origin", Json::str("model")),
        ]));
        let Json::Arr(atoms) = snapshot.get_mut("atoms").unwrap() else {
            panic!()
        };
        let r = |id: &str| Json::Arr(vec![Json::str("v"), Json::str(id)]);
        let (from, to, rows) = if mode == "forceA" {
            ("A", "B", vec![("p", "r"), ("q", "s")])
        } else {
            ("B", "A", vec![("p", "q"), ("r", "q"), ("s", "q")])
        };
        for (field, value) in [
            ("from", r(from)),
            ("to", r(to)),
            (
                "states",
                Json::Arr(
                    rows.into_iter()
                        .map(|(a, b)| Json::Arr(vec![r(a), r(b)]))
                        .collect(),
                ),
            ),
            ("reserves", Json::Arr(vec![])),
        ] {
            atoms.push(Json::obj([
                ("id", Json::str(format!("migration-{field}"))),
                ("subject", Json::str("m")),
                (
                    "field",
                    Json::str(format!("Reservations.Migration.{field}")),
                ),
                ("value", value),
                ("origin", Json::str("model")),
            ]));
        }
    } else {
        assert_eq!(mode, "ambiguous");
    }
    let script = r#"
view obPacked(p:State):(State,List<Option<State>>,Set<State>)=(p,list<Option<State>>[some(p),none<State>],set<State>{p});
view obPackUse(a:System,x:(State[a],List<Option<State[a]>>,Set<State[a]>)):Bool=true;
view obTable(m:Migration):Map<State,State> =m.states;
view obMapUse(a:System,b:System,x:Map<State[a],State[b]>):Bool=true;
"#;
    let law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.replace(SCRIPT, &format!("{SCRIPT}{script}"))
            .into_bytes(),
        map.canonical().into_bytes(),
    )
}
