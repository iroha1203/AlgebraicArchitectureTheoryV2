use archsig as fixture_archsig;
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_compound_family.rs");
}
use archsig::{
    canonical::Json,
    json::{JNode, JValue, parse},
    observed::input::InputSources,
};

pub const SCRIPT: &str = r#"
view accept(a:System,s:State[a]):Bool=true;
view parameter(a:System,s:State):Bool=accept(a,s);
view narrow(a:System,s:State):State[a]=s;
view returned(a:System,s:State):State=narrow(a,s);
view both(a:System,s:State[a]):State[a]=s;
view nested(a:System,s:State):State=both(a,narrow(a,s));
view read(a:System,s:State[a]):Z=s.free;
view skipped(a:System,s:State):Z=read(a,s);
view arrowAccept(a:System,e:Reserve[a]):Bool=true;
view arrowParameter(a:System,e:Reserve):Bool=arrowAccept(a,e);
view arrowNarrow(a:System,e:Reserve):Reserve[a]=e;
view arrowReturned(a:System,e:Reserve):Reserve=arrowNarrow(a,e);
view quantified(a:System):Bool=forall s:State[a].accept(a,s);
view fieldOwner(s:State):Bool=accept(s.owner,s);
view shifted(a:System,s:State[a],z:Z):Z=z+0;
law required affineCall(a:System,s:State,z:Z):shifted(a,s,z)=z;
view mixedReturn(a:System,s:State,z:Z):State[a]=s;
law required affineReturn(a:System,s:State,z:Z):mixedReturn(a,s,z)=s;
view plainAdd(x:Z):Z=x+1;
view plainCaller():Z=let n=plainAdd(3) in n+1;
view seed():Z=1;
law required prior():false;
"#;
fn convert(n: &JNode) -> Json {
    match &n.value {
        JValue::Bool(x) => Json::Bool(*x),
        JValue::Str(x) => Json::str(x),
        JValue::Num(x) => Json::Nat(x.parse().unwrap()),
        JValue::Arr(x) => Json::Arr(x.iter().map(convert).collect()),
        JValue::Obj(x) => Json::Obj(x.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
        JValue::Null => panic!("fixtureにnullはない"),
    }
}
pub fn input(unknown: bool, second: bool, revision: &str) -> InputSources {
    let input = base::input(unknown, second, revision);
    let law = String::from_utf8(input.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, SCRIPT);
    let mut map = convert(&parse(input.archmap().bytes()).unwrap());
    if !unknown {
        let Json::Obj(m) = &mut map else {
            panic!("map")
        };
        let Json::Arr(snapshots) = m.get_mut("snapshots").unwrap() else {
            panic!("snapshots")
        };
        for snapshot in snapshots {
            let Json::Obj(s) = snapshot else {
                panic!("snapshot")
            };
            let Json::Str(id) = &s["id"] else {
                panic!("id")
            };
            if id == "empty" {
                continue;
            }
            let id = id.clone();
            let Json::Arr(subjects) = s.get_mut("subjects").unwrap() else {
                panic!("subjects")
            };
            subjects.push(Json::obj([
                ("id", Json::str("e")),
                ("type", Json::str("Reservations.Reserve")),
                ("origin", Json::str("model")),
            ]));
            let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
                panic!("atoms")
            };
            for (field, target) in [("owner", "A"), ("from", "p"), ("to", "q")] {
                atoms.push(Json::obj([
                    ("id", Json::str(format!("e-{field}"))),
                    ("subject", Json::str("e")),
                    ("field", Json::str(format!("Reservations.Reserve.{field}"))),
                    ("value", Json::Arr(vec![Json::str(&id), Json::str(target)])),
                    ("origin", Json::str("model")),
                ]));
            }
        }
    }
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
