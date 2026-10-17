use archsig as fixture_archsig;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("map_application.rs");
}
use archsig::{
    canonical::Json,
    json::{JNode, JValue, parse},
    observed::input::InputSources,
};
pub const SCRIPT: &str = r#"
view mcMissingZero(p:Reservations.State):Z=p.free-p.free;
view mcObserved(a:Reservations.System,b:Reservations.System,m:Reservations.Migration,p:Reservations.State):Bool=let zero=p.free-p.free in mcParameter(a,b,m);
view mcAccept(a:Reservations.System,b:Reservations.System,f:Map<Reservations.State[a],Reservations.State[b]>):Bool=true;
view mcParameter(a:Reservations.System,b:Reservations.System,m:Reservations.Migration):Bool=mcAccept(a,b,m.states);
view mcReturn(a:Reservations.System,b:Reservations.System,f:Map<Reservations.State,Reservations.State>):Map<Reservations.State[a],Reservations.State[b]> =f;
view mcIgnore(f:Map<Reservations.State,Reservations.State>):Bool=true;
view mcReturned(a:Reservations.System,b:Reservations.System,m:Reservations.Migration):Bool=mcIgnore(mcReturn(a,b,m.states));
view mcRead(a:Reservations.System,b:Reservations.System,m:Reservations.Migration,x:Reservations.State):Reservations.State=mcReturn(a,b,m.states)(x);
view mcDomain(a:Reservations.System,f:Map<Reservations.State[a],Reservations.State>):Bool=true;
view mcImage(b:Reservations.System,f:Map<Reservations.State,Reservations.State[b]>):Bool=true;
view mcDomainUse(a:Reservations.System,m:Reservations.Migration):Bool=mcDomain(a,m.states);
view mcImageUse(b:Reservations.System,m:Reservations.Migration):Bool=mcImage(b,m.states);
view mcNested(a:Reservations.System,b:Reservations.System,fs:(Option<List<Map<Reservations.State[a],Reservations.State[b]>>>,Set<Map<Reservations.State[a],Reservations.State[b]>>)):Bool=true;
view mcNestedUse(a:Reservations.System,b:Reservations.System,m:Reservations.Migration):Bool=mcNested(a,b,(some(list<Map<Reservations.State,Reservations.State>>[m.states,m.states]),set<Map<Reservations.State,Reservations.State>>{m.states,m.states}));
view mcKeep(a:Reservations.System,b:Reservations.System,f:Map<Reservations.State[a],Reservations.State[b]>,z:Z):Z=z+0;
law required mcAffine(a:Reservations.System,b:Reservations.System,m:Reservations.Migration,z:Z):mcKeep(a,b,m.states,z)=z;
law required mcFamily(a:Reservations.System,b:Reservations.System,f:Map<Reservations.State[a],Reservations.State[b]>):mcAccept(a,b,f);
view mcIgnored(a:Reservations.System,b:Reservations.System,m:Reservations.Migration):Bool=mcIgnoreBool(mcParameter(a,b,m));
view mcIgnoreBool(x:Bool):Bool=true;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::owned_revision(
        if mode == "empty" {
            "empty"
        } else if mode == "missing" {
            "missing"
        } else {
            "known"
        },
        revision,
    );
    let law = String::from_utf8(i.law().bytes().to_vec())
        .unwrap()
        .replace(
            base::OWNED_SCRIPT,
            &(base::OWNED_SCRIPT.to_owned() + SCRIPT),
        );
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
    let mut map = convert(&parse(i.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    if mode == "unknown_owner" || mode == "stop" {
        let Json::Obj(s) = &mut snapshots[0] else {
            panic!()
        };
        let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
            panic!()
        };
        let before = atoms.len();
        let omitted = if mode == "stop" { "p-free" } else { "p-owner" };
        atoms.retain(|a| !matches!(a,Json::Obj(m) if m["id"]==Json::str(omitted)));
        assert_eq!(atoms.len() + 1, before);
    }
    let mut other = snapshots[0].clone();
    fn shift(j: &mut Json) {
        match j {
            Json::Obj(m) => {
                for v in m.values_mut() {
                    shift(v)
                }
            }
            Json::Arr(v) => {
                if v.len() == 2 && v[0] == Json::str("v") {
                    v[0] = Json::str("w");
                } else {
                    for v in v {
                        shift(v)
                    }
                }
            }
            _ => {}
        }
    }
    shift(&mut other);
    let Json::Obj(s) = &mut other else { panic!() };
    s.insert("id".into(), Json::str("w"));
    snapshots.push(other);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
