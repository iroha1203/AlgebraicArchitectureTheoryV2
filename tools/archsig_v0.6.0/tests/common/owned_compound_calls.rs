use archsig as fixture_archsig;
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_calls.rs");
}
use archsig::observed::input::InputSources;

pub const SCRIPT: &str = r#"
view ccAccept(a:System,b:System,x:(State[a],Option<List<State[b]>>),ys:Set<State[a]>,e:Option<Reserve[a]>):Bool=true;
view ccParameter(a:System,b:System,p:State,q:State,r:State,s:State,e:Reserve):Bool=ccAccept(a,b,(p,some(list<State>[r,s,r])),set<State>{p,q,p},some(e));
view ccNarrow(a:System,b:System,p:State,q:State,r:State,e:Reserve):(List<State[a]>,Option<Reserve[a]>,Set<State[b]>)=(list<State>[q,p,q],some(e),set<State>{r});
view ccReturned(a:System,b:System,p:State,q:State,r:State,e:Reserve):(List<State>,Option<Reserve>,Set<State>)=ccNarrow(a,b,p,q,r,e);
view ccEmptyAccept(a:System,x:Option<State[a]>,xs:List<State[a]>,ys:Set<State[a]>):Z=0;
view ccEmpty(a:System):Z=ccEmptyAccept(a,none<State>,list<State>[],set<State>{});
view ccEmptyReturn(a:System):(Option<State[a]>,List<State[a]>,Set<State[a]>)=(none<State>,list<State>[],set<State>{});
view ccEmptyReturned(a:System):(Option<State>,List<State>,Set<State>)=ccEmptyReturn(a);
view ccRead(a:System,x:List<State[a]>,s:State):Z=s.free;
view ccSkipped(a:System,p:State,s:State):Z=ccRead(a,list<State>[p],s);
view ccShift(a:System,x:Option<List<State[a]>>,z:Z):Z=z+0;
law required ccAffine(a:System,p:State,z:Z):ccShift(a,some(list<State>[p,p]),z)=z;
view ccIgnore(x:(List<State>,Option<Reserve>,Set<State>)):Bool=true;
view ccIgnored(a:System,b:System,p:State,q:State,r:State,e:Reserve):Bool=ccIgnore(ccNarrow(a,b,p,q,r,e));
view ccMissing(a:System,p:State):Z=let bad=narrow(a,p) in ccEmptyAccept(a,some(bad),list<State>[],set<State>{});
view ccSet(a:System,x:Set<State[a]>):Set<State> = x;
view ccSetEqual(a:System,p:State,q:State):Bool=ccSet(a,set<State>{p,q,p})=ccSet(a,set<State>{q,p});
view ccSome(a:System,x:Option<State[a]>):Bool=true;
view ccUnknown(a:System,e:Reserve):Bool=ccSome(a,some(e.to));
view ccMap(a:System,m:Map<State[a],State[a]>):Bool=true;
law required ccMapBoundary(a:System,m:Map<State,State>):ccMap(a,m);
"#;

pub fn input(unknown: bool, revision: &str) -> InputSources {
    let input = base::input(unknown, true, revision);
    let law = String::from_utf8(input.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT));
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        input.archmap().bytes().to_vec(),
    )
}

pub fn missing_member_input() -> InputSources {
    use archsig::{
        canonical::Json,
        json::{JNode, JValue, parse},
    };
    fn convert(n: &JNode) -> Json {
        match &n.value {
            JValue::Bool(x) => Json::Bool(*x),
            JValue::Str(x) => Json::str(x),
            JValue::Num(x) => Json::Nat(x.parse().unwrap()),
            JValue::Arr(xs) => Json::Arr(xs.iter().map(convert).collect()),
            JValue::Obj(xs) => Json::Obj(xs.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
            JValue::Null => panic!("null"),
        }
    }
    let i = input(false, "r1");
    let mut map = convert(&parse(i.archmap().bytes()).unwrap());
    let Json::Obj(m) = &mut map else {
        panic!("map")
    };
    let Json::Arr(ss) = m.get_mut("snapshots").unwrap() else {
        panic!("snapshots")
    };
    for s in ss {
        let Json::Obj(s) = s else { panic!("snapshot") };
        if s["id"] != Json::str("v") {
            continue;
        }
        let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
            panic!("atoms")
        };
        let before = atoms.len();
        atoms.retain(|a| !matches!(a,Json::Obj(m) if m["id"]==Json::str("e-to")));
        assert_eq!(atoms.len() + 1, before);
    }
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.canonical().into_bytes(),
    )
}
