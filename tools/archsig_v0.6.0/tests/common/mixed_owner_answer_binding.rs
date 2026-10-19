use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("free_compound_answer_binding.rs");
}
pub const SCRIPT: &str = r#"
view mxOption(p:Reservations.State,q:Reservations.State):Option<(Reservations.State,Reservations.State)> =some((p,q));
view mxList(p:Reservations.State,q:Reservations.State):List<(Reservations.State,Reservations.State)> =list<(Reservations.State,Reservations.State)>[(p,q),(p,q)];
view mxSet(p:Reservations.State,q:Reservations.State):Set<(Reservations.State,Reservations.State)> =set<(Reservations.State,Reservations.State)>{(p,q),(p,q)};
view mxWrapped(p:Reservations.State,q:Reservations.State):(Unit,Option<List<(Reservations.State,Reservations.State)>>)=(unit,some(mxList(p,q)));
view mxEmpty():(Option<(Reservations.State,Reservations.State)>,List<(Reservations.State,Reservations.State)>,Set<(Reservations.State,Reservations.State)>)=(none<(Reservations.State,Reservations.State)>,list<(Reservations.State,Reservations.State)>[],set<(Reservations.State,Reservations.State)>{});
view mxConflict(p:Reservations.State,q:Reservations.State,r:Reservations.State):(Reservations.State,List<Reservations.State>)=(p,list<Reservations.State>[q,r]);
view mxMissing(p:Reservations.State,q:Reservations.State):(Reservations.State,Reservations.State)=if p.free=0 then (p,q) else (q,p);
view mxOpaque(p:Reservations.State,q:Reservations.State):(Reservations.State,Reservations.State)=if (fn(z:Z)=>z*z)=(fn(z:Z)=>z*z+0) then (p,q) else (q,p);
view mxAll(p:Reservations.State,q:Reservations.State):(Reservations.State,Reservations.State)=let k=forall z:Z.z=z in if k then (p,q) else (p,q);
view mxCompletion(p:Reservations.State,q:Reservations.State):(Reservations.State,Reservations.State)=if p.free-p.free=0 then (p,q) else (p,q);
law required mxOptionLaw(a:Reservations.System,b:Reservations.System,x:Option<(Reservations.State[a],Reservations.State[b])>,flag:Bool):x=x or flag;
law required mxListLaw(a:Reservations.System,b:Reservations.System,x:List<(Reservations.State[a],Reservations.State[b])>,flag:Bool):x=x or flag;
law required mxSetLaw(a:Reservations.System,b:Reservations.System,x:Set<(Reservations.State[a],Reservations.State[b])>,flag:Bool):x=x or flag;
law required mxTuple(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],Reservations.State[b]),flag:Bool):x=x or flag;
law required mxEmptyLaw(a:Reservations.System,b:Reservations.System,x:Option<(Reservations.State[a],Reservations.State[b])>,xs:List<(Reservations.State[a],Reservations.State[b])>,ys:Set<(Reservations.State[a],Reservations.State[b])>):true;
law required mxConflictLaw(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],List<Reservations.State[b]>)):false;
law required mxFalse(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],Reservations.State[b])):false;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
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
            JValue::Null => panic!("null fixture"),
        }
    }
    let i = base::input(
        if matches!(mode, "unknown_free_owner" | "ambiguous_free_owner") {
            "known"
        } else {
            mode
        },
        revision,
    );
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    let mut map = convert(&parse(i.archmap().bytes()).unwrap());
    if matches!(mode, "unknown_free_owner" | "ambiguous_free_owner") {
        let Json::Obj(root) = &mut map else { panic!() };
        let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
            panic!()
        };
        for snapshot in snapshots {
            let Json::Obj(s) = snapshot else { panic!() };
            let Json::Arr(atoms) = s.get_mut("atoms").unwrap() else {
                panic!()
            };
            let count = atoms.len();
            atoms.retain(|a| !matches!(a,Json::Obj(m)if m["id"]==Json::str("r-owner")));
            assert_eq!(atoms.len() + 1, count);
            if mode == "ambiguous_free_owner" {
                atoms.retain(|a| !matches!(a,Json::Obj(m)if ["m", "e", "f"].iter().any(|id| m["subject"] == Json::str(*id))));
                let Json::Arr(subjects) = s.get_mut("subjects").unwrap() else {
                    panic!()
                };
                subjects.retain(|subject| !matches!(subject, Json::Obj(m)if ["m", "e", "f"].iter().any(|id| m["id"] == Json::str(*id))));
            }
        }
    }
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
            .into_bytes(),
        map.canonical().into_bytes(),
    )
}
