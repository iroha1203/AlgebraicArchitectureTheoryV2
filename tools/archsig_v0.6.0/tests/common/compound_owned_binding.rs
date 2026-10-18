use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_map_calls.rs");
}
pub const SCRIPT: &str = r#"
view cbOwner(a:Reservations.System):Reservations.System=a;
view cbUniversalOwner(a:Reservations.System):Reservations.System=let k=forall z:Z.z=z in if k then a else a;
view cbCompletionOwner(a:Reservations.System,p:Reservations.State):Reservations.System=if p.free-p.free=0 then a else a;
view cbOption(p:Reservations.State):Option<Reservations.State> =some(p);
view cbNone():Option<Reservations.State> =none<Reservations.State>;
view cbList(p:Reservations.State,q:Reservations.State):List<Reservations.State> =list<Reservations.State>[q,p,q];
view cbSet(p:Reservations.State,q:Reservations.State):Set<Reservations.State> =set<Reservations.State>{q,p,q};
view cbWrapped(p:Reservations.State,q:Reservations.State):(Unit,List<Reservations.State>)=(unit,list<Reservations.State>[q,p,q]);
view cbTuple(p:Reservations.State,q:Reservations.State):(Reservations.State,Option<List<Reservations.State>>)=(p,some(list<Reservations.State>[q,q]));
view cbNested(p:Reservations.State,q:Reservations.State):Option<List<Set<((Reservations.State,Z),Option<(Reservations.State,Q)>)>>> =some(list<Set<((Reservations.State,Z),Option<(Reservations.State,Q)>)>>[set<((Reservations.State,Z),Option<(Reservations.State,Q)>)>{((p,0),some((q,rat(1,2))))}]);
view cbTypedList(a:Reservations.System,p:Reservations.State[a]):List<Reservations.State[a]> =list<Reservations.State>[p];
view cbMissing(p:Reservations.State):List<Reservations.State> =if p.free=0 then list<Reservations.State>[p] else list<Reservations.State>[];
view cbOpaque(p:Reservations.State,q:Reservations.State):List<Reservations.State> =if (fn(z:Z)=>z*z)=(fn(z:Z)=>z*z+0) then list<Reservations.State>[p] else list<Reservations.State>[q];
view cbEmpty():(Option<Reservations.State>,List<Reservations.State>,Set<Reservations.State>)=(none<Reservations.State>,list<Reservations.State>[],set<Reservations.State>{});
view cbOptionUse(a:Reservations.System,x:Option<Reservations.State[a]>):Option<Reservations.State> =x;
view cbListUse(a:Reservations.System,x:List<Reservations.State[a]>):List<Reservations.State> =x;
view cbSetUse(a:Reservations.System,x:Set<Reservations.State[a]>):Set<Reservations.State> =x;
view cbTupleUse(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],Option<List<Reservations.State[b]>>)):(Reservations.State,Option<List<Reservations.State>>)=x;
view cbReverseUse(b:Reservations.System,a:Reservations.System,x:(Reservations.State[a],Option<List<Reservations.State[b]>>)):(Reservations.State,Option<List<Reservations.State>>)=x;
view cbNestedUse(a:Reservations.System,b:Reservations.System,x:Option<List<Set<((Reservations.State[a],Z),Option<(Reservations.State[b],Q)>)>>>):Option<List<Set<((Reservations.State,Z),Option<(Reservations.State,Q)>)>>> =x;
view cbEmptyUse(a:Reservations.System,x:Option<Reservations.State[a]>,xs:List<Reservations.State[a]>,ys:Set<Reservations.State[a]>):Z=0;
view cbCall(a:Reservations.System,x:List<Reservations.State[a]>):List<Reservations.State> =cbListUse(a,x);
view cbMap(m:Reservations.Migration):Map<Reservations.State,Reservations.State> =m.states;
view cbMapUse(a:Reservations.System,b:Reservations.System,x:Map<Reservations.State[a],Reservations.State[b]>):Map<Reservations.State,Reservations.State> =x;
view cbMapWrapped(m:Reservations.Migration):Option<List<Map<Reservations.State,Reservations.State>>> =some(list<Map<Reservations.State,Reservations.State>>[m.states,m.states]);
view cbMapWrappedUse(a:Reservations.System,b:Reservations.System,x:Option<List<Map<Reservations.State[a],Reservations.State[b]>>>):Option<List<Map<Reservations.State,Reservations.State>>> =x;
law required cbFamily(a:Reservations.System,x:List<Reservations.State[a]>,f:Option<Reservations.State[a]>):f=f;
law required cbFalse(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],Option<List<Reservations.State[b]>>),flag:Bool):false;
law required cbEq(a:Reservations.System,b:Reservations.System,x:Map<Reservations.State[a],Reservations.State[b]>):x=x;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
    let input = base::input(mode, revision);
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
