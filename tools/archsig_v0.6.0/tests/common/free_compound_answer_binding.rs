use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("compound_owned_binding.rs");
}
pub const SCRIPT: &str = r#"
view fcMapAll(m:Reservations.Migration):Map<Reservations.State,Reservations.State> =let k=forall z:Z.z=z in if k then m.states else m.states;
view fcMapCompletion(m:Reservations.Migration,p:Reservations.State):Map<Reservations.State,Reservations.State> =if p.free-p.free=0 then m.states else m.states;
law required fcDomain(a:Reservations.System,x:Map<Reservations.State[a],Reservations.State>):true;
law required fcBool(x:Bool):x=x;
law required fcOption(a:Reservations.System,x:Option<Reservations.State[a]>,flag:Bool):x=x or flag;
law required fcList(a:Reservations.System,x:List<Reservations.State[a]>,flag:Bool):x=x or flag;
law required fcSet(a:Reservations.System,x:Set<Reservations.State[a]>,flag:Bool):x=x or flag;
law required fcTuple(a:Reservations.System,b:Reservations.System,x:(Reservations.State[a],Option<List<Reservations.State[b]>>),flag:Bool):x=x or flag;
law required fcNested(a:Reservations.System,b:Reservations.System,x:Option<List<Set<((Reservations.State[a],Z),Option<(Reservations.State[b],Q)>)>>>,flag:Bool):x=x or flag;
law required fcMap(a:Reservations.System,b:Reservations.System,x:Map<Reservations.State[a],Reservations.State[b]>,flag:Bool):x=x or flag;
law required fcMapWrapped(a:Reservations.System,b:Reservations.System,x:Option<List<Map<Reservations.State[a],Reservations.State[b]>>>,flag:Bool):x=x or flag;
law required fcFalse(a:Reservations.System,x:List<Reservations.State[a]>):false;
law required fcEmpty(a:Reservations.System,x:Option<Reservations.State[a]>,xs:List<Reservations.State[a]>,ys:Set<Reservations.State[a]>):true;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::input(mode, revision);
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
