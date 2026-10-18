use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_compound_family.rs");
}
pub const SCRIPT: &str = r#"
view adOwner(a:System):System=a;
view adOwners(a:System,b:System):(System,System)=(a,b);
view adFlag():Bool=true;
view adZero():Z=0;
view adEmpty():List<System> =list<System>[];
view adMissing(p:State):Z=p.free;
view adUniversalOwner(a:System):System=let k=forall z:Z.z=z in if k then a else a;
view adCompletionOwner(a:System,p:State):System=if p.free-p.free=0 then a else a;
view adUnknownOwner(p:State):System=p.owner;
view adOpaque():Bool=(fn(z:Z)=>z*z)=(fn(z:Z)=>z*z+0);
law required adOwned(a:System,p:State[a]):p=p;
law required adFixedMember(a:System,p:State[a],flag:Bool):false;
law required adFixed(a:System,flag:Bool,f:Option<State[a]>):if flag then f=f else false;
law required adScalar(a:System,n:Z,f:Option<State[a]>):n=0;
law required adBool(a:System,flag:Bool,f:Option<State[a]>):flag;
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
