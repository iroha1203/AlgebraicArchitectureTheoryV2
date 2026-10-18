use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_binding.rs");
}
pub const SCRIPT: &str = r#"
view foChild(p:State):State=p;
view foPair(p:State):(Unit,State)=(unit,p);
view foUniversal(p:State):State=let k=forall z:Z.z=z in if k then p else p;
view foCompletion(p:State):State=if p.free-p.free=0 then p else p;
view foMissing(p:State,q:State):State=if p.free=0 then p else q;
view foOpaque(p:State,q:State):State=if adOpaque() then p else q;
law required foEq(a:System,p:State[a]):p=p;
law required foEmpty(a:System,p:State[a],r:Reserve[a]):false;
law required foFalse(a:System,p:State[a]):false;
law required foMixed(a:System,p:State[a],q:State[a],flag:Bool):q=q or flag;
"#;
pub fn input(unknown: bool, second: bool, revision: &str) -> InputSources {
    let i = base::input(unknown, second, revision);
    let l = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    assert_eq!(l.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        l.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
