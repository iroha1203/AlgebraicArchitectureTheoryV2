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
