use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("answer_bindings.rs");
}
pub const SCRIPT: &str = r#"
view adOpaque():Bool=(fn(z:Z)=>z*z)=(fn(z:Z)=>z*z+0);
view adMissing(p:Reservations.State):Z=p.free;
view adBoth(x:Z,b:Bool):Z=if b then x else x+1;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::input_mode(mode, revision);
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    let anchor = base::SCRIPT.replace("VALUE_TUPLE", base::PACK);
    assert_eq!(law.matches(&anchor).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(&anchor, &(anchor.clone() + SCRIPT))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
