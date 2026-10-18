use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("answer_projections.rs");
}
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::input(mode, revision);
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    let extra = r#"
view acRoot(a:Reservations.System):Reservations.System=a;
view acMix(x:Z,y:Z,b:Bool):Z=if b then x+y else x+y;
view acNestedNone():List<Option<List<Z>>> =list<Option<List<Z>>>[none<List<Z>>];
"#;
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + extra))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
pub fn tree_input(missing: bool, revision: &str) -> InputSources {
    base::tree_input(missing, revision)
}
