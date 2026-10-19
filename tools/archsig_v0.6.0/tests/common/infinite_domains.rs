use archsig as fixture_archsig;
use archsig::{definition::check_definitions, observed::input::InputSources};
#[allow(dead_code)]
mod fields {
    use super::fixture_archsig as archsig;
    include!("affine_field_chains.rs");
}
pub fn input(script: &str, number: &str, omitted: &[&str], revision: &str) -> InputSources {
    let original = fields::input(script, number, omitted, revision);
    let old = check_definitions(&[("definition0", original.definitions()[0].bytes())]).unwrap();
    let definitions = std::str::from_utf8(original.definitions()[0].bytes()).unwrap();
    let marker = "\"declarations\":[";
    assert_eq!(definitions.matches(marker).count(), 1);
    let extra = r#"{"kind":"data","name":"Paths.Tree","meaning":"有限木。","constructors":[{"name":"End","arguments":[],"meaning":"葉。"},{"name":"Next","arguments":[["Data","Paths.Tree"]],"meaning":"後続の木。"}]},{"kind":"data","name":"Paths.Infinite","meaning":"整数を持つ値。","constructors":[{"name":"Amount","arguments":["Z"],"meaning":"整数成分。"}]},"#;
    let definitions = definitions
        .replacen(marker, &format!("{marker}{extra}"), 1)
        .into_bytes();
    let checked = check_definitions(&[("definition0", &definitions)]).unwrap();
    let old_digest = &old.vocabularies["Paths"].digest;
    let new_digest = &checked.vocabularies["Paths"].digest;
    let law = std::str::from_utf8(original.law().bytes())
        .unwrap()
        .replace(old_digest, new_digest);
    let map = std::str::from_utf8(original.archmap().bytes())
        .unwrap()
        .replace(old_digest, new_digest);
    InputSources::from_bytes(vec![definitions], law.into_bytes(), map.into_bytes())
}
