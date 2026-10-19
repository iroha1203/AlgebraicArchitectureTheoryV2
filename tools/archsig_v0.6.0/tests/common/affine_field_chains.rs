use archsig as fixture_archsig;
use archsig::{
    canonical::Json,
    definition::check_definitions,
    json::{JNode, JValue},
    observed::input::InputSources,
};
#[allow(dead_code)]
mod paths {
    use super::fixture_archsig as archsig;
    include!("internal_paths.rs");
}
fn json(n: &JNode) -> Json {
    match &n.value {
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Str(s) => Json::str(s),
        JValue::Arr(xs) => Json::Arr(xs.iter().map(json).collect()),
        JValue::Obj(xs) => Json::Obj(xs.iter().map(|(k, v)| (k.clone(), json(v))).collect()),
        JValue::Null => panic!("このfixtureにnullはない"),
    }
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(xs) = j else { panic!("object") };
    &xs[k]
}
fn fm<'a>(j: &'a mut Json, k: &str) -> &'a mut Json {
    let Json::Obj(xs) = j else { panic!("object") };
    xs.get_mut(k).unwrap()
}
fn am(j: &mut Json) -> &mut Vec<Json> {
    let Json::Arr(xs) = j else { panic!("array") };
    xs
}
pub fn input(script: &str, number: &str, omitted: &[&str], revision: &str) -> InputSources {
    assert!(matches!(number, "Z" | "Q"));
    let original = paths::input("normal", revision);
    let mut definitions = json(&archsig::json::parse(original.definitions()[0].bytes()).unwrap());
    if number == "Q" {
        let declarations = am(fm(
            &mut am(fm(&mut definitions, "vocabularies"))[0],
            "declarations",
        ));
        let node = declarations
            .iter_mut()
            .find(|d| f(d, "name") == &Json::str("Paths.Node"))
            .unwrap();
        let mark = am(fm(node, "fields"))
            .iter_mut()
            .find(|d| f(d, "name") == &Json::str("mark"))
            .unwrap();
        *fm(mark, "type") = Json::str("Q");
    }
    let bytes = definitions.canonical().into_bytes();
    let checked = check_definitions(&[("definition0", &bytes)]).unwrap();
    let digest = &checked.vocabularies["Paths"].digest;
    let old = check_definitions(&[("definition0", original.definitions()[0].bytes())]).unwrap();
    let law = std::str::from_utf8(original.law().bytes()).unwrap();
    let marker = "view unused(x:Unused):Bool=true;";
    assert_eq!(law.matches(marker).count(), 1);
    let law = law
        .replace(marker, script)
        .replace(&old.vocabularies["Paths"].digest, digest);
    let mut map = json(&archsig::json::parse(original.archmap().bytes()).unwrap());
    *fm(&mut am(fm(&mut map, "vocabularies"))[0], "digest") = Json::str(digest);
    for snapshot in am(fm(&mut map, "snapshots")) {
        let selected = f(snapshot, "id") == &Json::str("v");
        let atoms = am(fm(snapshot, "atoms"));
        if selected {
            atoms.retain(|a| !omitted.iter().any(|id| f(a, "id") == &Json::str(*id)));
        }
        if number == "Q" {
            for atom in atoms
                .iter_mut()
                .filter(|a| f(a, "field") == &Json::str("Paths.Node.mark"))
            {
                let value = f(atom, "value").clone();
                let denominator = if value == Json::str("9") { "2" } else { "3" };
                *fm(atom, "value") = Json::Arr(vec![value, Json::str(denominator)]);
            }
        }
    }
    InputSources::from_bytes(vec![bytes], law.into_bytes(), map.canonical().into_bytes())
}
pub const SCRIPT: &str = r#"
view current(n:Node):Bool=forall z:Z . n.link.mark+z=z+n.link.mark;
law required chain(n:Node,z:Z):n.link.mark+z=z+n.link.mark;
"#;
