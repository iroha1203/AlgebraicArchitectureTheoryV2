// 有限なchange instanceと無限の整数parameterを区別する独立入力。
#[path = "repair_problem_data.rs"]
mod finite;
use archsig_input::input::InputSources;
pub fn input(parts: &[(&str, i64, i64, &str)], body: &str) -> InputSources {
    let tuples = parts
        .iter()
        .map(|(id, _, _, link)| (*id, false, *link))
        .collect::<Vec<_>>();
    let old = finite::sources(&tuples, body);
    let original = std::str::from_utf8(old.definitions()[0].bytes()).unwrap();
    let definition=original.replace(r#""fields":[{"name":"flag""#,r#""fields":[{"name":"x","type":"Z","meaning":"First integer"},{"name":"y","type":"Z","meaning":"Second integer"},{"name":"flag""#);
    let original =
        archsig_input::definition::check_definitions(&[("definition0", original.as_bytes())])
            .unwrap();
    let next =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let prior = &original.vocabularies()["Pattern"].digest;
    let digest = &next.vocabularies()["Pattern"].digest;
    let law = std::str::from_utf8(old.law().bytes())
        .unwrap()
        .replace(prior, digest);
    let extra=parts.iter().flat_map(|(id,x,y,_)|[("x",x),("y",y)].map(move |(field,value)|format!(r#"{{"id":"{field}-{id}","subject":"{id}","field":"Pattern.Part.{field}","value":"{value}","origin":"model"}},"#))).collect::<String>();
    let map = std::str::from_utf8(old.archmap().bytes())
        .unwrap()
        .replace(prior, digest)
        .replace(r#""atoms":["#, &format!(r#""atoms":[{extra}"#))
        .replace("Finite repair fixture", "Integer repair fixture");
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
