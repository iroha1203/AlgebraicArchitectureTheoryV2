pub fn input(
    body: &str,
    field_type: &str,
    known: Option<&str>,
) -> archsig_input::input::InputSources {
    with_parts(&[("v", false, "v")], body, field_type, known)
}
pub fn with_parts(
    parts: &[(&str, bool, &str)],
    body: &str,
    field_type: &str,
    known: Option<&str>,
) -> archsig_input::input::InputSources {
    let original = super::repair_problem_data::sources(parts, body);
    let definition = std::str::from_utf8(original.definitions()[0].bytes()).unwrap();
    let old =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let declaration = format!(
        r#""meaning":"Root","parameters":[],"fields":[{{"name":"h","type":{field_type},"meaning":"Input"}},{{"name":"z","type":"Bool","meaning":"Additional input"}}]"#
    );
    let definition = definition.replace(
        r#""meaning":"Root","parameters":[],"fields":[]"#,
        &declaration,
    );
    let new =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let old = &old.vocabularies()["Pattern"].digest;
    let new = &new.vocabularies()["Pattern"].digest;
    let law = std::str::from_utf8(original.law().bytes())
        .unwrap()
        .replace(old, new);
    let mut map = std::str::from_utf8(original.archmap().bytes())
        .unwrap()
        .replace(old, new);
    if let Some(known) = known {
        map=map.replace(r#""atoms":["#,&format!(r#""atoms":[{{"id":"h","subject":"root","field":"Pattern.Root.h","value":{known},"origin":"model"}},"#));
    }
    archsig_input::input::InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
