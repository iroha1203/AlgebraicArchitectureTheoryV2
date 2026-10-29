include!("finite_law_family_data.rs");

pub fn conditional_inputs(choice: Option<&str>, body: &str) -> Arc<CheckedInputs> {
    let definition = D.replace(
        r#""fields":[{"name":"quantity""#,
        r#""fields":[{"name":"choice","type":["Ref","Family.Root"],"meaning":"選んだ根。"},{"name":"quantity""#,
    );
    let defs =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &defs.vocabularies()["Family"].digest;
    let extra=choice.map(|root|format!(r#"{{"id":"choice","subject":"q","field":"Family.Part.choice","value":["v","{root}"],"origin":"model"}},"#)).unwrap_or_default();
    let map=MAP.replace(r#""atoms":["#,&format!(r#""atoms":[{{"id":"pc","subject":"p","field":"Family.Part.choice","value":["v","root"],"origin":"model"}},{extra}"#));
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Family version \"1\" digest \"{digest}\";{body}}}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definition.into_bytes()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap(),
    )
}
