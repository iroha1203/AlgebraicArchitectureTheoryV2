use crate::input::InputSources;
mod owner_fixture {
    include!("object_view_compatibility_data.rs");
}
pub fn owner_sources(structure_only: bool) -> InputSources {
    let definitions = owner_fixture::D.replace(
        r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,
        r#"{"name":"flag","type":"Bool","meaning":"条件。"}"#,
    );
    let definitions = if structure_only {
        definitions.replace(
            r#""name":"Pattern.External","meaning":"固定外部。","parameters":[]"#,
            r#""name":"Pattern.External","meaning":"固定外部。","parameters":[{"name":"owner","type":["Ref","Pattern.Root"],"meaning":"所属。"}]"#,
        )
    } else {
        definitions
    };
    let checked = crate::definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pattern","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"有限owner補完の再検査。","locations":[],"note":"全case。"}}],"snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"root","type":"Pattern.Root","origin":"o"}},{{"id":"other","type":"Pattern.Root","origin":"o"}},{{"id":"p","type":"Pattern.Part","origin":"o"}},{{"id":"q","type":"Pattern.Part","origin":"o"}}],"atoms":[{{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"o"}},{{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"o"}},{{"id":"fq","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"o"}}]}}]}}"#
    );
    let map = if structure_only {
        map.replace(
            r#""id":"q","type":"Pattern.Part""#,
            r#""id":"q","type":"Pattern.External""#,
        )
        .replace(
            r#""field":"Pattern.Part.flag","value":false"#,
            r#""field":"Pattern.External.quantity","value":"0""#,
        )
    } else {
        map
    };
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";change choose(c:Part,b:Bool)=c with{{flag=b}};law required valid(c:Part):c.flag;}}"
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
