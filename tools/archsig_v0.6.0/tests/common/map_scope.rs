//! 同じ未知参照の反復と、その有限な型付き補完を表す独立入力。
pub fn fixture(entries: Option<(&str, &str)>, source_links: &str) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let definition = include_bytes!("../fixtures/configuration-map-graph.atoms.json");
    let checked = archsig::definition::check_definitions(&[("definition0", definition)]).unwrap();
    let digest = &checked.vocabularies["Graph"].digest;
    let law = include_str!("../fixtures/configuration-map-graph.law").replace("@DIGEST@", digest);
    let mut map = include_str!("../fixtures/configuration-map-graph.archmap.json")
        .replace("@DIGEST@", digest)
        .replace(r#""@LINKS_A@""#, source_links)
        .replace(r#""@LINKS_B@""#, r#"[["v","r"],["v","s"]]"#)
        .replace(r#""@MEMBERS_A@""#, "[]")
        .replace(r#""@MEMBERS_B@""#, "[]");
    if let Some((p, q)) = entries {
        map = map.replace(
            r#"[[["v","p"],["v","r"]],[["v","q"],["v","r"]]]"#,
            &format!(r#"[[["v","p"],["v","{p}"]],[["v","q"],["v","{q}"]]]"#),
        );
    } else {
        map = map
            .lines()
            .filter(|line| !line.contains("m-entries"))
            .collect::<Vec<_>>()
            .join("\n");
    }
    (definition.to_vec(), law.into_bytes(), map.into_bytes())
}
