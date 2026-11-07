// 整数分解の再観測。係数・右辺・更新先を別の原始位置に置く。
use archsig_input::input::InputSources;
pub fn input(body: &str, coefficient: &str, rhs: &str) -> InputSources {
    let definition = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"Integer state","parameters":[],"fields":[{"name":"h","type":"Z","meaning":"First coordinate"},{"name":"k","type":"Z","meaning":"Second coordinate"},{"name":"a","type":"Z","meaning":"Coefficient"},{"name":"b","type":"Z","meaning":"Right hand side"}],"alignments":[]}]}]}"#;
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let digest = &checked.vocabularies()["Pair"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Pair{{use vocabulary Pair version \"1\" digest \"{digest}\";{body}}}"
    );
    let atoms = [("h","0"),("k","0"),("a",coefficient),("b",rhs)].into_iter().map(|(name,value)| format!(r#"{{"id":"{name}","subject":"s","field":"Pair.State.{name}","value":"{value}","origin":"model"}}"#)).collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"Integer reobservation fixture","locations":[],"note":"Exact integer fibers"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Pair.State","origin":"model"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
