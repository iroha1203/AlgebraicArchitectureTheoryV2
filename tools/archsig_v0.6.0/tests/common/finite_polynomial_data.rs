use archsig_common::control::Control;
use archsig_input::input::{CheckedInputs, InputSources, check_inputs};
use std::sync::Arc;
#[allow(dead_code)]
mod base {
    include!("object_view_compatibility_data.rs");
}
pub const BODY: &str = "law required ax(c:Part):c.quantity=0;law required ay(c:Part):c.other=1;law optional diff(c:Part):c.quantity=c.other;law optional duplicate(c:Part):c.quantity+c.quantity=0;";
pub const MAP: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pattern","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"有限代入の独立入力。","locations":[],"note":"r1"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"root","type":"Pattern.Root","origin":"model"},{"id":"p","type":"Pattern.Part","origin":"model"}],"atoms":[{"id":"owner-p","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"x","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"},{"id":"y","subject":"p","field":"Pattern.Part.other","value":"1","origin":"model"},{"id":"z","subject":"p","field":"Pattern.Part.third","value":"2","origin":"model"}]}]}"#;
pub fn inputs(body: &str) -> Arc<CheckedInputs> {
    with_map(body, MAP)
}
pub fn with_map(body: &str, map: &str) -> Arc<CheckedInputs> {
    let definition=base::D.replace(r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,r#"{"name":"quantity","type":["Fp","2"],"meaning":"数量。"},{"name":"other","type":["Fp","2"],"meaning":"第二成分。"},{"name":"third","type":["Fp","3"],"meaning":"異なる法。"}"#);
    let d = archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
        .unwrap();
    let digest = &d.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";{body}}}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![definition.into_bytes()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &Control::unlimited(),
        )
        .unwrap(),
    )
}
