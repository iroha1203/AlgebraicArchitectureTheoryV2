
use archsig_common::{control::Control};
use archsig_input::{input::{CheckedInputs, InputSources, check_inputs}};
use std::sync::Arc;
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Family","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Family.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Family.Part","meaning":"部分。","parameters":[{"name":"owner","type":["Ref","Family.Root"],"meaning":"所属。"}],"fields":[{"name":"quantity","type":["Fp","2"],"meaning":"値。"}],"alignments":[]}]}]}"#;
const MAP: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Family","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"独立の有限入力。","locations":[],"note":"元の値。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"root","type":"Family.Root","origin":"model"},{"id":"r2","type":"Family.Root","origin":"model"},{"id":"p","type":"Family.Part","origin":"model"},{"id":"q","type":"Family.Part","origin":"model"}],"atoms":[{"id":"op","subject":"p","field":"Family.Part.owner","value":["v","root"],"origin":"model"},{"id":"oq","subject":"q","field":"Family.Part.owner","value":["v","root"],"origin":"model"},{"id":"xp","subject":"p","field":"Family.Part.quantity","value":"0","origin":"model"},{"id":"xq","subject":"q","field":"Family.Part.quantity","value":"1","origin":"model"}]}]}"#;
pub fn inputs(missing: bool, body: &str) -> Arc<CheckedInputs> {
    let defs = archsig_input::definition::check_definitions(&[("definition0", D.as_bytes())]).unwrap();
    let digest = &defs.vocabularies()["Family"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Family version \"1\" digest \"{digest}\";{body}}}"
    );
    let map = if missing {
        MAP.replace(r#",{"id":"xq","subject":"q","field":"Family.Part.quantity","value":"1","origin":"model"}"#, "")
    } else {
        MAP.into()
    };
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![D.as_bytes().to_vec()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &Control::unlimited(),
        )
        .unwrap(),
    )
}
