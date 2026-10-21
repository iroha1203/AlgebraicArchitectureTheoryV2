pub const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pattern","version":"1","dependencies":[],"declarations":[
{"kind":"entity","name":"Pattern.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},
{"kind":"entity","name":"Pattern.Part","meaning":"部分。","parameters":[{"name":"owner","type":["Ref","Pattern.Root"],"meaning":"所属。"}],"fields":[{"name":"quantity","type":"Z","meaning":"数量。"}],"alignments":[]},
{"kind":"entity","name":"Pattern.External","meaning":"固定外部。","parameters":[],"fields":[{"name":"quantity","type":"Z","meaning":"外部量。"}],"alignments":[]},
{"kind":"entity","name":"Pattern.Vacant","meaning":"空の参照型。","parameters":[],"fields":[],"alignments":[]}
]}]}"#;
pub const A: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pattern","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"独立入力。","locations":[],"note":"fixture-r1"}],"snapshots":[{"id":"v","origin":"model","subjects":[
{"id":"root","type":"Pattern.Root","origin":"model"},
{"id":"p","type":"Pattern.Part","origin":"model"}
],"atoms":[
{"id":"owner-p","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},
{"id":"quantity-p","subject":"p","field":"Pattern.Part.quantity","value":"2","origin":"model"}
]}]}"#;
