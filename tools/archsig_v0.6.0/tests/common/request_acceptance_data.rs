use archsig::observed::input::InputSources;
pub const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Requests","version":"1","dependencies":[],"declarations":[
{"kind":"entity","name":"Requests.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},
{"kind":"entity","name":"Requests.Item","meaning":"所属する項目。","parameters":[{"name":"owner","type":["Ref","Requests.Root"],"meaning":"所属。"}],"fields":[{"name":"quantity","type":"Z","meaning":"未観測の数量。"}],"alignments":[]},
{"kind":"data","name":"Requests.Choice","meaning":"選択。","constructors":[{"name":"Empty","meaning":"空。","arguments":[]},{"name":"Number","meaning":"整数。","arguments":["Z"]}]}]}]}"#;
pub const BODY: &str = r#"
view missing(p:Item):Z=p.quantity;
view opaque():Bool=(fn(z:Z)=>z*z)=(fn(z:Z)=>z*z+0);
view first(): Z = 10;
view second(): Z = 20;
view seed(): Z = 30;
view plus(x: Z): Z = x+1;
view root(a: Root): Root = a;
view belongs(a: Root,p: Item[a]): Bool = true;
view empty(): List<Z> = list<Z>[];
view absent(): Option<Z> = none<Z>;
view choice(): Choice = Empty;
view pair(): (Z,Bool) = (1,true);
law required same(a: Root,b: Root): a=b;
law required require(b: Bool): b;
law required prior(): false;
"#;
pub fn input() -> InputSources {
    let d = archsig::definition::check_definitions(&[("definition0", D.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Requests"].digest;
    let l = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading R{{use vocabulary Requests version \"1\" digest \"{digest}\";{BODY}}}"
    );
    let a = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Requests","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"spec","mode":"specification","method":"独立した要求入力。","locations":[],"note":"r1"}}],"snapshots":[{{"id":"v","origin":"spec","subjects":[{{"id":"A","type":"Requests.Root","origin":"spec"}},{{"id":"B","type":"Requests.Root","origin":"spec"}},{{"id":"i","type":"Requests.Item","origin":"spec"}}],"atoms":[{{"id":"owner-i","subject":"i","field":"Requests.Item.owner","value":["v","A"],"origin":"spec"}}]}}]}}"#
    );
    InputSources::from_bytes(vec![D.as_bytes().to_vec()], l.into_bytes(), a.into_bytes())
}
