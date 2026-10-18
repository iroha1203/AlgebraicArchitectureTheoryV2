use archsig::{definition::check_definitions, observed::input::InputSources};

pub const SCRIPT: &str = r#"
view id(x:Node):Path<Node,Node> =identity(x);
view start(x:Node):Node=source(identity(x));
view end(x:Node):Node=target(id(x));
view maybe_value(x:Node):Option<Path<Node,Node>> =some(id(x));
view absent():Option<Path<Node,Node>> =none<Path<Node,Node>>;
view nested(x:Node):Option<List<(Bool,Option<Path<Node,Node>>)>> =some(list<(Bool,Option<Path<Node,Node>>)>[(true,some(identity(x))),(false,none<Path<Node,Node>>)]);
view empty():List<Path<Node,Node>> =list<Path<Node,Node>>[];
view lexical(x:Node):Path<Node,Node> =let p=id(x) in if true then p else identity(x);
view primitive():Option<List<(Bool,Z)>> =some(list<(Bool,Z)>[(false,2),(true,1)]);
view seed():Z=1;
law required prior():false;
"#;
pub fn input(moved: bool) -> InputSources {
    custom(SCRIPT, moved)
}
pub fn custom(body: &str, moved: bool) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
"vocabularies":[{"namespace":"Paths","version":"1","semantics":"archsig/0.6.0","dependencies":[],
"declarations":[{"kind":"entity","name":"Paths.Node","meaning":"恒等の対象。","parameters":[],"fields":[],"alignments":[]}]}]}"#;
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Paths"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\nreading Walk {{\nuse vocabulary Paths version \"1\" digest \"{digest}\";\n{body}\n}}\n"
    );
    let (uri, revision, span) = if moved {
        ("urn:fixture:paths-moved", "r2", "[10,11]")
    } else {
        ("urn:fixture:paths", "r1", "[0,1]")
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
"vocabularies":[{{"namespace":"Paths","version":"1","digest":"{digest}"}}],
"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
"origins":[{{"id":"objects","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"objects.model","span":{span}}}]}}],
"snapshots":[{{"id":"v","origin":"objects","subjects":[{{"id":"a","type":"Paths.Node","origin":"objects"}},{{"id":"b","type":"Paths.Node","origin":"objects"}}],"atoms":[]}},
{{"id":"w","origin":"objects","subjects":[{{"id":"a","type":"Paths.Node","origin":"objects"}}],"atoms":[]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

/// 同じ定義と原始対象を使い、呼出し先と呼出し元の reading を分ける。
pub fn cross_reading() -> InputSources {
    let original = input(false);
    let mut law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
    let import = law
        .lines()
        .find(|line| line.starts_with("use vocabulary "))
        .unwrap()
        .to_owned();
    law.push_str(&format!(
        r#"
reading Other {{
{import}
use Walk as O;
view mixed(x:Node,y:Node):Bool=(O.id(x),fn(z:Z)=>z)=(identity(y),fn(z:Z)=>z);
view nested(x:Node,y:Node):Bool=some(list<(Path<Node,Node>,Term<(Z)->Z>)>[(O.id(x),fn(z:Z)=>z)])=some(list<(Path<Node,Node>,Term<(Z)->Z>)>[(identity(y),fn(t:Z)=>t+0)]);
view different_term(x:Node):Bool=(O.id(x),fn(z:Z)=>z)=(identity(x),fn(z:Z)=>z+1);
view equal_path(x:Node,y:Node):Bool=O.id(x)=identity(y);
view unequal_path(x:Node,y:Node):Bool=O.id(x)!=identity(y);
view equal_option(x:Node,y:Node):Bool=some(O.id(x))=some(identity(y));
view equal_list(x:Node,y:Node):Bool=list<Path<Node,Node>>[O.id(x),identity(y)]=list<Path<Node,Node>>[identity(y),O.id(x)];
view equal_tuple(x:Node,y:Node):Bool=(false,O.id(x))=(false,identity(y));
view member_path(x:Node,y:Node):Bool=O.id(x) in list<Path<Node,Node>>[identity(y)];
view equal_absent():Bool=none<Path<Node,Node>> =none<Path<Node,Node>>;
law required direct_law(x:Node,y:Node):O.id(x)=identity(y);
}}
"#
    ));
    InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        original.archmap().bytes().to_vec(),
    )
}
