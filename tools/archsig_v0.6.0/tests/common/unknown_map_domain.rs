use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"MapCall","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"MapCall.Root","meaning":"Root","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"MapCall.Item","meaning":"Item","parameters":[{"name":"owner","type":["Ref","MapCall.Root"],"meaning":"owner"}],"fields":[],"alignments":[]},{"kind":"entity","name":"MapCall.Holder","meaning":"Holder","parameters":[{"name":"owner","type":["Ref","MapCall.Root"],"meaning":"owner"}],"fields":[{"name":"table","type":["Map",["Owned","MapCall.Item","owner"],["Owned","MapCall.Item","owner"]],"meaning":"table"}],"alignments":[]}]}]}"#;
pub const SCRIPT: &str = r#"
view accept(a:Root,f:Map<Item[a],Item[a]>):Bool=true;
view call(a:Root,h:Holder):Bool=accept(a,h.table);
view returned(a:Root,f:Map<Item,Item>):Map<Item[a],Item[a]> =f;
view through(a:Root,h:Holder):Bool=accept(a,returned(a,h.table));
view nested(a:Root,fs:(Option<List<Map<Item[a],Item[a]>>>,Set<Map<Item[a],Item[a]>>)):Bool=true;
view containers(a:Root,h:Holder):Bool=nested(a,(some(list<Map<Item,Item>>[h.table,h.table]),set<Map<Item,Item>>{h.table,h.table}));
view keep(a:Root,f:Map<Item[a],Item[a]>,z:Z):Z=z+0;
law required affine(a:Root,h:Holder,z:Z):keep(a,h.table,z)=z;
view keepQ(a:Root,f:Map<Item[a],Item[a]>,q:Q):Q=q+rat(0,1);
law required rational(a:Root,h:Holder,q:Q):keepQ(a,h.table,q)=q;
view seed():Z=1;
law required prior():false;
"#;
fn reference(subject: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(subject)])
}
fn subject(id: &str, ty: &str) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("type", Json::str(ty)),
        ("origin", Json::str("model")),
    ])
}
fn atom(id: &str, subject: &str, field: &str, value: Json) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("subject", Json::str(subject)),
        ("field", Json::str(field)),
        ("value", value),
        ("origin", Json::str("model")),
    ])
}
/// 値・参照・欠測だけを作る。成立や所属の判定は入力へ含めない。
pub fn input(mode: &str, revision: &str) -> InputSources {
    assert!(matches!(
        mode,
        "constrained" | "varying" | "nonkey" | "empty_varying" | "empty" | "missing_table"
    ));
    let checked = check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["MapCall"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading MapCall {{use vocabulary MapCall version "1" digest "{digest}";{SCRIPT}}}"#
    );
    let mut subjects = vec![
        subject("A", "MapCall.Root"),
        subject("B", "MapCall.Root"),
        subject("h", "MapCall.Holder"),
    ];
    let mut atoms = vec![];
    if mode != "empty" {
        subjects.push(subject("p", "MapCall.Item"));
    }
    if !matches!(mode, "varying" | "empty_varying") {
        atoms.push(atom("h-owner", "h", "MapCall.Holder.owner", reference("A")));
    }
    let empty = matches!(mode, "nonkey" | "empty_varying" | "empty");
    if mode != "missing_table" {
        let pairs = if empty {
            vec![]
        } else {
            vec![Json::Arr(vec![reference("p"), reference("p")])]
        };
        atoms.push(atom("table", "h", "MapCall.Holder.table", Json::Arr(pairs)));
    } else {
        subjects.push(subject("q", "MapCall.Item"));
        atoms.push(atom("q-owner", "q", "MapCall.Item.owner", reference("A")));
    }
    let map = Json::obj([
        ("format", Json::str("archsig.archmap/2")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("namespace", Json::str("MapCall")),
                ("version", Json::str("1")),
                ("digest", Json::str(digest)),
            ])]),
        ),
        (
            "sources",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("src")),
                ("uri", Json::str("urn:fixture:unknown-map-domain")),
                ("revision", Json::str(revision)),
                ("digest", Json::str(format!("sha256:{}", "a".repeat(64)))),
            ])]),
        ),
        (
            "origins",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("model")),
                ("mode", Json::str("specification")),
                ("method", Json::str("registered map and owner slots")),
                (
                    "locations",
                    Json::Arr(vec![Json::obj([
                        ("source", Json::str("src")),
                        ("path", Json::str("map-call.model")),
                        ("span", Json::Arr(vec![Json::Nat(0), Json::Nat(4)])),
                    ])]),
                ),
            ])]),
        ),
        (
            "snapshots",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("v")),
                ("origin", Json::str("model")),
                ("subjects", Json::Arr(subjects)),
                ("atoms", Json::Arr(atoms)),
            ])]),
        ),
    ]);
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
