use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Paths","version":"1","semantics":"archsig/0.6.0","dependencies":[],"declarations":[{"kind":"entity","name":"Paths.Root","meaning":"所属先。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Paths.Node","meaning":"内部操作の対象。","parameters":[{"name":"owner","type":["Ref","Paths.Root"],"meaning":"所属先。"}],"fields":[{"name":"mark","type":"Z","meaning":"量。"},{"name":"link","type":["Ref","Paths.Node"],"meaning":"対象参照。"},{"name":"links","type":["List",["Ref","Paths.Node"]],"meaning":"順序と重複を持つ対象参照。"},{"name":"members","type":["Set",["Ref","Paths.Node"]],"meaning":"対象参照の外延集合。"}],"alignments":[]},{"kind":"arrow","name":"Paths.Hop","meaning":"内部生成元。","parameters":[{"name":"owner","type":["Ref","Paths.Root"],"meaning":"所属先。"},{"name":"from","type":["Owned","Paths.Node","owner"],"meaning":"始点。"},{"name":"to","type":["Owned","Paths.Node","owner"],"meaning":"終点。"}],"fields":[],"alignments":[]},{"kind":"entity","name":"Paths.Unused","meaning":"未使用の正しい定義。","parameters":[],"fields":[],"alignments":[]}]}]}"#;
pub const SCRIPT: &str = r#"
view step(e:Hop):Path<Node,Node> =path(e);
view maybe(e:Hop):Option<Path<Node,Node>> =some(step(e));
view first(e:Hop):Node=source(path(e));
view last(e:Hop):Node=target(path(e));
view nested(e:Hop):Option<List<(Bool,Path<Node,Node>)>> =some(list<(Bool,Path<Node,Node>)>[(true,path(e)),(false,step(e))]);
view lexical(e:Hop):Path<Node,Node> =let p=step(e) in if true then p else path(e);
view same(e:Hop,f:Hop):Bool=path(e)=path(f);
view self_action(e:Hop):Bool=path(e)=identity(source(path(e)));
view missing_same(e:Hop):Bool=path(e)=path(e);
view seed():Z=1;
law required prior():false;
view unused(x:Unused):Bool=true;
"#;
fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}
fn subject(id: &str, ty: &str, origin: &str) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("type", Json::str(ty)),
        ("origin", Json::str(origin)),
    ])
}
fn atom(id: &str, owner: &str, field: &str, value: Json, origin: &str) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("subject", Json::str(owner)),
        ("field", Json::str(field)),
        ("value", value),
        ("origin", Json::str(origin)),
    ])
}
pub fn input(mode: &str, revision: &str) -> InputSources {
    assert!(matches!(
        mode,
        "normal" | "mismatch" | "list_mismatch" | "missing_to" | "missing_tag" | "missing_source"
    ));
    let checked = check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Paths"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Walk {{use vocabulary Paths version \"1\" digest \"{digest}\";{SCRIPT}}}"
    );
    let mut subjects = vec![subject("A", "Paths.Root", "v")];
    let mut atoms = vec![];
    for (id, mark) in [("p", "2"), ("q", "9"), ("r", "5")] {
        subjects.push(subject(id, "Paths.Node", "v"));
        atoms.push(atom(
            &format!("{id}-owner"),
            id,
            "Paths.Node.owner",
            reference("v", "A"),
            "v",
        ));
        if !((mode == "missing_tag" && id == "q") || (mode == "missing_source" && id == "p")) {
            atoms.push(atom(
                &format!("{id}-mark"),
                id,
                "Paths.Node.mark",
                Json::str(mark),
                "v",
            ));
        }
        atoms.push(atom(
            &format!("{id}-link"),
            id,
            "Paths.Node.link",
            reference(
                "v",
                if mode == "mismatch" && id == "q" {
                    "p"
                } else {
                    id
                },
            ),
            "v",
        ));
        let links = if mode == "list_mismatch" && id == "q" {
            vec![reference("v", id), reference("v", "q")]
        } else {
            vec![reference("v", id), reference("v", id), reference("v", "q")]
        };
        atoms.push(atom(
            &format!("{id}-links"),
            id,
            "Paths.Node.links",
            Json::Arr(links),
            "v",
        ));
        let mut members = vec![reference("v", id)];
        if id != "q" {
            members.push(reference("v", "q"));
        }
        atoms.push(atom(
            &format!("{id}-members"),
            id,
            "Paths.Node.members",
            Json::Arr(members),
            "v",
        ));
    }
    for (id, to) in [
        ("e", "q"),
        ("alias", "q"),
        ("self", "p"),
        ("different", "r"),
    ] {
        subjects.push(subject(id, "Paths.Hop", "v"));
        for (name, point) in [("owner", "A"), ("from", "p"), ("to", to)] {
            if mode == "missing_to" && id == "e" && name == "to" {
                continue;
            }
            atoms.push(atom(
                &format!("{id}-{name}"),
                id,
                &format!("Paths.Hop.{name}"),
                reference("v", point),
                "v",
            ));
        }
    }
    let other_subjects = vec![
        subject("A", "Paths.Root", "w"),
        subject("p", "Paths.Node", "w"),
    ];
    let other_atoms = vec![
        atom("p-owner", "p", "Paths.Node.owner", reference("w", "A"), "w"),
        atom("p-mark", "p", "Paths.Node.mark", Json::str("17"), "w"),
        atom("p-link", "p", "Paths.Node.link", reference("w", "p"), "w"),
        atom(
            "p-links",
            "p",
            "Paths.Node.links",
            Json::Arr(vec![reference("w", "p"), reference("w", "p")]),
            "w",
        ),
        atom(
            "p-members",
            "p",
            "Paths.Node.members",
            Json::Arr(vec![reference("w", "p")]),
            "w",
        ),
    ];
    let snapshot = |id: &str, subjects: Vec<Json>, atoms: Vec<Json>| {
        Json::obj([
            ("id", Json::str(id)),
            ("origin", Json::str(id)),
            ("subjects", Json::Arr(subjects)),
            ("atoms", Json::Arr(atoms)),
        ])
    };
    let origins = [("v", "observed"), ("w", "proposed")]
        .into_iter()
        .map(|(id, mode)| {
            Json::obj([
                ("id", Json::str(id)),
                ("mode", Json::str(mode)),
                (
                    "method",
                    Json::str("原始対象・内部arrowとfieldを観測する。"),
                ),
                (
                    "locations",
                    Json::Arr(vec![Json::obj([
                        ("source", Json::str("scan")),
                        ("path", Json::str(&format!("{id}.model"))),
                        (
                            "span",
                            Json::Arr(vec![
                                Json::Nat(if revision == "r1" { 0 } else { 10 }),
                                Json::Nat(if revision == "r1" { 1 } else { 11 }),
                            ]),
                        ),
                    ])]),
                ),
            ])
        })
        .collect();
    let map = Json::obj([
        ("format", Json::str("archsig.archmap/2")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("namespace", Json::str("Paths")),
                ("version", Json::str("1")),
                ("digest", Json::str(digest)),
            ])]),
        ),
        (
            "sources",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("scan")),
                ("uri", Json::str("urn:fixture:internal-path")),
                ("revision", Json::str(revision)),
                (
                    "digest",
                    Json::str(
                        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    ),
                ),
            ])]),
        ),
        ("origins", Json::Arr(origins)),
        (
            "snapshots",
            Json::Arr(vec![
                snapshot("v", subjects, atoms),
                snapshot("w", other_subjects, other_atoms),
            ]),
        ),
    ]);
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
