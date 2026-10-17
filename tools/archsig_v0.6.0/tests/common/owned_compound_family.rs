use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
pub const DEFINITIONS: &str = include_str!("../fixtures/reservations.atoms.json");
pub const SCRIPT: &str = r#"
law required option_values(a:System,f:Option<State[a]>):f=f;
law required tupled(a:System,f:(Unit,State[a])):f=f;
law required subset(a:System,f:Set<State[a]>):f=f;
law required maps(a:System,b:System,f:Map<State[a],State[b]>):f=f;
law required impossible(a:System,b:System,f:Map<State[a],State[b]>):f!=f;
law required map_option(a:System,b:System,f:Option<Map<State[a],State[b]>>):f=f;
law required map_tuple(a:System,b:System,f:(Unit,Map<State[a],State[b]>)):f=f;
law required map_set(a:System,b:System,f:Set<Map<State[a],State[b]>>):f=f;
law required prior():false;
view seed():Z=1;
"#;
pub fn input(unknown: bool, second: bool, revision: &str) -> InputSources {
    let d = check_definitions(&[("definition0", DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    let subject = |id: &str, ty: &str| {
        Json::obj([
            ("id", Json::str(id)),
            ("type", Json::str(format!("Reservations.{ty}"))),
            ("origin", Json::str("model")),
        ])
    };
    let snapshot = |id: &str| {
        let subjects = [
            ("A", "System"),
            ("B", "System"),
            ("Z", "System"),
            ("p", "State"),
            ("q", "State"),
            ("r", "State"),
            ("s", "State"),
        ]
        .iter()
        .map(|(s, t)| subject(s, t))
        .collect();
        let atoms = [("p", "A"), ("q", "A"), ("r", "B"), ("s", "B")]
            .iter()
            .filter(|(s, _)| !(unknown && *s == "p"))
            .map(|(s, o)| {
                Json::obj([
                    ("id", Json::str(format!("{s}-owner"))),
                    ("subject", Json::str(*s)),
                    ("field", Json::str("Reservations.State.owner")),
                    ("value", Json::Arr(vec![Json::str(id), Json::str(*o)])),
                    ("origin", Json::str("model")),
                ])
            })
            .collect();
        Json::obj([
            ("id", Json::str(id)),
            ("origin", Json::str("model")),
            ("subjects", Json::Arr(subjects)),
            ("atoms", Json::Arr(atoms)),
        ])
    };
    let mut snapshots = vec![snapshot("v")];
    if second {
        snapshots.push(snapshot("w"));
    }
    snapshots.push(Json::obj([
        ("id", Json::str("empty")),
        ("origin", Json::str("model")),
        ("subjects", Json::Arr(vec![])),
        ("atoms", Json::Arr(vec![])),
    ]));
    let map = Json::obj([
        ("format", Json::str("archsig.archmap/2")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("namespace", Json::str("Reservations")),
                ("version", Json::str("1")),
                ("digest", Json::str(digest)),
            ])]),
        ),
        (
            "sources",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("src")),
                ("uri", Json::str("urn:fixture:owned-compound-family")),
                ("revision", Json::str(revision)),
                ("digest", Json::str(format!("sha256:{}", "a".repeat(64)))),
            ])]),
        ),
        (
            "origins",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("model")),
                ("mode", Json::str("specification")),
                ("method", Json::str("finite owner families")),
                (
                    "locations",
                    Json::Arr(vec![Json::obj([
                        ("source", Json::str("src")),
                        ("path", Json::str("families.model")),
                        ("span", Json::Arr(vec![Json::Nat(0), Json::Nat(4)])),
                    ])]),
                ),
            ])]),
        ),
        ("snapshots", Json::Arr(snapshots)),
    ]);
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading Reservations {{use vocabulary Reservations version "1" digest "{digest}";{SCRIPT}}}"#
    );
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
