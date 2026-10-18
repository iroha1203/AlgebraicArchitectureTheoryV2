use archsig as fixture_archsig;
use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
#[allow(dead_code)]
mod references {
    use super::fixture_archsig as archsig;
    include!("reference_completions.rs");
}
pub fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}
fn unary(kind: &str, value: Json) -> Json {
    Json::Arr(vec![Json::str(kind), value])
}
fn field(name: &str, ty: Json) -> Json {
    Json::obj([
        ("name", Json::str(name)),
        ("type", ty),
        ("meaning", Json::str("有限fieldの例。")),
    ])
}
fn entity(name: &str, parameters: Vec<Json>, fields: Vec<Json>) -> Json {
    Json::obj([
        ("kind", Json::str("entity")),
        ("name", Json::str(name)),
        ("meaning", Json::str("登録された対象。")),
        ("parameters", Json::Arr(parameters)),
        ("fields", Json::Arr(fields)),
        ("alignments", Json::Arr(vec![])),
    ])
}
pub const SCRIPT: &str = r#"
view chosen(h:Holder):Sample=h.chosen;
view same(h:Holder):Bool=h.chosen=h.chosen;
view pair(h:Holder):(Sample,Sample)=(h.chosen,h.chosen);
view independent(h:Holder):Bool=h.chosen=h.second;
view maybe_value(h:Holder):Option<Sample> =h.maybe_value;
view members(h:Holder):Set<Sample> =h.members;
view mixed(h:Holder):(Sample,Bool)=h.mixed;
view plain(h:Holder):Option<Root> =h.plain;
view choice(h:Holder):Choice=h.choice;
view empty_option(h:Holder):Option<Empty> =h.empty_option;
view empty_set(h:Holder):Set<Empty> =h.empty_set;
view size(h:Holder):Z=count(h.members);
view owner(h:Holder):Root=h.owner;
view stable(h:Holder):Bool=h.mixed=h.mixed;
view called(h:Holder):Bool=let v=pair(h) in v.0=v.1;
law required valid(h:Holder):h.chosen.owner=h.owner;
law required each(h:Holder):h.chosen=h.chosen;
law required numeric(h:Holder,z:Z,q:Q):z=z and h.chosen=h.chosen and q=q;
law required flags(h:Holder):h.flag and h.chosen=h.chosen;
law required prior():false;
view seed():Z=1;
"#;
pub fn input(peer: bool, moved: bool, unknown_owner: bool) -> InputSources {
    build(peer, moved, unknown_owner, None)
}
pub fn counterexample(reverse: bool) -> InputSources {
    build(false, false, false, Some(reverse))
}
fn build(peer: bool, moved: bool, unknown_owner: bool, counter: Option<bool>) -> InputSources {
    let root = unary("Ref", Json::str("Fields.Root"));
    let owned = Json::Arr(vec![
        Json::str("Owned"),
        Json::str("Fields.Sample"),
        Json::str("owner"),
    ]);
    let holder = entity(
        "Fields.Holder",
        vec![field("owner", root.clone())],
        vec![
            field("chosen", owned.clone()),
            field("second", owned.clone()),
            field("maybe_value", unary("Option", owned.clone())),
            field("members", unary("Set", owned.clone())),
            field(
                "mixed",
                Json::Arr(vec![Json::str("Tuple"), owned, Json::str("Bool")]),
            ),
            field("plain", unary("Option", root.clone())),
            field("choice", unary("Data", Json::str("Fields.Choice"))),
            field(
                "empty_option",
                unary("Option", unary("Ref", Json::str("Fields.Empty"))),
            ),
            field(
                "empty_set",
                unary("Set", unary("Ref", Json::str("Fields.Empty"))),
            ),
            field("flag", Json::str("Bool")),
        ],
    );
    let choice = Json::obj([
        ("kind", Json::str("data")),
        ("name", Json::str("Fields.Choice")),
        ("meaning", Json::str("参照を含む有限data。")),
        (
            "constructors",
            Json::Arr(vec![
                Json::obj([
                    ("name", Json::str("empty")),
                    ("arguments", Json::Arr(vec![])),
                    ("meaning", Json::str("空。")),
                ]),
                Json::obj([
                    ("name", Json::str("pick")),
                    (
                        "arguments",
                        Json::Arr(vec![root.clone(), Json::str("Bool")]),
                    ),
                    ("meaning", Json::str("参照と条件。")),
                ]),
            ]),
        ),
    ]);
    let definitions = Json::obj([
        ("format", Json::str("archsig.atom-definition/1")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("semantics", Json::str("archsig/0.6.0")),
                ("namespace", Json::str("Fields")),
                ("version", Json::str("1")),
                ("dependencies", Json::Arr(vec![])),
                (
                    "declarations",
                    Json::Arr(vec![
                        entity("Fields.Root", vec![], vec![]),
                        entity("Fields.Empty", vec![], vec![]),
                        entity("Fields.Sample", vec![field("owner", root)], vec![]),
                        holder,
                        choice,
                    ]),
                ),
            ])]),
        ),
    ])
    .canonical();
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Fields"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Inspect {{ use vocabulary Fields version \"1\" digest \"{digest}\"; {SCRIPT} }}"
    );
    let mut subjects = vec![];
    let mut atoms = vec![];
    for (id, ty) in [
        ("A", "Root"),
        ("B", "Root"),
        ("p", "Sample"),
        ("q", "Sample"),
        ("r", "Sample"),
        ("h", "Holder"),
        ("k", "Holder"),
    ] {
        subjects.push(Json::obj([
            ("id", Json::str(id)),
            ("type", Json::str(format!("Fields.{ty}"))),
            ("origin", Json::str("v")),
        ]));
    }
    if counter == Some(true) {
        subjects.swap(5, 6);
    }
    for (subject, ty, owner) in [
        ("p", "Sample", "A"),
        ("q", "Sample", "A"),
        ("r", "Sample", "B"),
        ("h", "Holder", "A"),
        ("k", "Holder", "B"),
    ] {
        if unknown_owner && subject == "h" {
            continue;
        }
        atoms.push(Json::obj([
            ("id", Json::str(format!("{subject}-owner"))),
            ("subject", Json::str(subject)),
            ("field", Json::str(format!("Fields.{ty}.owner"))),
            ("value", reference("v", owner)),
            ("origin", Json::str("v")),
        ]));
    }
    for (subject, flag) in [("h", true), ("k", false)] {
        if counter.is_some() && subject == "h" {
            continue;
        }
        atoms.push(Json::obj([
            ("id", Json::str(format!("{subject}-flag"))),
            ("subject", Json::str(subject)),
            ("field", Json::str("Fields.Holder.flag")),
            ("value", Json::Bool(flag)),
            ("origin", Json::str("v")),
        ]));
    }
    let mut snapshots = vec![Json::obj([
        ("id", Json::str("v")),
        ("origin", Json::str("v")),
        ("subjects", Json::Arr(subjects)),
        ("atoms", Json::Arr(atoms)),
    ])];
    if peer {
        snapshots.push(Json::obj([
            ("id", Json::str("w")),
            ("origin", Json::str("w")),
            (
                "subjects",
                Json::Arr(vec![
                    Json::obj([
                        ("id", Json::str("C")),
                        ("type", Json::str("Fields.Root")),
                        ("origin", Json::str("w")),
                    ]),
                    Json::obj([
                        ("id", Json::str("p")),
                        ("type", Json::str("Fields.Sample")),
                        ("origin", Json::str("w")),
                    ]),
                ]),
            ),
            (
                "atoms",
                Json::Arr(vec![Json::obj([
                    ("id", Json::str("w-owner")),
                    ("subject", Json::str("p")),
                    ("field", Json::str("Fields.Sample.owner")),
                    ("value", reference("w", "C")),
                    ("origin", Json::str("w")),
                ])]),
            ),
        ]));
    }
    let shift = if moved { 10 } else { 0 };
    let origins = ["v", "w"]
        .into_iter()
        .take(if peer { 2 } else { 1 })
        .map(|id| {
            Json::obj([
                ("id", Json::str(id)),
                ("mode", Json::str("observed")),
                ("method", Json::str("有限fieldの観測。")),
                (
                    "locations",
                    Json::Arr(vec![Json::obj([
                        ("source", Json::str("src")),
                        ("path", Json::str(format!("{id}.fields.model"))),
                        (
                            "span",
                            Json::Arr(vec![Json::Nat(shift), Json::Nat(shift + 1)]),
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
                ("namespace", Json::str("Fields")),
                ("version", Json::str("1")),
                ("digest", Json::str(digest)),
            ])]),
        ),
        (
            "sources",
            Json::Arr(vec![Json::obj([
                ("id", Json::str("src")),
                (
                    "uri",
                    Json::str(if moved {
                        "urn:fixture:finite-reference-fields:relocated"
                    } else {
                        "urn:fixture:finite-reference-fields"
                    }),
                ),
                ("revision", Json::str(if moved { "r2" } else { "r1" })),
                (
                    "digest",
                    Json::str(
                        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    ),
                ),
            ])]),
        ),
        ("origins", Json::Arr(origins)),
        ("snapshots", Json::Arr(snapshots)),
    ])
    .canonical();
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

pub const MAP_SCRIPT: &str = r#"
view chosen(p:Reservations.State):Reservations.State=p.chosen;
view pair(p:Reservations.State):(Reservations.State,Reservations.System)=(p.chosen,p.owner);
law required valid(p:Reservations.State):p.chosen.owner=p.owner;
"#;
pub fn map_constrained() -> InputSources {
    let i = references::constrained(true);
    let old = String::from_utf8(i.definitions()[0].bytes().to_vec()).unwrap();
    let d = check_definitions(&[("definition0", old.as_bytes())]).unwrap();
    let old_digest = &d.vocabularies["Reservations"].digest;
    let start = old.find("\"name\": \"Reservations.State\"").unwrap();
    let index = start + old[start..].find("\"fields\": [").unwrap() + "\"fields\": [".len();
    let extra = r#"{"name":"chosen","type":["Owned","Reservations.State","owner"],"meaning":"移行元から選ぶ欠測状態。"},"#;
    let mut definitions = old.clone();
    definitions.insert_str(index, extra);
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Reservations"].digest;
    let law = String::from_utf8(i.law().bytes().to_vec())
        .unwrap()
        .replace(references::MAP_SCRIPT, MAP_SCRIPT)
        .replace(old_digest, digest);
    let map = String::from_utf8(i.archmap().bytes().to_vec())
        .unwrap()
        .replace(old_digest, digest);
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
pub fn known_values() -> InputSources {
    let i = input(false, false, false);
    let values = [
        ("chosen", reference("v", "p")),
        ("maybe_value", Json::obj([("some", reference("v", "q"))])),
        (
            "members",
            Json::Arr(vec![reference("v", "p"), reference("v", "q")]),
        ),
        (
            "mixed",
            Json::Arr(vec![reference("v", "p"), Json::Bool(true)]),
        ),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                (
                    "args",
                    Json::Arr(vec![reference("v", "A"), Json::Bool(false)]),
                ),
            ]),
        ),
    ];
    let atoms = values
        .into_iter()
        .map(|(field, value)| {
            Json::obj([
                ("id", Json::str(format!("known-{field}"))),
                ("subject", Json::str("h")),
                ("field", Json::str(format!("Fields.Holder.{field}"))),
                ("value", value),
                ("origin", Json::str("v")),
            ])
            .canonical()
        })
        .collect::<Vec<_>>()
        .join(",");
    let map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    assert_eq!(map.matches("\"atoms\":[").count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.replacen("\"atoms\":[", &format!("\"atoms\":[{atoms},"), 1)
            .into_bytes(),
    )
}
