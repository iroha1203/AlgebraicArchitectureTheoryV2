use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
pub fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}
pub fn table(snapshot: &str, key: &str, image: &str) -> Json {
    Json::Arr(vec![Json::Arr(vec![
        reference(snapshot, key),
        reference(snapshot, image),
    ])])
}
fn unary(kind: &str, element: Json) -> Json {
    Json::Arr(vec![Json::str(kind), element])
}
fn mapping(domain: Json, codomain: Json) -> Json {
    Json::Arr(vec![Json::str("Map"), domain, codomain])
}
fn field(name: &str, ty: Json) -> Json {
    Json::obj([
        ("name", Json::str(name)),
        ("type", ty),
        ("meaning", Json::str("原始field。")),
    ])
}
fn entity(name: &str, parameters: Vec<Json>, fields: Vec<Json>) -> Json {
    Json::obj([
        ("kind", Json::str("entity")),
        ("name", Json::str(format!("MapFields.{name}"))),
        ("meaning", Json::str("登録された対象。")),
        ("parameters", Json::Arr(parameters)),
        ("fields", Json::Arr(fields)),
        ("alignments", Json::Arr(vec![])),
    ])
}
pub const SCRIPT: &str = r#"
view read(h:Holder):Map<Key,Image> =h.table;
view same(h:Holder):Bool=h.table=h.table;
view pair(h:Holder):(Map<Key,Image>,Map<Key,Image>)=(h.table,h.table);
view independent(h:Holder):Bool=h.table=h.other;
view apply(h:Holder,x:Key):Image=h.table(x);
view lexical(h:Holder,x:Key):Image=let f=h.table in f(x);
view called(h:Holder,x:Key):Image=apply(h,x);
view maybe_value(h:Holder):Option<Map<Key,Image>> =h.maybe_value;
view mixed(h:Holder):(Bool,Map<Key,Image>)=h.mixed;
view bag(h:Holder):Set<Map<Key,Image>> =h.bag;
view choice(h:Holder):Payload=h.choice;
view plain(h:Holder):Map<Key,Image> =h.plain;
view empty(h:Holder):Map<Void,Image> =h.empty;
view summary(h:Holder):(Map<Key,Image>,Z)=(h.table,count(Key[h.owner]));
view owner(h:Holder):Root=h.owner;
view partial(h:Holder):(Map<Key,Image>,Z,Z)=(h.table,h.level,count(Key[h.owner]));
view pending(h:Holder,a:Root):(Map<Key,Image>,Z)=(h.table,count(Key[if h.level=0 then h.owner else a]));
law required valid(h:Holder):let a=h.owner in forall x:Key[a] . h.table(x)=h.table(x);
law required each(h:Holder):h.table=h.table;
law required numeric(h:Holder,z:Z,q:Q):z=z and h.table=h.table and q=q;
law required flags(h:Holder):h.flag and h.table=h.table;
law required prior():false;
view seed():Z=1;
"#;
#[derive(Default)]
struct Variant {
    peer: bool,
    moved: bool,
    unknown_owner: bool,
    anchor: bool,
    empty: bool,
    no_images: bool,
    counter: Option<bool>,
    known: bool,
}
pub fn input(peer: bool, moved: bool, unknown_owner: bool, anchor: bool) -> InputSources {
    build(Variant {
        peer,
        moved,
        unknown_owner,
        anchor,
        ..Variant::default()
    })
}
pub fn counterexample(reverse: bool) -> InputSources {
    build(Variant {
        counter: Some(reverse),
        ..Variant::default()
    })
}
pub fn empty_rosters() -> InputSources {
    build(Variant {
        empty: true,
        ..Variant::default()
    })
}
pub fn no_images() -> InputSources {
    build(Variant {
        no_images: true,
        ..Variant::default()
    })
}
pub fn known_values() -> InputSources {
    build(Variant {
        known: true,
        ..Variant::default()
    })
}
fn build(v: Variant) -> InputSources {
    let root = unary("Ref", Json::str("MapFields.Root"));
    let key = unary("Ref", Json::str("MapFields.Key"));
    let image = unary("Ref", Json::str("MapFields.Image"));
    let owned = |name: &str| {
        Json::Arr(vec![
            Json::str("Owned"),
            Json::str(format!("MapFields.{name}")),
            Json::str("owner"),
        ])
    };
    let map = mapping(owned("Key"), owned("Image"));
    let plain = mapping(key.clone(), image.clone());
    let payload = Json::obj([
        ("kind", Json::str("data")),
        ("name", Json::str("MapFields.Payload")),
        ("meaning", Json::str("有限Mapの選択。")),
        (
            "constructors",
            Json::Arr(vec![
                Json::obj([
                    ("name", Json::str("blank")),
                    ("arguments", Json::Arr(vec![])),
                    ("meaning", Json::str("空の選択。")),
                ]),
                Json::obj([
                    ("name", Json::str("wrap")),
                    ("arguments", Json::Arr(vec![plain.clone()])),
                    ("meaning", Json::str("Mapを含む値。")),
                ]),
            ]),
        ),
    ]);
    let holder = entity(
        "Holder",
        vec![field("owner", root.clone())],
        vec![
            field("table", map.clone()),
            field("other", map.clone()),
            field("anchor", mapping(owned("Key"), image.clone())),
            field("plain", plain),
            field(
                "empty",
                mapping(unary("Ref", Json::str("MapFields.Void")), image.clone()),
            ),
            field("maybe_value", unary("Option", map.clone())),
            field(
                "mixed",
                Json::Arr(vec![Json::str("Tuple"), Json::str("Bool"), map.clone()]),
            ),
            field("bag", unary("Set", map)),
            field("choice", unary("Data", Json::str("MapFields.Payload"))),
            field("flag", Json::str("Bool")),
            field("level", Json::str("Z")),
        ],
    );
    let definitions = Json::obj([
        ("format", Json::str("archsig.atom-definition/1")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("semantics", Json::str("archsig/0.6.0")),
                ("namespace", Json::str("MapFields")),
                ("version", Json::str("1")),
                ("dependencies", Json::Arr(vec![])),
                (
                    "declarations",
                    Json::Arr(vec![
                        entity("Root", vec![], vec![]),
                        entity("Void", vec![], vec![]),
                        entity("Key", vec![field("owner", root.clone())], vec![]),
                        entity("Image", vec![field("owner", root)], vec![]),
                        holder,
                        payload,
                    ]),
                ),
            ])]),
        ),
    ])
    .canonical();
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["MapFields"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Inspect{{use vocabulary MapFields version \"1\" digest \"{digest}\";{SCRIPT}}}"
    );
    let mut subjects = vec![];
    for (id, ty) in [
        ("A", "Root"),
        ("B", "Root"),
        ("k", "Key"),
        ("x", "Image"),
        ("y", "Image"),
        ("h", "Holder"),
        ("j", "Holder"),
    ] {
        if (v.empty && matches!(ty, "Key" | "Image")) || (v.no_images && ty == "Image") {
            continue;
        }
        subjects.push(subject(id, ty, "v"));
    }
    if v.counter == Some(true) {
        let n = subjects.len();
        subjects.swap(n - 1, n - 2);
    }
    let mut atoms = vec![];
    for (id, ty) in [
        ("k", "Key"),
        ("x", "Image"),
        ("y", "Image"),
        ("h", "Holder"),
        ("j", "Holder"),
    ] {
        if (v.empty && matches!(ty, "Key" | "Image"))
            || (v.no_images && ty == "Image")
            || (v.unknown_owner && id == "h")
        {
            continue;
        }
        atoms.push(atom(
            &format!("{id}-owner"),
            id,
            &format!("{ty}.owner"),
            reference("v", "A"),
            "v",
        ));
    }
    for (id, flag) in [("h", true), ("j", false)] {
        if v.counter.is_some() && id == "h" {
            continue;
        }
        atoms.push(atom(
            &format!("{id}-flag"),
            id,
            "Holder.flag",
            Json::Bool(flag),
            "v",
        ));
    }
    if v.anchor {
        atoms.push(atom(
            "anchor",
            "h",
            "Holder.anchor",
            table("v", "k", "x"),
            "v",
        ));
    }
    if v.known {
        for (name, value) in [
            ("table", table("v", "k", "x")),
            ("other", table("v", "k", "y")),
            ("maybe_value", Json::obj([("some", table("v", "k", "y"))])),
            (
                "mixed",
                Json::Arr(vec![Json::Bool(true), table("v", "k", "x")]),
            ),
            (
                "bag",
                Json::Arr(vec![table("v", "k", "x"), table("v", "k", "y")]),
            ),
            (
                "choice",
                Json::obj([
                    ("tag", Json::str("wrap")),
                    ("args", Json::Arr(vec![table("v", "k", "x")])),
                ]),
            ),
        ] {
            atoms.push(atom(
                &format!("known-{name}"),
                "h",
                &format!("Holder.{name}"),
                value,
                "v",
            ));
        }
    }
    let mut origins = vec![origin("v", v.moved)];
    let mut snapshots = vec![Json::obj([
        ("id", Json::str("v")),
        ("origin", Json::str("v")),
        ("subjects", Json::Arr(subjects)),
        ("atoms", Json::Arr(atoms)),
    ])];
    if v.peer {
        origins.push(origin("w", v.moved));
        snapshots.push(Json::obj([
            ("id", Json::str("w")),
            ("origin", Json::str("w")),
            (
                "subjects",
                Json::Arr(vec![
                    subject("C", "Root", "w"),
                    subject("k", "Key", "w"),
                    subject("x", "Image", "w"),
                ]),
            ),
            (
                "atoms",
                Json::Arr(vec![
                    atom("k-owner", "k", "Key.owner", reference("w", "C"), "w"),
                    atom("x-owner", "x", "Image.owner", reference("w", "C"), "w"),
                ]),
            ),
        ]));
    }
    let map = Json::obj([
        ("format", Json::str("archsig.archmap/2")),
        ("semantics", Json::str("archsig/0.6.0")),
        (
            "vocabularies",
            Json::Arr(vec![Json::obj([
                ("namespace", Json::str("MapFields")),
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
                    Json::str(if v.moved {
                        "urn:fixture:map-field:relocated"
                    } else {
                        "urn:fixture:map-field"
                    }),
                ),
                ("revision", Json::str(if v.moved { "r2" } else { "r1" })),
                ("digest", Json::str(format!("sha256:{}", "a".repeat(64)))),
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
fn subject(id: &str, ty: &str, origin: &str) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("type", Json::str(format!("MapFields.{ty}"))),
        ("origin", Json::str(origin)),
    ])
}
fn atom(id: &str, subject: &str, field: &str, value: Json, origin: &str) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("subject", Json::str(subject)),
        ("field", Json::str(format!("MapFields.{field}"))),
        ("value", value),
        ("origin", Json::str(origin)),
    ])
}
fn origin(id: &str, moved: bool) -> Json {
    Json::obj([
        ("id", Json::str(id)),
        ("mode", Json::str("observed")),
        ("method", Json::str("finite map field fixture")),
        (
            "locations",
            Json::Arr(vec![Json::obj([
                ("source", Json::str("src")),
                ("path", Json::str("map-field.model")),
                (
                    "span",
                    Json::Arr(if moved {
                        vec![Json::Nat(10), Json::Nat(11)]
                    } else {
                        vec![Json::Nat(0), Json::Nat(1)]
                    }),
                ),
            ])]),
        ),
    ])
}
