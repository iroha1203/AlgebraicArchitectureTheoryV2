// 全体写像の原始入力。局所表だけを与え、完成したglobal作用は渡さない。
include!("model_assembly_data.rs");
pub const MAP: &str =
    "m=assemble_map(Assembly.moves,from=$a.assembly,to=$a.assembly,x=@v/moveA,y=@v/moveB)";
pub fn mapped(edit: impl FnOnce(String) -> String) -> InputSources {
    sources(
        include_bytes!("../fixtures/model-map-assembly.atoms.json"),
        edit(include_str!("../fixtures/model-map-assembly.archmap.json").to_owned()),
    )
}
pub fn query(edit: impl FnOnce(String) -> String) -> InputSources {
    let raw = mapped(edit);
    let law=String::from_utf8(raw.law().bytes().to_vec()).unwrap().replace("law required zero(p:Part):p.quantity=0;","view moves(x:Move,y:Move):Set<Move> = set<Move>{x,y};law required zero(p:Part):p.quantity=0;");
    InputSources::from_bytes(
        raw.definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        raw.archmap().bytes().to_vec(),
    )
}
pub fn swapping(map: String) -> String {
    let map = atom(map, "moveA-steps", Some(Json::Arr(vec![])));
    let map = atom(map, "moveB-steps", Some(Json::Arr(vec![])));
    let map = without_arrows(map);
    let map = atom(
        map,
        "moveA-to",
        Some(Json::Arr(vec![Json::str("v"), Json::str("B")])),
    );
    let map = atom(
        map,
        "moveB-to",
        Some(Json::Arr(vec![Json::str("v"), Json::str("A")])),
    );
    let pairs = |pairs: [(&str, &str); 2]| {
        Json::Arr(
            pairs
                .into_iter()
                .map(|(a, b)| {
                    Json::Arr(vec![
                        Json::Arr(vec![Json::str("v"), Json::str(a)]),
                        Json::Arr(vec![Json::str("v"), Json::str(b)]),
                    ])
                })
                .collect(),
        )
    };
    let map = atom(map, "moveA-parts", Some(pairs([("a", "b"), ("ma", "mb")])));
    atom(map, "moveB-parts", Some(pairs([("mb", "ma"), ("b", "a")])))
}

pub fn folding(map: String, quantity: bool) -> String {
    let map = atom(map, "moveA-steps", Some(Json::Arr(vec![])));
    let map = atom(map, "moveB-steps", Some(Json::Arr(vec![])));
    let map = without_arrows(map);
    let map = atom(
        map,
        "moveB-to",
        Some(Json::Arr(vec![Json::str("v"), Json::str("A")])),
    );
    let pairs = [("mb", "ma"), ("b", "a")]
        .into_iter()
        .map(|(a, b)| {
            Json::Arr(vec![
                Json::Arr(vec![Json::str("v"), Json::str(a)]),
                Json::Arr(vec![Json::str("v"), Json::str(b)]),
            ])
        })
        .collect();
    let map = atom(map, "moveB-parts", Some(Json::Arr(pairs)));
    if quantity {
        atom(map, "a-quantity", Some(Json::str("1")))
    } else {
        map
    }
}
pub fn replace_law(raw: InputSources, old: &str, new: &str) -> InputSources {
    let law = String::from_utf8(raw.law().bytes().to_vec())
        .unwrap()
        .replace(old, new);
    InputSources::from_bytes(
        raw.definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        raw.archmap().bytes().to_vec(),
    )
}

pub fn generations() -> InputSources {
    query(|_| include_str!("../fixtures/model-map-generations.archmap.json").to_owned())
}
pub fn folding_with_arrows(map: String) -> String {
    let map = atom(
        map,
        "moveB-to",
        Some(Json::Arr(vec![Json::str("v"), Json::str("A")])),
    );
    let pairs = |pairs: Vec<(&str, &str)>| {
        Json::Arr(
            pairs
                .into_iter()
                .map(|(a, b)| {
                    Json::Arr(vec![
                        Json::Arr(vec![Json::str("v"), Json::str(a)]),
                        Json::Arr(vec![Json::str("v"), Json::str(b)]),
                    ])
                })
                .collect(),
        )
    };
    let map = atom(
        map,
        "moveB-parts",
        Some(pairs(vec![("mb", "ma"), ("b", "a")])),
    );
    let map = atom(
        map,
        "moveA-steps",
        Some(pairs(vec![("left", "left"), ("back", "back")])),
    );
    let map = atom(map, "moveB-steps", Some(pairs(vec![("right", "back")])));
    let mut map = owned(&archsig_common::json::parse(map.as_bytes()).unwrap());
    let snapshot = &mut items(fields(&mut map).get_mut("snapshots").unwrap())[0];
    items(fields(snapshot).get_mut("subjects").unwrap()).push(Json::obj([
        ("id", Json::str("back")),
        ("type", Json::str("Assemble.Step")),
        ("origin", Json::str("model")),
    ]));
    for (field, target) in [("owner", "A"), ("from", "ma"), ("to", "a")] {
        items(fields(snapshot).get_mut("atoms").unwrap()).push(Json::obj([
            ("id", Json::str(format!("back-{field}"))),
            ("subject", Json::str("back")),
            ("field", Json::str(format!("Assemble.Step.{field}"))),
            ("value", Json::Arr(vec![Json::str("v"), Json::str(target)])),
            ("origin", Json::str("model")),
        ]));
    }
    map.canonical()
}
