// 文書から独立した原始型と観測値。実行時のみ三入力へ包装する。
use archsig::{definition::check_definitions, observed::input::InputSources};
pub const FIELDS: &[(&str, &str, &str, &str)] = &[
    ("vunit", r#""Unit""#, "Unit", "[]"),
    ("vflag", r#""Bool""#, "Bool", "false"),
    (
        "vinteger",
        r#""Z""#,
        "Z",
        r#""1234567890123456789012345678901234567890""#,
    ),
    ("vrational", r#""Q""#, "Q", r#"["-2","3"]"#),
    ("vresidue", r#"["Fp","5"]"#, "Fp(5)", r#""4""#),
    ("vtext", r#""Text""#, "Text", r#""日本語🙂""#),
    (
        "vpair",
        r#"["Tuple","Z","Bool"]"#,
        "(Z,Bool)",
        r#"["0",false]"#,
    ),
    ("vlist", r#"["List","Z"]"#, "List<Z>", r#"["1","2","1"]"#),
    ("vset", r#"["Set","Z"]"#, "Set<Z>", r#"["2","1"]"#),
    (
        "voption",
        r#"["Option","Z"]"#,
        "Option<Z>",
        r#"{"none":true}"#,
    ),
    (
        "vpacket",
        r#"["Data","Values.Packet"]"#,
        "Packet",
        r#"{"tag":"Full","args":["7"]}"#,
    ),
    (
        "vmap",
        r#"["Map",["Ref","Values.Sample"],["Ref","Values.Sample"]]"#,
        "Map<Sample,Sample>",
        r#"[[["v","a"],["v","b"]],[["v","b"],["v","a"]],[["w","a"],["w","a"]]]"#,
    ),
];
pub fn input(missing: bool, extra: &str) -> InputSources {
    let fields = FIELDS
        .iter()
        .map(|(n, t, _, _)| format!(r#"{{"name":"{n}","type":{t},"meaning":"観測値"}}"#))
        .collect::<Vec<_>>()
        .join(",");
    let d = format!(
        r#"{{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{{"semantics":"archsig/0.6.0","namespace":"Values","version":"1","dependencies":[],"declarations":[{{"kind":"entity","name":"Values.Sample","meaning":"対象","parameters":[],"fields":[{fields}],"alignments":[]}},{{"kind":"data","name":"Values.Packet","meaning":"constructorの区別","constructors":[{{"name":"Empty","arguments":[],"meaning":"空"}},{{"name":"Full","arguments":["Z"],"meaning":"値"}}]}}]}}]}}"#
    );
    let checked = check_definitions(&[("definition0", d.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Values"].digest;
    let views = FIELDS
        .iter()
        .map(|(n, _, t, _)| format!("view {n}(s:Sample):{t} = s.{n};"))
        .collect::<Vec<_>>()
        .join("\n");
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Values{{use vocabulary Values version \"1\" digest \"{digest}\";{views}{extra}}}");
    let mut atoms = vec![];
    for id in ["a", "b"] {
        for (n, _, _, v) in FIELDS {
            if missing && id == "b" && *n == "vinteger" {
                continue;
            }
            let value = match (id, *n) {
                ("b", "vlist") => r#"["1","1","2"]"#,
                ("b", "vset") => r#"["1","2"]"#,
                ("b", "vmap") => {
                    r#"[[["w","a"],["w","a"]],[["v","b"],["v","a"]],[["v","a"],["v","b"]]]"#
                }
                _ => v,
            };
            atoms.push(format!(r#"{{"id":"{id}-{n}","subject":"{id}","field":"Values.Sample.{n}","value":{value},"origin":"base"}}"#));
        }
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Values","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"base","mode":"specification","method":"独立観測値","locations":[],"note":"比較用の有限モデル"}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"a","type":"Values.Sample","origin":"base"}},{{"id":"b","type":"Values.Sample","origin":"base"}}],"atoms":[{}]}},{{"id":"w","origin":"base","subjects":[{{"id":"a","type":"Values.Sample","origin":"base"}}],"atoms":[]}}]}}"#,
        atoms.join(",")
    );
    InputSources::from_bytes(vec![d.into_bytes()], law.into_bytes(), map.into_bytes())
}
