use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod owners {
    use super::fixture_archsig as archsig;
    include!("owner_completions.rs");
}
#[allow(unused_imports)]
pub use owners::ref_value;

pub const SCRIPT: &str = r#"
law required each(a:Root,s:Sample[a]):s.flag;
law required pair(a:Root,s:Sample[a],t:Sample[a]):s.flag and t.flag;
law required owner_is_a(a:Root,s:Sample[a]):s.owner=a;
law required numeric(a:Root,z:Z,s:Sample[a],q:Q):z+1=z+1 and q+1=q+1;
law required prior():false;
view hole(a:Root):Z=count(Sample[a]);
view seed():Z=1;
law required sets(a:Root,x:Set<Sample[a]>):count(x)>=0;
law required options(a:Root,x:Option<Sample[a]>):true;
law required tuples(a:Root,x:(Sample[a],Bool)):true;
"#;

fn script(i: InputSources, from: &str, to: &str, map: Vec<u8>) -> InputSources {
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    assert!(law.contains(from));
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replacen(from, to, 1).into_bytes(),
        map,
    )
}
pub fn input(unknowns: usize, peer: bool, moved: bool, flag: Option<bool>) -> InputSources {
    let i = owners::input(unknowns, peer, moved, false);
    let mut map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    if let Some(flag) = flag {
        let atoms = ["item", "other"].into_iter().take(unknowns).map(|s|format!(r#"{{"id":"{s}-flag","subject":"{s}","field":"Refs.Sample.flag","value":{flag},"origin":"v"}}"#)).collect::<Vec<_>>().join(",");
        if map.contains("\"atoms\":[]") {
            map = map.replacen("\"atoms\":[]", &format!("\"atoms\":[{atoms}]"), 1);
        } else {
            assert!(map.contains("\"atoms\":["));
            map = map.replacen("\"atoms\":[", &format!("\"atoms\":[{atoms},"), 1);
        }
    }
    script(i, owners::SCRIPT, SCRIPT, map.into_bytes())
}
pub fn counterexample(reverse: bool, moved: bool) -> InputSources {
    let i = owners::counterexample(reverse, moved);
    let map = i.archmap().bytes().to_vec();
    script(i, owners::SCRIPT, SCRIPT, map)
}
pub const MAP_SCRIPT: &str = r#"
law required each(a:Reservations.System,s:Reservations.State[a]):s.owner=a;
"#;
pub fn constrained() -> InputSources {
    let i = owners::constrained();
    let map = i.archmap().bytes().to_vec();
    script(i, owners::MAP_SCRIPT, MAP_SCRIPT, map)
}

pub const ARROW_SCRIPT: &str = r#"
law required each(a:Reservations.System,e:Reservations.Reserve[a]):e.owner=a;
"#;
pub fn arrow() -> InputSources {
    let i = owners::constrained();
    let map = String::from_utf8(i.archmap().bytes().to_vec())
        .unwrap()
        .lines()
        .filter(|line| !line.contains("\"id\": \"e-owner\""))
        .collect::<Vec<_>>()
        .join("\n");
    script(i, owners::MAP_SCRIPT, ARROW_SCRIPT, map.into_bytes())
}

fn nested_base(body: &str, flags: [Option<bool>; 2], unknown: bool) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Dep","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Dep.Root","meaning":"根。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Child","meaning":"根に属する対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[],"alignments":[]},{"kind":"entity","name":"Dep.Leaf","meaning":"同じ根に属する別の対象。","parameters":[{"name":"owner","type":["Ref","Dep.Root"],"meaning":"所属。"}],"fields":[{"name":"ok","type":"Bool","meaning":"観測条件。"}],"alignments":[]}]}]}"#;
    let checked =
        archsig::definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Dep"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Inspect {{ use vocabulary Dep version \"1\" digest \"{digest}\"; {body} }}"
    );
    let subjects = [
        ("A", "Root"),
        ("B", "Root"),
        ("Z", "Root"),
        ("p", "Child"),
        ("q", "Child"),
        ("l", "Leaf"),
        ("m", "Leaf"),
    ]
    .map(|(id, ty)| format!(r#"{{"id":"{id}","type":"Dep.{ty}","origin":"scan"}}"#))
    .join(",");
    let mut atoms = Vec::new();
    for (id, ty, owner) in [
        ("p", "Child", "A"),
        ("q", "Child", "B"),
        ("l", "Leaf", "A"),
        ("m", "Leaf", "B"),
    ] {
        if unknown && id == "p" {
            continue;
        }
        atoms.push(format!(r#"{{"id":"{id}-owner","subject":"{id}","field":"Dep.{ty}.owner","value":["v","{owner}"],"origin":"scan"}}"#));
    }
    for (id, flag) in ["l", "m"].into_iter().zip(flags) {
        if let Some(flag) = flag {
            atoms.push(format!(r#"{{"id":"{id}-ok","subject":"{id}","field":"Dep.Leaf.ok","value":{flag},"origin":"scan"}}"#));
        }
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Dep","version":"1","digest":"{digest}"}}],"sources":[{{"id":"source","uri":"urn:fixture:dependent-private","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"scan","mode":"observed","method":"有限な対象と所属の観測。","locations":[{{"source":"source","path":"dependent.model","span":[0,1]}}]}}],"snapshots":[{{"id":"v","origin":"scan","subjects":[{subjects}],"atoms":[{}]}}]}}"#,
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

pub const NESTED_SCRIPT: &str = "law required each(a:Root,b:Child[a],c:Leaf[a]):c.ok;";
pub fn nested(missing_flag: bool) -> InputSources {
    let flags = if missing_flag {
        [None, Some(false)]
    } else {
        [Some(true), Some(true)]
    };
    let i = nested_base(NESTED_SCRIPT, flags, true);
    let map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    let atom = r#"{"id":"l-owner","subject":"l","field":"Dep.Leaf.owner","value":["v","A"],"origin":"scan"}"#;
    assert!(map.contains(&format!("{atom},")));
    let map = map.replacen(&format!("{atom},"), "", 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.into_bytes(),
    )
}
