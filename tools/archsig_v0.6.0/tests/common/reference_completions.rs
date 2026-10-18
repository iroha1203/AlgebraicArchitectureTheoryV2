use archsig as fixture_archsig;
use archsig::{canonical::Json, definition::check_definitions, observed::input::InputSources};
#[allow(dead_code)]
mod maps {
    use super::fixture_archsig as archsig;
    include!("map_application.rs");
}
pub const SCRIPT: &str = r#"
view same(s:Sample):Bool=s.left=s.left;
view same_pair(s:Sample):(Root,Root)=(s.left,s.left);
view compare(s:Sample):Bool=s.left=s.right;
view choose(s:Sample):Root=s.left;
view ignore(s:Sample):Z=if s.left=s.left then 7 else 8;
law required equal(s:Sample):s.left=s.left;
law required differs(s:Sample):s.left!=s.left;
law required prior():false;
view seed():Z=1;
"#;
pub fn input(script: &str, peer: bool, moved: bool) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Refs","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Refs.Root","meaning":"参照先。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Refs.Sample","meaning":"独立した欠測参照。","parameters":[{"name":"owner","type":["Ref","Refs.Root"],"meaning":"所属。"}],"fields":[{"name":"left","type":["Ref","Refs.Root"],"meaning":"左参照。"},{"name":"right","type":["Ref","Refs.Root"],"meaning":"右参照。"},{"name":"flag","type":"Bool","meaning":"有限条件。"}],"alignments":[]}]}]}"#;
    let d = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Refs"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading RefCalc {{use vocabulary Refs version "1" digest "{digest}";{script}}}"#
    );
    let shift = if moved { 10 } else { 0 };
    let revision = if moved { "r2" } else { "r1" };
    let suffix = if moved { ":relocated" } else { "" };
    let mut snapshots = vec![];
    let mut origins = vec![];
    for (id, mode, roots) in [
        ("v", "specification", vec!["A", "B"]),
        ("w", "proposed", vec!["C"]),
    ] {
        if id == "w" && !peer {
            continue;
        }
        origins.push(format!(r#"{{"id":"{id}","mode":"{mode}","method":"登録参照の小さい例。","locations":[{{"source":"src","path":"{id}.refs.model","span":[{shift},{}]}}]}}"#,shift+1));
        let mut subjects: Vec<_> = roots
            .iter()
            .map(|root| format!(r#"{{"id":"{root}","type":"Refs.Root","origin":"{id}"}}"#))
            .collect();
        let mut atoms = vec![];
        if id == "v" {
            for item in ["item", "other"] {
                subjects.push(format!(
                    r#"{{"id":"{item}","type":"Refs.Sample","origin":"v"}}"#
                ));
                atoms.push(format!(r#"{{"id":"{item}-owner","subject":"{item}","field":"Refs.Sample.owner","value":["v","A"],"origin":"v"}}"#));
            }
        }
        snapshots.push(format!(
            r#"{{"id":"{id}","origin":"{id}","subjects":[{}],"atoms":[{}]}}"#,
            subjects.join(","),
            atoms.join(",")
        ));
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Refs","version":"1","digest":"{digest}"}}],"sources":[{{"id":"src","uri":"urn:fixture:reference-completions{suffix}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
pub const MAP_SCRIPT: &str = r#"
view origin_ref(m:Reservations.Migration):Reservations.System=m.from;
view same(m:Reservations.Migration):Bool=m.from=m.from;
view members(m:Reservations.Migration):Set<Reservations.State> =Reservations.State[m.from];
view endpoints(m:Reservations.Migration):(Reservations.System,Reservations.System)=(m.from,m.to);
view same_owner(p:Reservations.State):Bool=p.owner=p.owner;
view owner(p:Reservations.State):Reservations.System=p.owner;
"#;
pub fn constrained(owner: bool) -> InputSources {
    let i = maps::owned("known");
    let law = String::from_utf8(i.law().bytes().to_vec())
        .unwrap()
        .replace(maps::OWNED_SCRIPT, MAP_SCRIPT);
    let remove = if owner { "p-owner" } else { "m-from" };
    let map = String::from_utf8(i.archmap().bytes().to_vec())
        .unwrap()
        .lines()
        .filter(|line| {
            !line.contains(&format!("\"id\": \"{remove}\""))
                && !(owner && line.contains("\"id\": \"e-from\""))
        })
        .collect::<Vec<_>>()
        .join("\n");
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.into_bytes(),
        map.into_bytes(),
    )
}
#[allow(dead_code)]
pub fn ref_value(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}

pub fn constrained_joint() -> InputSources {
    let i = constrained(false);
    let map = String::from_utf8(i.archmap().bytes().to_vec())
        .unwrap()
        .lines()
        .filter(|line| !line.contains("\"id\": \"m-to\""))
        .collect::<Vec<_>>()
        .join("\n");
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.into_bytes(),
    )
}
