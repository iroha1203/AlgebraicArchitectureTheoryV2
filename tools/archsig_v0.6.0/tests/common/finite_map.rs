pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Maps","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Maps.Key","meaning":"Key","parameters":[],"fields":[{"name":"mark","type":"Bool","meaning":"mark"}],"alignments":[]},{"kind":"entity","name":"Maps.Image","meaning":"Image","parameters":[],"fields":[{"name":"mark","type":"Bool","meaning":"mark"}],"alignments":[]},{"kind":"entity","name":"Maps.Void","meaning":"Void","parameters":[],"fields":[],"alignments":[]}]}]}"#;
pub const SCRIPT: &str = r#"
view every():Bool=forall f:Map<Key,Image> . f=f;
view any():Bool=exists f:Map<Key,Image> . f=f;
view empty_source():Bool=exists f:Map<Void,Image> . true;
view empty_target():Bool=exists f:Map<Key,Void> . true;
view no_map_all():Bool=forall f:Map<Key,Void> . false;
view both_empty():Bool=exists f:Map<Void,Void> . true;
view option_domain():Bool=forall f:Option<Map<Key,Image>> . f=f;
view tuple_domain():Bool=forall f:(Unit,Map<Key,Image>) . f=f;
view set_domain():Bool=forall f:Set<Map<Key,Image>> . f=f;
view seed():Z=1;
law required whole(f:Map<Key,Image>):f=f;
law required impossible(f:Map<Key,Image>):f!=f;
law required prior():false;
"#;
pub fn law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Maps {{use vocabulary Maps version \"1\" digest \"{digest}\";{SCRIPT}}}"
    )
}
pub fn archmap(digest: &str, revision: &str) -> String {
    r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Maps","version":"1","digest":"DIGEST"}],"sources":[{"id":"src","uri":"urn:fixture:finite-map-domain","revision":"REVISION","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}],"origins":[{"id":"base","mode":"specification","method":"finite registered families","locations":[{"source":"src","path":"families.model","span":[0,4]}]}],"snapshots":[{"id":"v","origin":"base","subjects":[{"id":"a","type":"Maps.Key","origin":"base"},{"id":"x","type":"Maps.Image","origin":"base"}],"atoms":[]},{"id":"w","origin":"base","subjects":[{"id":"b","type":"Maps.Key","origin":"base"},{"id":"y","type":"Maps.Image","origin":"base"}],"atoms":[]},{"id":"z","origin":"base","subjects":[],"atoms":[]}]}"#.replace("DIGEST",digest).replace("REVISION",revision)
}

pub const OWNED_DEFINITIONS: &str = include_str!("../fixtures/reservations.atoms.json");
pub const OWNED_SCRIPT: &str = r#"
view every(a:System,b:System):Bool=forall f:Map<State[a],State[b]> . f=f;
view any(a:System,b:System):Bool=exists f:Map<State[a],State[b]> . true;
view lexical(m:Migration):Bool=let a=m.from in let b=m.to in forall f:Map<State[a],State[b]> . f=f;
"#;
pub fn owned_law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Reservations {{use vocabulary Reservations version \"1\" digest \"{digest}\";{OWNED_SCRIPT}}}"
    )
}
pub fn owned_archmap(unknown: bool) -> String {
    let source = include_str!("../fixtures/reservations.archmap.json").replace(
        "\"subjects\": [",
        "\"subjects\": [{\"id\":\"Z\",\"type\":\"Reservations.System\",\"origin\":\"model\"},",
    );
    if unknown {
        source
            .lines()
            .filter(|l| !l.contains("\"id\": \"p-owner\""))
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        source
    }
}
