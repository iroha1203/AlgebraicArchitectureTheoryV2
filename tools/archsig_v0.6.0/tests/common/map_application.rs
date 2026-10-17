use archsig::{definition::check_definitions, observed::input::InputSources};
#[allow(dead_code)]
mod known {
    include!("known_map.rs");
}
pub const OWNED_DEFINITIONS: &str = include_str!("../fixtures/reservations.atoms.json");
pub const OWNED_SCRIPT: &str = r#"
view apply(m:Reservations.Migration,x:Reservations.State):Reservations.State=m.states(x);
view lexical(m:Reservations.Migration,x:Reservations.State):Reservations.State=let f=m.states in f(x);
view called(m:Reservations.Migration,x:Reservations.State):Reservations.State=apply(m,x);
view pair(m:Reservations.Migration,x:Reservations.State):(Reservations.State,Reservations.State)=(m.states(x),m.states(x));
view wrapped(m:Reservations.Migration,x:Reservations.State):Reservations.State=let pair=(unit,m.states) in pair.1(x);
view from_edge(m:Reservations.Migration,e:Reservations.Reserve):Reservations.State=m.states(e.from);
law required holds(m:Reservations.Migration,x:Reservations.State):m.states(x)=m.states(x);
law required parameter(a:Reservations.System,b:Reservations.System,f:Map<Reservations.State[a],Reservations.State[b]>,x:Reservations.State):f(x)=f(x);
view seed():Z=1;
law required prior():false;
"#;
pub fn owned(mode: &str) -> InputSources {
    owned_revision(mode, "r1")
}
pub fn owned_revision(mode: &str, revision: &str) -> InputSources {
    let definitions = OWNED_DEFINITIONS.as_bytes();
    let d = check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Reservations"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";reading Applications {{use vocabulary Reservations version "1" digest "{digest}";{OWNED_SCRIPT}}}"#
    );
    let mut map = include_str!("../fixtures/reservations.archmap.json").to_string();
    if mode == "empty" {
        map = map.replace(
            "\"subjects\": [",
            "\"subjects\": [{\"id\":\"Z\",\"type\":\"Reservations.System\",\"origin\":\"model\"},",
        );
        map = map
            .lines()
            .filter(|l| !l.contains("\"id\": \"m-reserves\""))
            .map(|l| {
                if l.contains("\"id\": \"m-from\"") {
                    l.replace("[\"v\", \"A\"]", "[\"v\", \"Z\"]")
                } else if l.contains("\"id\": \"m-states\"") {
                    l.replace(
                        "[[[\"v\", \"p\"], [\"v\", \"r\"]], [[\"v\", \"q\"], [\"v\", \"s\"]]]",
                        "[]",
                    )
                } else {
                    l.into()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        // Removing the final reserves row also removes its preceding separator.
        map = map.replace(
            "\"origin\": \"model\"},\n    ]",
            "\"origin\": \"model\"}\n    ]",
        );
    }
    if mode == "missing_key" {
        map = map
            .lines()
            .filter(|l| !l.contains("\"id\": \"e-from\""))
            .collect::<Vec<_>>()
            .join("\n");
    }
    if mode == "missing" {
        map = map
            .lines()
            .filter(|l| !l.contains("\"id\": \"m-states\""))
            .collect::<Vec<_>>()
            .join("\n");
    }
    let source = archsig::canonical::Json::obj([
        ("id", archsig::canonical::Json::str("src")),
        (
            "uri",
            archsig::canonical::Json::str("urn:fixture:map-application"),
        ),
        ("revision", archsig::canonical::Json::str(revision)),
        (
            "digest",
            archsig::canonical::Json::str(format!("sha256:{}", "a".repeat(64))),
        ),
    ]);
    map = map.replace(
        "\"sources\": []",
        &format!("\"sources\": [{}]", source.canonical()),
    );
    map = map.replace(
        "\"locations\": []",
        r#""locations":[{"source":"src","path":"application.model","span":[0,4]}]"#,
    );
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
pub fn plain(revision: &str) -> InputSources {
    let definitions = known::DEFINITIONS.as_bytes();
    let d = check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    let body = r#"view apply(s:Sample,x:Item):Item=s.different(x);view choice(s:Sample,x:Item):Item=(if true then s.m else s.different)(x);view lexical(s:Sample,x:Item):Item=let f=s.different in f(x);view generated(x:Item):Bool=forall f:Map<Item,Item> . f(x)=f(x);view absent(s:Sample,x:Item):Item=s.missing(x);view read(s:Sample):Map<Item,Item> =s.different;view call(s:Sample,x:Item):Item=read(s)(x);view composed(s:Sample,x:Item):Item=s.m(s.different(x));view seed():Z=1;law required prior():false;"#;
    let law = known::law(digest).replace(known::SCRIPT, body);
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        law.into_bytes(),
        known::archmap(digest, revision).into_bytes(),
    )
}

#[allow(dead_code)]
mod finite {
    include!("finite_map.rs");
}
pub fn distinct() -> InputSources {
    let definitions = finite::DEFINITIONS.as_bytes();
    let d = check_definitions(&[("definition0", definitions)]).unwrap();
    let digest = &d.vocabularies["Maps"].digest;
    let law = finite::law(digest).replace(
        finite::SCRIPT,
        "view generated(x:Key):Bool=forall f:Map<Key,Image> . f(x)=f(x);",
    );
    InputSources::from_bytes(
        vec![definitions.to_vec()],
        law.into_bytes(),
        finite::archmap(digest, "r1").into_bytes(),
    )
}
