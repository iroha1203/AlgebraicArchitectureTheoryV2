use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod references {
    use super::fixture_archsig as archsig;
    include!("reference_completions.rs");
}
#[allow(unused_imports)]
pub use references::ref_value;

pub const SCRIPT: &str = r#"
view members(a:Root):Set<Sample> =Sample[a];
view size(a:Root):Z=count(Sample[a]);
view total(a:Root,b:Root):Z=count(Sample[a])+count(Sample[b]);
view pair(a:Root,b:Root):(Z,Z)=(count(Sample[a]),count(Sample[b]));
law required nonnegative(a:Root):count(Sample[a])>=0;
law required nonempty(a:Root):count(Sample[a])>0;
law required every(a:Root):forall s in Sample[a] . s.flag;
law required prior():false;
view seed():Z=1;
"#;

pub fn input(unknowns: usize, peer: bool, moved: bool, known_false: bool) -> InputSources {
    assert!((1..=2).contains(&unknowns));
    assert!(!known_false || unknowns == 1);
    let i = references::input(SCRIPT, peer, moved);
    let mut map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    for name in ["item", "other"].into_iter().take(unknowns) {
        let atom = format!(
            r#"{{"id":"{name}-owner","subject":"{name}","field":"Refs.Sample.owner","value":["v","A"],"origin":"v"}}"#
        );
        assert!(map.contains(&atom));
        map = if map.contains(&format!("{atom},")) {
            map.replacen(&format!("{atom},"), "", 1)
        } else if map.contains(&format!(",{atom}")) {
            map.replacen(&format!(",{atom}"), "", 1)
        } else {
            map.replacen(&atom, "", 1)
        };
        assert!(!map.contains(&atom));
    }
    if unknowns == 1 && !known_false {
        let other = r#",{"id":"other","type":"Refs.Sample","origin":"v"}"#;
        let owner = r#"{"id":"other-owner","subject":"other","field":"Refs.Sample.owner","value":["v","A"],"origin":"v"}"#;
        assert!(map.contains(other) && map.contains(owner));
        map = map.replacen(other, "", 1).replacen(owner, "", 1);
    }
    if known_false {
        map = map.replacen(
            "\"atoms\":[",
            r#""atoms":[{"id":"other-flag","subject":"other","field":"Refs.Sample.flag","value":false,"origin":"v"},"#,
            1,
        );
    }
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.into_bytes(),
    )
}

pub const MAP_SCRIPT: &str = r#"
view members(a:Reservations.System):Set<Reservations.State> =Reservations.State[a];
view size(a:Reservations.System):Z=count(Reservations.State[a]);
"#;
pub fn constrained() -> InputSources {
    let i = references::constrained(true);
    let law = String::from_utf8(i.law().bytes().to_vec())
        .unwrap()
        .replace(references::MAP_SCRIPT, MAP_SCRIPT);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}

pub fn counterexample(reverse: bool, moved: bool) -> InputSources {
    let i = input(1, false, moved, true);
    let mut map = String::from_utf8(i.archmap().bytes().to_vec()).unwrap();
    if reverse {
        let item = r#"{"id":"item","type":"Refs.Sample","origin":"v"}"#;
        let other = r#"{"id":"other","type":"Refs.Sample","origin":"v"}"#;
        let order = format!("{item},{other}");
        assert!(map.contains(&order));
        map = map.replacen(&order, &format!("{other},{item}"), 1);
    }
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        i.law().bytes().to_vec(),
        map.into_bytes(),
    )
}
