use archsig as fixture_archsig;
mod base {
    use super::fixture_archsig as archsig;
    include!("internal_paths.rs");
}
use archsig::{
    canonical::Json,
    json::{JNode, JValue, parse},
    observed::input::InputSources,
};
pub const SCRIPT: &str = r#"
view keep(p:Path<Node,Node>):Path<Node,Node> =p;
view join(e:Hop,f:Hop):Path<Node,Node> =then(path(e),path(f));
view triple(s:Hop,e:Hop,f:Hop):Path<Node,Node> =then(then(path(s),path(e)),path(f));
view associative(s:Hop,e:Hop,f:Hop):Bool=then(then(path(s),path(e)),path(f))=then(path(s),then(path(e),path(f)));
view left_unit(e:Hop):Bool=then(identity(source(path(e))),path(e))=path(e);
view right_unit(e:Hop):Bool=then(path(e),identity(target(path(e))))=path(e);
view same_self(s:Hop,e:Hop):Bool=then(path(s),path(e))=path(e);
view no_reextend(e:Hop,f:Hop,g:Hop):Bool=join(e,f)=path(g);
view empty(x:Node):Path<Node,Node> =then(identity(x),identity(x));
view join_first(e:Hop,f:Hop):Node=source(join(e,f));
view join_last(e:Hop,f:Hop):Node=target(join(e,f));
view join_nested(e:Hop,f:Hop):Option<List<(Bool,Path<Node,Node>)>> =some(list<(Bool,Path<Node,Node>)>[(true,join(e,f)),(false,let p=join(e,f) in if true then p else join(e,f))]);
"#;
fn convert(n: &JNode) -> Json {
    match &n.value {
        JValue::Str(s) => Json::str(s),
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Arr(xs) => Json::Arr(xs.iter().map(convert).collect()),
        JValue::Obj(xs) => Json::Obj(xs.iter().map(|(k, v)| (k.clone(), convert(v))).collect()),
        JValue::Null => panic!("fixture null"),
    }
}
fn reference(subject: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(subject)])
}
pub fn input(missing: bool, revision: &str) -> InputSources {
    let original = base::input(if missing { "missing_to" } else { "normal" }, revision);
    let mut map = convert(&parse(original.archmap().bytes()).unwrap());
    let Json::Obj(root) = &mut map else { panic!() };
    let Json::Arr(snapshots) = root.get_mut("snapshots").unwrap() else {
        panic!()
    };
    let Json::Obj(v) = &mut snapshots[0] else {
        panic!()
    };
    assert_eq!(v["id"], Json::str("v"));
    let Json::Arr(subjects) = v.get_mut("subjects").unwrap() else {
        panic!()
    };
    subjects.push(Json::obj([
        ("id", Json::str("next")),
        ("type", Json::str("Paths.Hop")),
        ("origin", Json::str("v")),
    ]));
    let Json::Arr(atoms) = v.get_mut("atoms").unwrap() else {
        panic!()
    };
    for a in atoms.iter_mut() {
        let Json::Obj(a) = a else { panic!() };
        let Json::Str(subject) = &a["subject"] else {
            panic!()
        };
        let subject = subject.clone();
        if ["p", "q", "r"].contains(&subject.as_str()) {
            if a["field"] == Json::str("Paths.Node.links") {
                a.insert(
                    "value".into(),
                    Json::Arr(vec![
                        reference(&subject),
                        reference(&subject),
                        reference(&subject),
                    ]),
                );
            }
            if a["field"] == Json::str("Paths.Node.members") {
                a.insert("value".into(), Json::Arr(vec![reference(&subject)]));
            }
        }
    }
    for (name, subject) in [("owner", "A"), ("from", "q"), ("to", "r")] {
        atoms.push(Json::obj([
            ("id", Json::str(&format!("next-{name}"))),
            ("subject", Json::str("next")),
            ("field", Json::str(&format!("Paths.Hop.{name}"))),
            ("value", reference(subject)),
            ("origin", Json::str("v")),
        ]));
    }
    let law = String::from_utf8(original.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, &format!("{}{SCRIPT}", base::SCRIPT));
    InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        map.canonical().into_bytes(),
    )
}
