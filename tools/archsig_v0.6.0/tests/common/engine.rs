// 既存の有限構文木fixture。生成IRや全称の結論は入力しない。
pub const DEFINITIONS: &[u8] = include_bytes!("../fixtures/engine.atoms.json");
pub const LAW: &[u8] = include_bytes!("../fixtures/engine.law");
pub const MAP: &[u8] = include_bytes!("../fixtures/engine.archmap.json");
pub const WRAPPERS: &str = r#"
  law required matched(c:Compiler):forall x:Z . match c.operator {
    AddOp=>evalIR(Engine.IR.Load,x)=x;
    SubtractOp=>evalIR(Engine.IR.Load,x)=x+1;
  };
  view seed():Z=1;
  law required prior(): false;
  view generated(c:Compiler):IR = translate(c.source,c.operator);
  view sourceAt(c:Compiler):Z = evalSource(c.source,5);
  view irAt(c:Compiler):Z = evalIR(translate(c.source,c.operator),5);
"#;
pub fn law(wrappers: bool) -> Vec<u8> {
    if !wrappers {
        return LAW.to_vec();
    }
    let s = std::str::from_utf8(LAW).unwrap();
    let end = s.rfind('}').unwrap();
    format!("{}{}{}", &s[..end], WRAPPERS, &s[end..]).into_bytes()
}
pub fn map(missing: bool, revision: Option<&str>) -> Vec<u8> {
    let mut s = std::str::from_utf8(MAP).unwrap().to_string();
    if missing {
        let line = s
            .lines()
            .find(|l| l.contains("\"add-operator\""))
            .unwrap()
            .to_string();
        s = s.replace(&(line + "\n"), "");
    }
    if let Some(revision) = revision {
        s=s.replace("\"sources\": []",&format!(r#""sources": [{{"id":"scan","uri":"urn:fixture:engine","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}]"#));
        s = s.replace(
            "\"locations\": []",
            r#""locations": [{"source":"scan","path":"engine.model","span":[0,1]}]"#,
        );
    }
    s.into_bytes()
}

pub fn smaller(missing: bool, revision: Option<&str>) -> Vec<u8> {
    let mut s = String::from_utf8(map(missing, revision)).unwrap();
    let original = s
        .lines()
        .find(|l| l.contains("\"add-source\""))
        .unwrap()
        .split("\"value\": ")
        .nth(1)
        .unwrap()
        .split(", \"origin\"")
        .next()
        .unwrap()
        .to_string();
    assert_eq!(s.matches(&original).count(), 2);
    s = s.replace(
        &original,
        r#"{"tag":"Add","args":[{"tag":"Var","args":[]},{"tag":"Lit","args":["1"]}]}"#,
    );
    s.into_bytes()
}
