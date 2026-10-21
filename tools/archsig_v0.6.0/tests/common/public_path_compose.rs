// 原始観測fixtureとLawのPath view。期待値は実装から生成しない。
use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
mod base {
    use super::fixture_archsig as archsig;
    include!("composed_paths.rs");
}
pub fn input(missing: bool, revision: &str) -> InputSources {
    let original = base::input(missing, revision);
    let law = String::from_utf8(original.law().bytes().to_vec()).unwrap();
    let at = law.rfind('}').unwrap();
    let extra = r#"
view identityAt(x:Node):Path<Node,Node> =identity(x);
view absentPath(e:Hop):Option<Path<Node,Node>> =none<Path<Node,Node>>;
view wrapped(p:Path<Node,Node>):Option<List<Path<Node,Node>>> =some(list<Path<Node,Node>>[p]);
view samePaths(a:Path<Node,Node>,b:Path<Node,Node>):Bool=a=b;
"#;
    let law = format!("{}{}{}", &law[..at], extra, &law[at..]);
    InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        original.archmap().bytes().to_vec(),
    )
}
pub const E: &str = "e=evaluate(Walk.step,e=@v/e)";
pub const F: &str = "f=evaluate(Walk.step,e=@v/next)";
pub const C: &str = "c=compose($e.value,then=$f.value)";
