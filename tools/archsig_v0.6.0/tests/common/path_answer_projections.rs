use archsig_input::input::InputSources;
#[allow(dead_code)]
mod identities {

    include!("identity_paths.rs");
}
#[allow(dead_code)]
mod arrows {

    include!("internal_paths.rs");
}
#[allow(dead_code)]
mod composed {

    include!("composed_paths.rs");
}
#[allow(dead_code)]
mod correspondences {

    include!("correspondence_paths.rs");
}
pub fn identity(moved: bool) -> InputSources {
    identities::input(moved)
}
fn extend(input: InputSources, marker: &str, declarations: &str) -> InputSources {
    let law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(marker).count(), 1);
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.replace(marker, &(marker.to_owned() + declarations))
            .into_bytes(),
        input.archmap().bytes().to_vec(),
    )
}
pub const INTERNAL: &str = r#"
view keep_node(x:Node):Node=x;
view keep_bool(x:Bool):Bool=x;
view own_node(a:Root,x:Node[a]):Node=x;
view keep_hop(e:Hop):Hop=e;
view identity_node(x:Node):Path<Node,Node> =identity(x);
law required node_equal(x:Node,y:Node):x=y;
"#;
pub fn internal(mode: &str, revision: &str) -> InputSources {
    extend(arrows::input(mode, revision), arrows::SCRIPT, INTERNAL)
}
pub fn composed(missing: bool, revision: &str) -> InputSources {
    extend(
        composed::input(missing, revision),
        composed::SCRIPT,
        INTERNAL,
    )
}
pub fn correspondence(mode: &str, revision: &str) -> InputSources {
    extend(
        correspondences::input(mode, revision),
        correspondences::SCRIPT,
        r#"
view keep_system(a:System):System=a;
view keep_migration(m:Migration):Migration=m;
view keep_reserve(r:Reserve):Reserve=r;
"#,
    )
}
