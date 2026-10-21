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

// 可視性の原始三入力をRustテスト内に保持し、期待値は各assertionで独立に定める。
pub fn visibility_input() -> InputSources {
    const DEFINITIONS: &str = r##"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"declarations":[{"alignments":[],"fields":[],"kind":"arrow","meaning":"同じシステム内の予約操作。","name":"Reservations.Reserve","parameters":[{"meaning":"操作が所属するシステム。","name":"owner","type":["Ref","Reservations.System"]},{"meaning":"操作前の状態。","name":"from","type":["Owned","Reservations.State","owner"]},{"meaning":"操作後の状態。","name":"to","type":["Owned","Reservations.State","owner"]}]},{"alignments":[],"fields":[{"meaning":"この状態の空き数量。","name":"free","type":"Z"},{"meaning":"この状態の確保数量。","name":"held","type":"Z"}],"kind":"entity","meaning":"ある時点の空き数量と確保数量を持つ状態。","name":"Reservations.State","parameters":[{"meaning":"状態が所属するシステム。","name":"owner","type":["Ref","Reservations.System"]}]},{"alignments":[],"fields":[],"kind":"entity","meaning":"予約状態と操作が所属する一つのシステム。","name":"Reservations.System","parameters":[]}],"dependencies":[],"namespace":"Reservations","semantics":"archsig/0.6.0","version":"1"},{"declarations":[{"alignments":[],"fields":[],"kind":"arrow","meaning":"別readingの内部arrow。","name":"Hidden.Hop","parameters":[{"meaning":"所属。","name":"owner","type":["Ref","Reservations.System"]},{"meaning":"始点。","name":"from","type":["Owned","Reservations.State","owner"]},{"meaning":"終点。","name":"to","type":["Owned","Reservations.State","owner"]}]}],"dependencies":[{"digest":"sha256:d0f6c9dcbc921c4529eac0c3abb6374f9ee272ef901fe77b7113aae5755d4100","namespace":"Reservations","version":"1"}],"namespace":"Hidden","semantics":"archsig/0.6.0","version":"1"}]}"##;
    const LAW: &str = r##"law "archsig.law/2" semantics "archsig/0.6.0";
reading Reservations { use vocabulary Reservations version "1" digest "sha256:d0f6c9dcbc921c4529eac0c3abb6374f9ee272ef901fe77b7113aae5755d4100";
view route(e:Reserve):Path<State,State> =path(e);
view stay(s:State):Path<State,State> =identity(s); }
reading Alternative { use vocabulary Reservations version "1" digest "sha256:d0f6c9dcbc921c4529eac0c3abb6374f9ee272ef901fe77b7113aae5755d4100";
use vocabulary Hidden version "1" digest "sha256:331f93a88540c0f81fb0b2d90e7ba0df91fce59ce5c970797d3ed500c25de30a";
view route(e:Hidden.Hop):Path<Reservations.State,Reservations.State> =path(e); view common(e:Reservations.Reserve):Path<Reservations.State,Reservations.State> =path(e);
view stay(s:Reservations.State):Path<Reservations.State,Reservations.State> =identity(s);
}"##;
    const ARCHMAP: &str = r##"{"format":"archsig.archmap/2","origins":[{"id":"model","locations":[],"method":"二つのシステムの状態・操作・移行候補を有限な原始事実で提示する。","mode":"specification","note":"状態の数量と候補対応の仕様例。成立・残差・修復は入力しない。"}],"semantics":"archsig/0.6.0","snapshots":[{"atoms":[{"field":"Reservations.State.owner","id":"p-owner","origin":"model","subject":"p","value":["v","A"]},{"field":"Reservations.State.free","id":"p-free","origin":"model","subject":"p","value":"2"},{"field":"Reservations.State.held","id":"p-held","origin":"model","subject":"p","value":"0"},{"field":"Reservations.State.owner","id":"q-owner","origin":"model","subject":"q","value":["v","A"]},{"field":"Reservations.State.free","id":"q-free","origin":"model","subject":"q","value":"1"},{"field":"Reservations.State.held","id":"q-held","origin":"model","subject":"q","value":"1"},{"field":"Reservations.State.owner","id":"r-owner","origin":"model","subject":"r","value":["v","B"]},{"field":"Reservations.State.free","id":"r-free","origin":"model","subject":"r","value":"4"},{"field":"Reservations.State.held","id":"r-held","origin":"model","subject":"r","value":"0"},{"field":"Reservations.State.owner","id":"s-owner","origin":"model","subject":"s","value":["v","B"]},{"field":"Reservations.State.free","id":"s-free","origin":"model","subject":"s","value":"3"},{"field":"Reservations.State.held","id":"s-held","origin":"model","subject":"s","value":"1"},{"field":"Reservations.Reserve.owner","id":"e-owner","origin":"model","subject":"e","value":["v","A"]},{"field":"Reservations.Reserve.from","id":"e-from","origin":"model","subject":"e","value":["v","p"]},{"field":"Reservations.Reserve.to","id":"e-to","origin":"model","subject":"e","value":["v","q"]},{"field":"Reservations.Reserve.owner","id":"f-owner","origin":"model","subject":"f","value":["v","B"]},{"field":"Reservations.Reserve.from","id":"f-from","origin":"model","subject":"f","value":["v","r"]},{"field":"Reservations.Reserve.to","id":"f-to","origin":"model","subject":"f","value":["v","s"]},{"field":"Hidden.Hop.owner","id":"h-owner","origin":"model","subject":"h","value":["v","A"]},{"field":"Hidden.Hop.from","id":"h-from","origin":"model","subject":"h","value":["v","q"]},{"field":"Hidden.Hop.to","id":"h-to","origin":"model","subject":"h","value":["v","p"]},{"field":"Reservations.Reserve.owner","id":"k-owner","origin":"model","subject":"k","value":["v","A"]},{"field":"Reservations.Reserve.from","id":"k-from","origin":"model","subject":"k","value":["v","p"]},{"field":"Reservations.Reserve.to","id":"k-to","origin":"model","subject":"k","value":["v","q"]},{"field":"Reservations.Reserve.owner","id":"l-owner","origin":"model","subject":"l","value":["v","B"]},{"field":"Reservations.Reserve.from","id":"l-from","origin":"model","subject":"l","value":["v","s"]},{"field":"Reservations.Reserve.to","id":"l-to","origin":"model","subject":"l","value":["v","r"]},{"field":"Reservations.Reserve.owner","id":"t-owner","origin":"model","subject":"t","value":["v","B"]},{"field":"Reservations.Reserve.from","id":"t-from","origin":"model","subject":"t","value":["v","r"]},{"field":"Reservations.Reserve.to","id":"t-to","origin":"model","subject":"t","value":["v","s"]}],"id":"v","origin":"model","subjects":[{"id":"A","origin":"model","type":"Reservations.System"},{"id":"B","origin":"model","type":"Reservations.System"},{"id":"p","origin":"model","type":"Reservations.State"},{"id":"q","origin":"model","type":"Reservations.State"},{"id":"r","origin":"model","type":"Reservations.State"},{"id":"s","origin":"model","type":"Reservations.State"},{"id":"e","origin":"model","type":"Reservations.Reserve"},{"id":"f","origin":"model","type":"Reservations.Reserve"},{"id":"h","origin":"model","type":"Hidden.Hop"},{"id":"k","origin":"model","type":"Reservations.Reserve"},{"id":"l","origin":"model","type":"Reservations.Reserve"},{"id":"t","origin":"model","type":"Reservations.Reserve"}]}],"sources":[],"vocabularies":[{"digest":"sha256:d0f6c9dcbc921c4529eac0c3abb6374f9ee272ef901fe77b7113aae5755d4100","namespace":"Reservations","version":"1"},{"digest":"sha256:331f93a88540c0f81fb0b2d90e7ba0df91fce59ce5c970797d3ed500c25de30a","namespace":"Hidden","version":"1"}]}"##;
    InputSources::from_bytes(
        vec![DEFINITIONS.as_bytes().to_vec()],
        LAW.as_bytes().to_vec(),
        ARCHMAP.as_bytes().to_vec(),
    )
}
