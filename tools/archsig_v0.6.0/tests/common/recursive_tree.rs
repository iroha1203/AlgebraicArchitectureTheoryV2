// 既知の有限木。型全域の標本としては使わない。
pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Trees","version":"1","dependencies":[],"declarations":[{"kind":"data","name":"Trees.Tree","meaning":"有限木","constructors":[{"name":"Empty","arguments":[],"meaning":"空"},{"name":"Leaf","arguments":["Z"],"meaning":"葉"},{"name":"Branch","arguments":[["Data","Trees.Tree"],["Data","Trees.Tree"]],"meaning":"分岐"},{"name":"Packed","arguments":[["Tuple",["Data","Trees.Tree"],["Option",["Data","Trees.Tree"]],["List",["Data","Trees.Tree"]]]],"meaning":"正の再帰包装"}]},{"kind":"entity","name":"Trees.Sample","meaning":"観測対象","parameters":[],"fields":[{"name":"tree","type":["Data","Trees.Tree"],"meaning":"有限木"}],"alignments":[]}]}]}"#;

pub const SCRIPT: &str = r#"
  view total(t:Tree):Z = match t { Empty=>0; Leaf(n)=>n; Branch(l,r)=>total(l)+total(r); Packed(_)=>0; };
  view copy(t:Tree):Tree = match t { Empty=>Empty; Leaf(n)=>Leaf(n); Branch(l,r)=>Branch(copy(l),copy(r)); Packed(p)=>Packed(p); };
  view read(s:Sample):Z = total(s.tree);
  view raw(s:Sample):Tree = s.tree;
  view copied(s:Sample):Tree = copy(s.tree);
  view wrapped(s:Sample):Tree = Packed((s.tree,some(s.tree),list<Tree>[Empty,s.tree]));
  view same(s:Sample):Bool = copy(s.tree)=s.tree;
  view constant(t:Tree):Z = 9;
  view ignores(s:Sample):Z = constant(s.tree);
  law required four(s:Sample): total(s.tree)=4;
"#;

pub const TREE: &str = r#"{"tag":"Branch","args":[{"tag":"Leaf","args":["2"]},{"tag":"Branch","args":[{"tag":"Leaf","args":["2"]},{"tag":"Empty","args":[]}]}]}"#;

pub fn law(digest: &str, extra: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Trees {{ use vocabulary Trees version \"1\" digest \"{digest}\"; {SCRIPT} {extra} }}"
    )
}

pub fn archmap(digest: &str, missing: bool, revision: &str) -> String {
    let atoms = if missing {
        String::new()
    } else {
        format!(
            r#"{{"id":"tree","subject":"sample","field":"Trees.Sample.tree","value":{TREE},"origin":"values"}}"#
        )
    };
    format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Trees","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"urn:fixture:recursive-tree","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"base","mode":"specification","method":"対象の提示","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},{{"id":"values","mode":"specification","method":"有限木の観測","locations":[{{"source":"scan","path":"tree.model","span":[2,5]}}]}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Trees.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    )
}
