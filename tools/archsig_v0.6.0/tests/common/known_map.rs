pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Maps","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Maps.Item","meaning":"Item","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Maps.Void","meaning":"Void","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Maps.Sample","meaning":"Sample","parameters":[],"fields":[{"name":"m","type":["Map",["Ref","Maps.Item"],["Ref","Maps.Item"]],"meaning":"m"},{"name":"n","type":["Map",["Ref","Maps.Item"],["Ref","Maps.Item"]],"meaning":"n"},{"name":"different","type":["Map",["Ref","Maps.Item"],["Ref","Maps.Item"]],"meaning":"different"},{"name":"missing","type":["Map",["Ref","Maps.Item"],["Ref","Maps.Item"]],"meaning":"missing"},{"name":"empty","type":["Map",["Ref","Maps.Void"],["Ref","Maps.Void"]],"meaning":"empty"}],"alignments":[]}]}]}"#;
pub const SCRIPT: &str = r#"
view read(s:Sample):Map<Item,Item> = s.m;
view equal(s:Sample):Bool = s.m=s.n;
view unequal(s:Sample):Bool = s.m!=s.different;
view wrapped(s:Sample):(Map<Item,Item>,Option<Map<Item,Item>>,List<Map<Item,Item>>,Set<Map<Item,Item>>) = let x=s.m in (x,some(x),list<Map<Item,Item>>[x,s.n],set<Map<Item,Item>>{x,s.n});
view choice(s:Sample):Map<Item,Item> = if true then read(s) else s.different;
view absent(s:Sample):Map<Item,Item> = s.missing;
view empty(s:Sample):Map<Void,Void> = s.empty;
view seed():Z = 1;
law required prior(): false;
law required same(s:Sample):s.m=s.n;
law required changed(s:Sample):s.m=s.different;
"#;
pub fn law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Maps {{ use vocabulary Maps version \"1\" digest \"{digest}\"; {SCRIPT} }}"
    )
}
pub fn archmap(digest: &str, revision: &str) -> String {
    format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Maps","version":"1","digest":"{digest}"}}],"sources":[{{"id":"src","uri":"urn:fixture:known-map","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{{"id":"base","mode":"specification","method":"registered values","locations":[{{"source":"src","path":"maps.model","span":[0,2]}}]}}],"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"a","type":"Maps.Item","origin":"base"}},{{"id":"b","type":"Maps.Item","origin":"base"}},{{"id":"s","type":"Maps.Sample","origin":"base"}}],"atoms":[{{"id":"m","subject":"s","field":"Maps.Sample.m","value":[[["v","a"],["v","a"]],[["v","b"],["v","a"]]],"origin":"base"}},{{"id":"n","subject":"s","field":"Maps.Sample.n","value":[[["v","b"],["v","a"]],[["v","a"],["v","a"]]],"origin":"base"}},{{"id":"different","subject":"s","field":"Maps.Sample.different","value":[[["v","a"],["v","b"]],[["v","b"],["v","a"]]],"origin":"base"}},{{"id":"empty","subject":"s","field":"Maps.Sample.empty","value":[],"origin":"base"}}]}}]}}"#
    )
}

pub const OWNED_DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Maps","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Maps.Root","meaning":"Root","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Maps.Item","meaning":"Item","parameters":[{"name":"owner","type":["Ref","Maps.Root"],"meaning":"owner"}],"fields":[],"alignments":[]},{"kind":"entity","name":"Maps.Holder","meaning":"Holder","parameters":[{"name":"owner","type":["Ref","Maps.Root"],"meaning":"owner"}],"fields":[{"name":"tables","type":["List",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"tables"},{"name":"bag","type":["Set",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"bag"},{"name":"maybe","type":["Option",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"maybe"},{"name":"emptylist","type":["List",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"emptylist"},{"name":"emptyset","type":["Set",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"emptyset"},{"name":"absent","type":["Option",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]],"meaning":"none"},{"name":"nested","type":["Tuple","Unit",["List",["Option",["Map",["Owned","Maps.Item","owner"],["Owned","Maps.Item","owner"]]]]],"meaning":"nested"}],"alignments":[]}]}]}"#;
pub fn owned_archmap(digest: &str) -> String {
    r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Maps","version":"1","digest":"DIGEST"}],"sources":[{"id":"src","uri":"urn:fixture:owned-map-wrapper","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}],"origins":[{"id":"base","mode":"specification","method":"owned map observations","locations":[{"source":"src","path":"owned.model","span":[0,3]}]}],"snapshots":[{"id":"v","origin":"base","subjects":[{"id":"r","type":"Maps.Root","origin":"base"},{"id":"a","type":"Maps.Item","origin":"base"},{"id":"h","type":"Maps.Holder","origin":"base"}],"atoms":[{"id":"a-owner","subject":"a","field":"Maps.Item.owner","value":["v","r"],"origin":"base"},{"id":"h-owner","subject":"h","field":"Maps.Holder.owner","value":["v","r"],"origin":"base"},{"id":"tables","subject":"h","field":"Maps.Holder.tables","value":[[[["v","a"],["v","a"]]]],"origin":"base"},{"id":"bag","subject":"h","field":"Maps.Holder.bag","value":[[[["v","a"],["v","a"]]]],"origin":"base"},{"id":"maybe","subject":"h","field":"Maps.Holder.maybe","value":{"some":[[["v","a"],["v","a"]]]},"origin":"base"},{"id":"emptylist","subject":"h","field":"Maps.Holder.emptylist","value":[],"origin":"base"},{"id":"emptyset","subject":"h","field":"Maps.Holder.emptyset","value":[],"origin":"base"},{"id":"none","subject":"h","field":"Maps.Holder.absent","value":{"none":true},"origin":"base"},{"id":"nested","subject":"h","field":"Maps.Holder.nested","value":[[],[{"some":[[["v","a"],["v","a"]]]}]],"origin":"base"}]}]}"#.replace("DIGEST",digest)
}
pub fn owned_law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Maps {{ use vocabulary Maps version \"1\" digest \"{digest}\"; view tables(s:Holder):List<Map<Item,Item>> = s.tables;view bag(s:Holder):Set<Map<Item,Item>> = s.bag;view maybe(s:Holder):Option<Map<Item,Item>> = s.maybe;view emptylist(s:Holder):List<Map<Item,Item>> = s.emptylist;view emptyset(s:Holder):Set<Map<Item,Item>> = s.emptyset;view absent(s:Holder):Option<Map<Item,Item>> = s.absent;view nested(s:Holder):(Unit,List<Option<Map<Item,Item>>>) = s.nested; }}"
    )
}
