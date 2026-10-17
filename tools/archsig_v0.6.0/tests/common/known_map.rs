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
