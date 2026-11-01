use archsig_input::input::InputSources;

pub const DATA: &str = r#"
{"kind":"data","name":"Pair.Token","meaning":"選択値。","constructors":[{"name":"Empty","meaning":"空。","arguments":[]},{"name":"Left","meaning":"左。","arguments":["Bool"]},{"name":"Right","meaning":"右。","arguments":["Bool"]},{"name":"Both","meaning":"順序対。","arguments":["Bool","Bool"]}]},
{"kind":"data","name":"Pair.Other","meaning":"別の型。","constructors":[{"name":"Left","meaning":"左。","arguments":["Bool"]}]},
{"kind":"data","name":"Pair.Packet","meaning":"包装値。","constructors":[{"name":"Wrap","meaning":"包む。","arguments":[["Tuple",["Option",["Data","Pair.Token"]],["List",["Data","Pair.Token"]],["Set",["Data","Pair.Token"]]]]}]},
{"kind":"data","name":"Pair.Tree","meaning":"有限木。","constructors":[{"name":"End","meaning":"終端。","arguments":[]},{"name":"Leaf","meaning":"葉。","arguments":["Bool"]},{"name":"Branch","meaning":"分岐。","arguments":[["Data","Pair.Tree"],["Data","Pair.Tree"]]},{"name":"Packed","meaning":"正の再帰。","arguments":[["Tuple",["Data","Pair.Tree"],["Option",["Data","Pair.Tree"]],["List",["Data","Pair.Tree"]]]]}]}
"#;

pub fn sources(extra_definitions: &str, body: &str) -> InputSources {
    let extra = if extra_definitions.is_empty() {
        String::new()
    } else {
        format!(",{extra_definitions}")
    };
    let d = format!(
        r#"{{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{{"kind":"entity","name":"Pair.State","meaning":"二つの条件。","parameters":[],"fields":[{{"name":"x","type":"Bool","meaning":"第一条件。"}},{{"name":"y","type":"Bool","meaning":"第二条件。"}}],"alignments":[]}},{DATA}{extra}]}}]}}"#
    );
    let checked = archsig_input::definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pair"].digest;
    let a = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"有限候補のData商。","note":"独立した有限入力。","locations":[]}}],"snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"s","type":"Pair.State","origin":"o"}}],"atoms":[{{"id":"x","subject":"s","field":"Pair.State.x","value":false,"origin":"o"}},{{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}}]}}]}}"#
    );
    let l = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Pair{{use vocabulary Pair version \"1\" digest \"{digest}\";change choose(s:State,a:Bool,b:Bool)=s with{{x=a,y=b}};law required valid(s:State):s.x;{body}}}"
    );
    InputSources::from_bytes(vec![d.into_bytes()], l.into_bytes(), a.into_bytes())
}
