use archsig_input::input::InputSources;
pub fn sources(parts: &[(&str, bool, &str)], body: &str) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pattern","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pattern.Root","meaning":"Root","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Pattern.Part","meaning":"Flag","parameters":[{"name":"owner","type":["Ref","Pattern.Root"],"meaning":"Owner"}],"fields":[{"name":"flag","type":"Bool","meaning":"Value"},{"name":"label","type":"Text","meaning":"Role"},{"name":"link","type":["Ref","Pattern.Part"],"meaning":"Related flag"}],"alignments":[]}]}]}"#;
    let checked =
        archsig_input::definition::check_definitions(&[("definition0", definitions.as_bytes())])
            .expect("finite repair definitions");
    let digest = &checked.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";{body}}}"
    );
    let mut subjects = vec![r#"{"id":"root","type":"Pattern.Root","origin":"model"}"#.to_owned()];
    let mut atoms = vec![];
    for (id, value, link) in parts {
        subjects.push(format!(
            r#"{{"id":"{id}","type":"Pattern.Part","origin":"model"}}"#
        ));
        atoms.extend([
            format!(r#"{{"id":"owner-{id}","subject":"{id}","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"}}"#),
            format!(r#"{{"id":"flag-{id}","subject":"{id}","field":"Pattern.Part.flag","value":{value},"origin":"model"}}"#),
            format!(r#"{{"id":"label-{id}","subject":"{id}","field":"Pattern.Part.label","value":"{id}","origin":"model"}}"#),
            format!(r#"{{"id":"link-{id}","subject":"{id}","field":"Pattern.Part.link","value":["v","{link}"],"origin":"model"}}"#),
        ]);
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pattern","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"Finite repair fixture","locations":[],"note":"Exact finite selection"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{}],"atoms":[{}]}}]}}"#,
        subjects.join(","),
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
pub fn input(extra: &str) -> InputSources {
    sources(
        &[("p", true, "p"), ("q", false, "q")],
        &format!(
            "view all(r:Root):Set<Part> =Part[r];view flag(c:Part):Bool=c.flag;change choose(c:Part,p:Bool,q:Bool)=c with {{flag=p}};law required valid(c:Part):c.flag;{extra}"
        ),
    )
}
pub fn six(cross: bool) -> InputSources {
    let extra = if cross {
        r#"else if c.label="a" then c.flag=c.link.flag"#
    } else {
        ""
    };
    sources(
        &[
            ("x", false, "y"),
            ("y", false, "z"),
            ("z", false, "z"),
            ("a", false, "b"),
            ("b", false, "a"),
            ("c", false, "c"),
        ],
        &format!(
            r#"
        view internal(r:Root):Set<Part> =set {{c|c in Part[r] where c.label!="x" and c.label!="y" and c.label!="z"}};
        view xy(r:Root):Set<Part> =set {{c|c in Part[r] where c.label="x" or c.label="y"}};
        view xyz(r:Root):Set<Part> =set {{c|c in Part[r] where c.label="x" or c.label="y" or c.label="z"}};
        change choose(c:Part,p:Bool)=c with {{flag=p}};
        law required valid(r:Root):forall c in Part[r]. if c.label="x" then c.flag and c.flag=c.link.flag else if c.label="y" then c.flag=c.link.flag {extra} else true;
    "#
        ),
    )
}
