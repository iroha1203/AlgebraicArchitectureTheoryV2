//! 公開候補域と解集合を混同しない有限view商。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::{definition, json::{JNode, JValue}};
use cli::*;
fn input(name: &str) -> std::path::PathBuf {
    let d = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの条件。","parameters":[],"fields":[{"name":"x","type":"Bool","meaning":"第一条件。"},{"name":"y","type":"Bool","meaning":"第二条件。"}],"alignments":[]}]}]}"#;
    let checked = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Pair"].digest;
    let a=r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pair","version":"1","digest":"@D@"}],"sources":[],"origins":[{"id":"o","mode":"specification","method":"有限商の独立試験。","locations":[],"note":"候補と解を分ける。"}],"snapshots":[{"id":"v","origin":"o","subjects":[{"id":"s","type":"Pair.State","origin":"o"}],"atoms":[{"id":"x","subject":"s","field":"Pair.State.x","value":false,"origin":"o"},{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}]}]}"#.replace("@D@",digest);
    let l = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Pair{{use vocabulary Pair version \"1\" digest \"{digest}\";change choose(s:State,a:Bool,b:Bool)=s with{{x=a,y=b}};law required valid(s:State):s.x;law optional empty(s:State):false;view last(s:State):Bool=s.y;}}"
    );
    let dir = workdir(name);
    for (n, v) in [("d.json", d), ("a.json", a.as_str()), ("l.law", l.as_str())] {
        std::fs::write(dir.join(n), v).unwrap();
    }
    dir
}
fn execute(dir: &std::path::Path, out: &str, asks: &[&str], reuse: Option<&str>) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        out,
        "--time-ms",
        "120000",
    ];
    if let Some(reuse) = reuse {
        args.extend(["--reuse", reuse]);
    }
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    run(dir, &args)
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn quotient<'a>(result: &'a JNode, index: usize) -> &'a JNode {
    get(
        node(
            result,
            get(
                get(&arr(get(result, "answers"))[index], "outputs"),
                "quotient",
            ),
        ),
        "value",
    )
}
fn fiber_sizes(result: &JNode, index: usize) -> Vec<usize> {
    let q = quotient(result, index);
    let fibers = arr(get(get(q, "representation"), "fibers"));
    let mut sizes = vec![];
    for fiber in fibers {
        let class = node(result, get(fiber, "image"));
        let preimage = node(result, get(fiber, "preimage"));
        let points = arr(get(get(preimage, "value"), "elements"));
        assert_eq!(arr(get(class, "value")).len(), points.len());
        sizes.push(points.len());
    }
    let projection = node(result, get(q, "projection"));
    assert_eq!(
        arr(get(get(projection, "value"), "pairs")).len(),
        sizes.iter().sum::<usize>()
    );
    sizes.sort();
    sizes
}
fn pair(value: &JNode) -> (bool, bool) {
    let values=arr(value);
    assert_eq!(values.len(),2);
    let boolean=|v:&JNode| match &v.value { JValue::Bool(b)=>*b, _=>panic!("expected Bool") };
    (boolean(&values[0]),boolean(&values[1]))
}
fn members(value: &JNode) -> Vec<(bool,bool)> {
    let mut values=arr(value).iter().map(pair).collect::<Vec<_>>();
    values.sort();values
}
fn exact_fibers(result: &JNode, index: usize, mut expected: Vec<Vec<(bool,bool)>>) {
    for class in &mut expected {class.sort();}
    expected.sort();
    let q=quotient(result,index);
    let class_domain=node(result,get(q,"classes"));
    let mut actual=arr(get(get(class_domain,"value"),"elements")).iter()
        .map(|r|members(get(node(result,r),"value"))).collect::<Vec<_>>();
    actual.sort();assert_eq!(actual,expected);
    let mut fibers=vec![];
    for fiber in arr(get(get(q,"representation"),"fibers")) {
        let class=members(get(node(result,get(fiber,"image")),"value"));
        let preimage=node(result,get(fiber,"preimage"));
        let mut points=arr(get(get(preimage,"value"),"elements")).iter()
            .map(|r|pair(get(node(result,r),"value"))).collect::<Vec<_>>();
        points.sort();assert_eq!(points,class);
        fibers.push(class);
    }
    fibers.sort();assert_eq!(fibers,expected);
    let projection=node(result,get(q,"projection"));
    let mut pairs=arr(get(get(projection,"value"),"pairs")).iter().map(|p| {
        let p=arr(p);assert_eq!(p.len(),2);
        (pair(get(node(result,&p[0]),"value")),members(get(node(result,&p[1]),"value")))
    }).collect::<Vec<_>>();
    let mut expected_pairs=expected.iter().flat_map(|class|
        class.iter().map(|point|(*point,class.clone()))).collect::<Vec<_>>();
    pairs.sort();expected_pairs.sort();assert_eq!(pairs,expected_pairs);
}
#[test]
fn finite_quotient_distinguishes_all_candidates_from_solutions_and_reuses() {
    let dir = input("quotient-domains");
    let asks = [
        "all=quotient(Pair.last,on=$s.domain,s=@v/s)",
        "good=quotient(Pair.last,on=$s.solutions,s=@v/s)",
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let original = result_json(&dir, &first);
    for request in &arr(get(&original, "requests"))[..2] {
        let defaults=arr(get(request,"defaults"));
        assert_eq!(defaults.len(),1);
        assert_eq!(s(get(&defaults[0],"rule")),"no_law_check");
    }
    assert_eq!(fiber_sizes(&original, 0), vec![2, 2]);
    assert_eq!(fiber_sizes(&original, 1), vec![1, 1]);
    exact_fibers(&original,0,vec![vec![(false,false),(true,false)],vec![(false,true),(true,true)]]);
    exact_fibers(&original,1,vec![vec![(true,false)],vec![(true,true)]]);
    let repeated = execute(&dir, "out2", &asks, Some("out"));
    assert_eq!(repeated.code, 0, "{} {}", repeated.stdout, repeated.stderr);
    let reused = result_json(&dir, &repeated);
    for key in ["answers", "nodes"] {
        assert_eq!(get(&original, key).value, get(&reused, key).value);
    }
}
#[test]
fn empty_solution_quotient_keeps_its_type_and_has_no_fibers() {
    let dir = input("quotient-empty");
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.empty,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.solutions,s=@v/s)",
        ],
        None,
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    assert!(fiber_sizes(&result, 1).is_empty());
    let classes = node(&result, get(quotient(&result, 1), "classes"));
    assert_eq!(s(&arr(get(get(classes, "value"), "type"))[0]), "Set");
    assert!(arr(get(get(classes, "value"), "elements")).is_empty());
    assert!(!arr(get(classes,"arguments")).is_empty());
    assert_eq!(get(classes,"scope").value,get(&arr(get(&result,"answers"))[1],"scope").value);
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "established"
    );
}

#[test]
fn quotient_rejects_wrong_domain_missing_bindings_private_fields_and_cycles() {
    let cases: &[&[&str]] = &[
        &["v=evaluate(Pair.last,s=@v/s)", "q=quotient(Pair.last,on=$v.value,s=@v/s)"],
        &["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)", "q=quotient(Pair.last,on=$s.domain)"],
        &["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)", "q=quotient(Pair.last,on=$s.domain,s=@v/s)", "v=evaluate(Pair.last,s=$q.quotient.representation)"],
        &["q=quotient(Pair.last,on=$q.quotient.domain,s=@v/s)"],
    ];
    for (i, asks) in cases.iter().enumerate() {
        let dir=input(&format!("quotient-static-{i}"));let r=execute(&dir,"out",asks,None);
        assert_eq!(r.code,64,"{} {}",r.stdout,r.stderr);
        assert!(!has(&r.receipt,"result"));
    }
}

#[test]
fn stopped_quotient_keeps_prior_solve_without_publishing_incomplete_classes() {
    use archsig::observed::{control::{Checkpoint,Control,Limits,Usage},input::InputSources,evaluate::evaluate_observed_bytes};
    use std::{cell::Cell,rc::Rc};
    let dir=law_input("quotient-stop","law optional same(s:State,b:Bool):s.x=b;");
    for case in 0..6 {
        let mode=case%3;
        let seen=Rc::new(Cell::new(0));let count=seen.clone();
        let mut c=Control::new(Limits{time_ms:Some(1),memory_mib:Some(1)},move|point|{
            if point==Checkpoint::Quotient {count.set(count.get()+1);}
            if count.get()==2 {match mode {
                0=>Usage{elapsed_ms:2,..Usage::default()},1=>Usage{memory_mib:2,..Usage::default()},
                _=>Usage{signal:Some(archsig::result::Signal::Term),..Usage::default()},
            }}else{Usage::default()}
        });
        let sources=InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()],std::fs::read(dir.join("l.law")).unwrap(),std::fs::read(dir.join("a.json")).unwrap());
        let quotient=if case<3 {"q=quotient(Pair.last,on=$s.domain,s=@v/s)"} else {"q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.same)"};
        let result=evaluate_observed_bytes(sources,&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",quotient,"later=evaluate(Pair.last,s=@v/s)"],&mut c).unwrap();
        assert_eq!(seen.get(),2);
        let wire=archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();let answers=arr(get(&wire,"answers"));
        assert_eq!(s(get(&answers[0],"status")),"established");assert!(has(get(&answers[0],"outputs"),"solutions"));
        assert!(!has(get(&answers[1],"outputs"),"quotient"));

        for answer in &answers[1..] {
            assert_eq!(s(get(answer,"status")),"undetermined");
            assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))==if mode==2 {"cancelled"}else{"budget_exhausted"}));
        }
    }
}

#[test]
fn quotient_of_new_solutions_reads_the_previous_repaired_state() {
    let dir=input("quotient-repaired");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap().replace("view last", "change toggle(s:State,b:Bool)=s with{x=not s.x,y=b};law optional pinned(s:State):s.x and s.y;law optional opposite(s:State):not s.x;view last");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let r=execute(&dir,"out",&[
        "r=repair(Pair.pinned,on=@v/s,using=Pair.choose,s=@v/s)",
        "s=solve(Pair.opposite,on=$r.object,using=Pair.toggle,s=@v/s)",
        "q=quotient(Pair.last,on=$s.solutions,s=@v/s)"],None);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);assert_eq!(fiber_sizes(&result,2),vec![1,1]);
}

#[test]
fn missing_view_keeps_quotient_undetermined_and_independent_followup_available() {
    let dir=input("quotient-missing");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap()
        .replace("x=a,y=b","x=a").replace("Bool=s.y","Bool=s.x and s.y");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let map=std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(",{\"id\":\"y\",\"subject\":\"s\",\"field\":\"Pair.State.y\",\"value\":false,\"origin\":\"o\"}","");
    std::fs::write(dir.join("a.json"),map).unwrap();
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s)","later=check(Pair.empty,s=@v/s)"];
    let first=execute(&dir,"out",&asks,None);
    assert_eq!(first.code,2,"{} {}",first.stdout,first.stderr);
    let result=result_json(&dir,&first);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[0],"status")),"established");
    assert_eq!(s(get(&answers[1],"status")),"undetermined");
    assert!(!has(get(&answers[1],"outputs"),"quotient"));
    for key in ["snapshots","modes"] {
        assert_eq!(get(get(&answers[1],"scope"),key).value,get(get(&answers[0],"scope"),key).value);
    }
    assert_eq!(s(get(&answers[2],"status")),"refuted");
    let reason=arr(get(&answers[1],"reasons")).iter().find(|r|s(get(r,"code"))=="missing_observation").unwrap();
    assert!(!arr(get(reason,"dependencies")).is_empty());
    assert!(arr(get(reason,"missing")).iter().any(|f|s(get(f,"field"))=="Pair.State.y"));
    let defaults=arr(get(&arr(get(&result,"requests"))[1],"defaults"));
    assert_eq!(defaults.len(),1);assert_eq!(s(get(&defaults[0],"rule")),"no_law_check");
    let second=execute(&dir,"out2",&asks,Some("out"));
    assert_eq!(second.code,2,"{} {}",second.stdout,second.stderr);
    let reused=result_json(&dir,&second);
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&reused,key).value);}
}

#[test]
fn unavailable_view_binding_blocks_quotient_without_breaking_independent_requests() {
    let dir=input("quotient-binding-missing");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap()
        .replace("x=a,y=b","x=a").replace("view last", "view echo(b:Bool):Bool=b;view first(s:State):Bool=s.x;view last");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let map=std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(",{\"id\":\"y\",\"subject\":\"s\",\"field\":\"Pair.State.y\",\"value\":false,\"origin\":\"o\"}","");
    std::fs::write(dir.join("a.json"),map).unwrap();
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.last,s=@v/s)","q=quotient(Pair.echo,on=$s.domain,b=$v.value)",
        "later=check(Pair.empty,s=@v/s)"];
    let first=execute(&dir,"out",&asks,None);
    assert_eq!(first.code,2,"{} {}",first.stdout,first.stderr);
    let result=result_json(&dir,&first);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[0],"status")),"established");
    assert_eq!(s(get(&answers[2],"status")),"undetermined");
    assert!(!has(get(&answers[2],"outputs"),"quotient"));
    assert_eq!(s(get(&answers[3],"status")),"refuted");
    let reasons=arr(get(&answers[2],"reasons"));
    assert!(reasons.iter().any(|r|s(get(r,"code"))=="dependency_blocked"));
    assert!(reasons.iter().any(|r|s(get(r,"code"))=="missing_observation" &&
        arr(get(r,"missing")).iter().any(|f|s(get(f,"field"))=="Pair.State.y")));
    let second=execute(&dir,"out2",&asks,Some("out"));
    assert_eq!(second.code,2,"{} {}",second.stdout,second.stderr);
    let reused=result_json(&dir,&second);
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&reused,key).value);}
    let mut known=asks;
    known[1]="v=evaluate(Pair.first,s=@v/s)";
    let available=execute(&dir,"known",&known,None);
    assert_eq!(available.code,1,"{} {}",available.stdout,available.stderr);
    let complete=result_json(&dir,&available);
    assert_eq!(s(get(&arr(get(&complete,"answers"))[2],"status")),"established");
    exact_fibers(&complete,2,vec![vec![(false,false),(false,true),(true,false),(true,true)]]);
}

#[test]
fn quotient_keeps_view_quantifiers_and_binding_producer_scope() {
    let dir=input("quotient-scope");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap();
    let vocabulary=law.split("reading Pair{").nth(1).unwrap().split(';').next().unwrap();
    let extra=format!("reading Other{{{vocabulary};view flag(s:State):Bool=s.x;}}");
    let law=law.replace("view last", "view all(s:State):Bool=forall b:Bool . b or not b;view echo(b:Bool):Bool=b;view last")+&extra;
    std::fs::write(dir.join("l.law"),law).unwrap();
    let r=execute(&dir,"out",&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Other.flag,s=@v/s)","q=quotient(Pair.echo,on=$s.domain,b=$v.value)",
        "all=quotient(Pair.all,on=$s.domain,s=@v/s)","ev=evaluate(Pair.all,s=@v/s)"],None);
    let result=result_json(&dir,&r);let answers=arr(get(&result,"answers"));
    assert_eq!(r.code,0,"{} {} {answers:?}",r.stdout,r.stderr);
    assert!(arr(get(get(&answers[2],"scope"),"readings")).iter().any(|x|s(x)=="Other"));
    let producer=s(get(get(get(&answers[1],"outputs"),"value"),"node"));
    let q=get(get(&answers[2],"outputs"),"quotient");
    let classes=get(quotient(&result,2),"classes");
    let projection=node(&result,get(quotient(&result,2),"projection"));
    let target=get(get(projection,"value"),"target");
    for root in [q,classes,target] {
        let scope=get(node(&result,root),"scope");
        assert!(arr(get(scope,"readings")).iter().any(|x|s(x)=="Other"));
        assert!(arr(get(scope,"snapshots")).iter().any(|x|s(x)=="v"));
        let mut pending=vec![root];let mut seen=std::collections::BTreeSet::new();
        while let Some(reference)=pending.pop(){
            if seen.insert(s(get(reference,"node"))) {pending.extend(arr(get(node(&result,reference),"arguments")));}
        }
        assert!(seen.contains(producer));
    }
    let ordinary=arr(get(get(&answers[4],"scope"),"quantifiers"));assert!(!ordinary.is_empty());
    let class_scope=get(node(&result,get(quotient(&result,3),"classes")),"scope");
    for scope in [get(&answers[3],"scope"),class_scope] {
        let quantifiers=arr(get(scope,"quantifiers"));
        for q in ordinary {assert!(quantifiers.iter().any(|actual|
            ["kind","name","type"].iter().all(|key|get(actual,key).value==get(q,key).value)));}
    }
}

#[test]
fn inapplicable_view_binding_preserves_projection_condition_and_followup() {
    let dir=input("quotient-inapplicable");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap()
        .replace("view last", "view no():Option<Bool> = none<Bool>;view echo(b:Bool):Bool=b;view last");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let r=execute(&dir,"out",&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.no)","q=quotient(Pair.echo,on=$s.domain,b=$v.value.some)",
        "later=check(Pair.empty,s=@v/s)"],None);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[2],"status")),"undetermined");assert!(!has(get(&answers[2],"outputs"),"quotient"));
    assert_eq!(s(get(&answers[3],"status")),"refuted");
    for code in ["condition_failed","dependency_blocked"] {
        assert!(arr(get(&answers[2],"reasons")).iter().any(|r|s(get(r,"code"))==code));
    }
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap().replace("none<Bool>","some(true)");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.no)","q=quotient(Pair.echo,on=$s.domain,b=$v.value.some)"];
    let available=execute(&dir,"known",&asks,None);
    assert_eq!(available.code,0,"{} {}",available.stdout,available.stderr);
    let complete=result_json(&dir,&available);
    exact_fibers(&complete,2,vec![vec![(false,false),(false,true),(true,false),(true,true)]]);
    let reused=execute(&dir,"known2",&asks,Some("known"));
    assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
    let repeated=result_json(&dir,&reused);
    for key in ["answers","nodes"] {assert_eq!(get(&complete,key).value,get(&repeated,key).value);}
}

fn law_input(name: &str, extra: &str) -> std::path::PathBuf {
    let dir = input(name);
    let path = dir.join("l.law");
    let mut law = std::fs::read_to_string(&path).unwrap();
    law.pop(); law.push_str(extra); law.push('}');
    std::fs::write(path,law).unwrap(); dir
}
#[test]
fn law_descent_compares_typed_pairs_instead_of_truth_and_reuses() {
    let dir = law_input("quotient-law-pairs", "law optional same(s:State):s.x=s.x;law optional last_eq(s:State):s.y=s.y;");
    let asks = ["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "bad=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.same)",
        "good=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.last_eq)",
        "solutions=quotient(Pair.last,on=$s.solutions,s=@v/s,law=Pair.same)"];
    let r=execute(&dir,"out",&asks,None);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);
    let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[1],"status")),"refuted");
    for index in [2,3] {
        assert_eq!(s(get(&answers[index],"status")),"established");
        let q=quotient(&result,index);
        let map=node(&result,get(q,"descent"));
        assert_eq!(arr(get(get(map,"value"),"pairs")).len(),2);
        for entry in arr(get(get(map,"value"),"pairs")) {
            let entry=arr(entry);
            let class=members(get(node(&result,&entry[0]),"value"));
            let family=arr(get(node(&result,&entry[1]),"value"));assert_eq!(family.len(),1);
            let value=arr(get(&arr(&family[0])[1],"some"));assert_eq!(value.len(),2);
            let expected=if index==2 {class[0].1} else {true};
            for side in value {assert_eq!(side.value,JValue::Bool(expected));}
        }
    }
    let evidence=node(&result,&arr(get(&answers[1],"evidence"))[0]);
    assert_eq!(s(get(get(evidence,"value"),"kind")),"separating_pair");
    let data=get(get(evidence,"value"),"data");
    let points=[pair(get(node(&result,get(data,"first")),"value")),pair(get(node(&result,get(data,"second")),"value"))];
    assert_eq!(points[0].1,points[1].1);assert_ne!(points[0].0,points[1].0);
    let values=arr(get(data,"law_values"));
    assert_ne!(get(node(&result,&values[0]),"value").value,get(node(&result,&values[1]),"value").value);
    for evaluation in arr(get(quotient(&result,1),"evaluations")) {
        let evaluation=get(node(&result,evaluation),"value");
        assert_eq!(get(node(&result,get(evaluation,"value")),"value").value,JValue::Bool(true));
        let environment=get(node(&result,get(evaluation,"environment")),"value");
        assert_eq!(arr(get(environment,"overrides")).len(),2);
    }
    let repeated=execute(&dir,"reused",&asks,Some("out"));
    assert_eq!(repeated.code,1,"{} {}",repeated.stdout,repeated.stderr);
    let reused=result_json(&dir,&repeated);
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&reused,key).value);}
}
#[test]
fn law_descent_preserves_unbound_instance_keys_and_additional_binding() {
    let dir=law_input("quotient-law-quantified","law optional indexed(s:State,b:Bool):s.y=b;view fixed():Bool=false;view yes():Bool=true;");
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.yes)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.indexed)",
        "bound=quotient(Pair.last,on=$s.domain,s=@v/s,b=$v.value,law=Pair.indexed)",
        "bad=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.indexed)"];
    let r=execute(&dir,"out",&asks,None);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[2],"status")),"established");
    assert_eq!(s(get(&answers[3],"status")),"established");
    assert_eq!(s(get(&answers[4],"status")),"refuted");
    assert!(arr(get(get(&answers[2],"scope"),"quantifiers")).iter().any(|q| s(get(q,"name"))=="b"&&s(get(q,"kind"))=="forall"));
    assert_eq!(arr(get(quotient(&result,2),"evaluations")).len(),8);
    assert_eq!(arr(get(quotient(&result,3),"evaluations")).len(),4);
    let map=get(node(&result,get(quotient(&result,2),"descent")),"value");
    for entry in arr(get(map,"pairs")) {
        let family=get(node(&result,&arr(entry)[1]),"value");
        assert_eq!(arr(family).len(),2);
        let keys=arr(family).iter().map(|item| matches!(arr(&arr(item)[0])[1].value,JValue::Bool(true))).collect::<Vec<_>>();
        assert!(keys.contains(&false)&&keys.contains(&true));
    }
}
#[test]
fn law_descent_distinguishes_guard_and_preserves_empty_domain_type() {
    let dir=law_input("quotient-law-guard","law optional guarded(s:State) when s.x:s.y=s.y;");
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "bad=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.guarded)",
        "good=quotient(Pair.last,on=$s.solutions,s=@v/s,law=Pair.guarded)",
        "empty=solve(Pair.empty,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.last,on=$empty.solutions,s=@v/s,law=Pair.guarded)"];
    let r=execute(&dir,"out",&asks,None);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[1],"status")),"refuted");
    assert_eq!(s(get(&answers[2],"status")),"established");
    assert_eq!(s(get(&answers[4],"status")),"established");
    let q=quotient(&result,4);
    assert!(arr(get(q,"evaluations")).is_empty());
    let map=get(node(&result,get(q,"descent")),"value");
    assert!(arr(get(map,"pairs")).is_empty());
    let target=get(node(&result,get(map,"target")),"value");
    assert!(arr(get(target,"elements")).is_empty());
    assert_eq!(s(&arr(get(target,"type"))[0]),"Set");
    let evaluations=arr(get(quotient(&result,1),"evaluations"));
    let inactive=evaluations.iter().map(|r|get(node(&result,r),"value"))
        .filter(|e|s(get(e,"applicability"))=="not_applicable").collect::<Vec<_>>();
    assert_eq!(inactive.len(),2);
    for e in inactive {
        assert!(!has(e,"value"));
        let parts=arr(get(e,"parts"));assert_eq!(parts.len(),2);
        assert!(arr(get(&parts[1],"children")).is_empty());assert!(!has(&parts[1],"value"));
    }
}
#[test]
fn missing_law_values_remain_missing_and_independent_followup_runs() {
    let dir=law_input("quotient-law-missing","law optional both(s:State):s.y=s.y;view fixed(s:State):Bool=false;");
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap().replace("with{x=a,y=b}","with{x=a}");std::fs::write(path,law).unwrap();
    let path=dir.join("a.json");let map=std::fs::read_to_string(&path).unwrap().replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}"#,"");std::fs::write(path,map).unwrap();
    let asks=["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)","q=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.both)","later=check(Pair.valid,s=@v/s)"];
    let r=execute(&dir,"out",&asks,None);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);let answers=arr(get(&result,"answers"));
    assert_eq!(s(get(&answers[1],"status")),"undetermined");
    assert!(!has(get(&answers[1],"outputs"),"quotient"));
    assert_eq!(s(get(&answers[2],"status")),"refuted");
    assert!(format!("{:?}",get(&answers[1],"reasons")).contains("Pair.State.y"));
    let repeated=execute(&dir,"reused",&asks,Some("out"));assert_eq!(repeated.code,2);
    let reused=result_json(&dir,&repeated);assert_eq!(get(&result,"answers").value,get(&reused,"answers").value);
}
#[test]
fn quotient_law_rejects_wrong_kind_and_shared_parameter_type() {
    let dir=law_input("quotient-law-usage","law optional other(s:Bool):s=s;");
    for ask in ["q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.last)","q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.other)","q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.valid,law=Pair.valid)"] {
        let r=execute(&dir,"out",&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",ask],None);
        assert_eq!(r.code,64,"{} {}",r.stdout,r.stderr);
    }
}
#[test]
fn quotient_law_preserves_composite_operand_and_guard_evaluation_children() {
    let dir=law_input("quotient-law-children","law optional composite(s:State) when s.x or s.y:(s.x and s.y)=s.y;");
    let r=execute(&dir,"out",&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)","q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.composite)"],None);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let result=result_json(&dir,&r);
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap();
    let check_children=|children:&[JNode],expected:&[bool]| {
        assert_eq!(children.len(),2);
        for ((child,source),expected) in children.iter().zip(["s.x","s.y"]).zip(expected) {
            let evaluation=get(node(&result,child),"value");
            assert_eq!(get(node(&result,get(evaluation,"value")),"value").value,JValue::Bool(*expected));
            let expression=get(node(&result,get(evaluation,"expression")),"value");
            let span=arr(get(get(expression,"location"),"span"));
            assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize],source);
        }
    };
    for reference in arr(get(quotient(&result,1),"evaluations")) {
        let evaluation=get(node(&result,reference),"value");
        let environment=get(node(&result,get(evaluation,"environment")),"value");
        let mut values=std::collections::BTreeMap::new();
        for row in arr(get(environment,"overrides")) {
            values.insert(s(get(get(row,"slot"),"field")),matches!(get(node(&result,get(row,"value")),"value").value,JValue::Bool(true)));
        }
        let expected=[values["Pair.State.x"],values["Pair.State.y"]];
        let parts=arr(get(evaluation,"parts"));
        let guard=get(node(&result,&arr(get(&parts[0],"children"))[0]),"value");
        check_children(arr(get(&arr(get(guard,"parts"))[0],"children")),&expected);
        if s(get(evaluation,"applicability"))=="applicable" {
            let body=arr(get(&parts[1],"children"));assert_eq!(body.len(),2);
            let group=get(node(&result,&body[0]),"value");
            let and=get(node(&result,&arr(get(&arr(get(group,"parts"))[0],"children"))[0]),"value");
            check_children(arr(get(&arr(get(and,"parts"))[0],"children")),&expected);
            assert_eq!(get(node(&result,get(and,"value")),"value").value,JValue::Bool(expected[0]&&expected[1]));
        }
    }
    let reused=execute(&dir,"reused",&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)","q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.composite)"],Some("out"));
    assert_eq!(reused.code,1,"{} {}",reused.stdout,reused.stderr);
    let reused=result_json(&dir,&reused);
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&reused,key).value);}
}
