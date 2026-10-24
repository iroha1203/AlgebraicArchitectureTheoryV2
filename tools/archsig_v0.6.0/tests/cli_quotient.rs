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
    let dir=input("quotient-stop");
    for mode in 0..3 {
        let seen=Rc::new(Cell::new(0));let count=seen.clone();
        let mut c=Control::new(Limits{time_ms:Some(1),memory_mib:Some(1)},move|point|{
            if point==Checkpoint::Quotient {count.set(count.get()+1);}
            if count.get()==2 {match mode {
                0=>Usage{elapsed_ms:2,..Usage::default()},1=>Usage{memory_mib:2,..Usage::default()},
                _=>Usage{signal:Some(archsig::result::Signal::Term),..Usage::default()},
            }}else{Usage::default()}
        });
        let sources=InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()],std::fs::read(dir.join("l.law")).unwrap(),std::fs::read(dir.join("a.json")).unwrap());
        let result=evaluate_observed_bytes(sources,&["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)","q=quotient(Pair.last,on=$s.domain,s=@v/s)","later=evaluate(Pair.last,s=@v/s)"],&mut c).unwrap();
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
