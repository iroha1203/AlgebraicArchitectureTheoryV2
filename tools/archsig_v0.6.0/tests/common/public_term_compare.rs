// 文書から独立した閉じたTermと観測値。
mod primitive {
    include!("terms.rs");
}
use archsig::{definition::check_definitions, observed::input::InputSources};
pub const SCRIPT: &str = r#"
view observed(s:Sample):Term<(Bool)->Z> = s.g;
view finiteSame():Term<(Bool)->Z> = fn(t:Bool)=>if not t then 9 else 4;
view finiteOther():Term<(Bool)->Z> = fn(t:Bool)=>if t then 5 else 9;
view affineSame():Term<(Z,Z)->Z> = fn(a:Z,b:Z)=>a+a-b;
view affineShift():Term<(Z,Z)->Z> = fn(a:Z,b:Z)=>2*a-b+1;
view affineSlope():Term<(Z,Z)->Z> = fn(a:Z,b:Z)=>2*a-2*b;
view rationalLeft():Term<(Q)->Q> = fn(q:Q)=>rat(1,2)*q+rat(1,3);
view rationalSame():Term<(Q)->Q> = fn(x:Q)=>x*rat(2,4)+rat(2,6);
view rationalOther():Term<(Q)->Q> = fn(x:Q)=>rat(2,3)*x+rat(1,3);
view packed(s:Sample):(Term<(Bool)->Z>,List<Term<(Bool)->Z>>,Option<Term<(Bool)->Z>>,FnBox) = (s.g,list<Term<(Bool)->Z>>[s.g,s.g],some(s.g),Wrap(s.g));
view packedSame():(Term<(Bool)->Z>,List<Term<(Bool)->Z>>,Option<Term<(Bool)->Z>>,FnBox) = let f=fn(t:Bool)=>if not t then 9 else 4 in (f,list<Term<(Bool)->Z>>[f,f],some(f),Wrap(f));
view packedOther():(Term<(Bool)->Z>,List<Term<(Bool)->Z>>,Option<Term<(Bool)->Z>>,FnBox) = let f=fn(t:Bool)=>if not t then 9 else 4 in (f,list<Term<(Bool)->Z>>[f,f],some(f),Wrap(fn(t:Bool)=>if t then 5 else 9));
view higherLeft():Term<(Bool)->Term<(Bool)->Z>> = fn(b:Bool)=>if b then (fn(x:Bool)=>if x then 4 else 9) else (fn(x:Bool)=>if x then 4 else 9);
view higherSame():Term<(Bool)->Term<(Bool)->Z>> = fn(c:Bool)=>fn(y:Bool)=>if not y then 9 else 4;
view higherOther():Term<(Bool)->Term<(Bool)->Z>> = fn(c:Bool)=>if c then (fn(y:Bool)=>if y then 5 else 9) else (fn(y:Bool)=>if y then 4 else 9);
view nonlinear():Term<(Z)->Z> = fn(x:Z)=>x*x;
view nonlinearSame():Term<(Z)->Z> = fn(y:Z)=>y*y+0;
view opaqueLeft():(Term<(Z)->Z>,Z) = (fn(x:Z)=>x*x,0);
view opaqueOther():(Term<(Z)->Z>,Z) = (fn(y:Z)=>y*y+0,1);
"#;
pub fn input(extra: &str, missing: bool, revision: &str) -> InputSources {
    let definitions=primitive::DEFINITIONS.replace(r#"{"kind":"data","name":"Terms.Choice""#,r#"{"kind":"data","name":"Terms.FnBox","meaning":"閉じた項の保持","constructors":[{"name":"Wrap","arguments":[["Term",["Bool"],"Z"]],"meaning":"項を保持"},{"name":"Plain","arguments":["Bool"],"meaning":"真偽値"},{"name":"Vacant","arguments":[],"meaning":"空"}]},{"kind":"data","name":"Terms.Flag","meaning":"有限型","constructors":[{"name":"Off","arguments":[],"meaning":"無効"},{"name":"On","arguments":["Bool"],"meaning":"有効"}]},{"kind":"data","name":"Terms.Choice""#);
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Terms"].digest;
    let law = primitive::law(digest).replace(
        primitive::SCRIPT,
        &format!("{}\n{SCRIPT}\n{extra}", primitive::SCRIPT),
    );
    let map = primitive::archmap(digest, revision);
    let map = if missing {
        map.replace(r#",{"id":"g","subject":"s","field":"Terms.Sample.g","value":{"params":["b"],"body":"if b then 4 else 9"},"origin":"base"}"#,"")
    } else {
        map
    };
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
