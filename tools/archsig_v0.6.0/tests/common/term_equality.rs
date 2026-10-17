mod source_terms {
    include!("terms.rs");
}
pub fn definitions() -> String {
    source_terms::DEFINITIONS.replace(r#"{"name":"h","type":"Z","meaning":"h"}"#,r#"{"name":"p","type":"Bool","meaning":"p"}"#).replace(r#"{"kind":"data","name":"Terms.Choice""#,r#"{"kind":"data","name":"Terms.Flag","meaning":"flag","constructors":[{"name":"Off","arguments":[],"meaning":"off"},{"name":"On","arguments":["Bool"],"meaning":"on"}]},{"kind":"data","name":"Terms.Box","meaning":"box","constructors":[{"name":"Wrap","arguments":[["Term",["Bool"],"Z"]],"meaning":"wrap"}]},{"kind":"data","name":"Terms.Choice""#)
}
pub const SCRIPT: &str = r#"
view eq(s:Sample):Bool=s.g=(fn(t:Bool)=>if not t then 9 else 4);
view ne(s:Sample):Bool=s.g!=(fn(t:Bool)=>if t then 5 else 9);
law required same(s:Sample):s.g=(fn(t:Bool)=>if not t then 9 else 4);
law required different(s:Sample):s.g=(fn(t:Bool)=>if t then 5 else 9);
view selfEq(s:Sample):Bool=s.g=s.g;
view zero():Bool=(fn()=>3)=(fn()=>1+2);
view one():Bool=(fn(u:Unit)=>rat(1,2))=(fn(v:Unit)=>rat(2,4));
view fp():Bool=(fn(x:Fp(3))=>x+x)=(fn(y:Fp(3))=>2*y);
view finiteData():Bool=(fn(x:Flag)=>match x {Off=>0;On(b)=>if b then 1 else 2;})=(fn(y:Flag)=>match y {Off=>1-1;On(c)=>if not c then 2 else 1;});
view tuple():Bool=(fn(t:(Bool,Option<Unit>,Set<Unit>))=>(if t.0 then 1 else 0)+(if t.1=some(unit) then 2 else 0)+count(t.2))=(fn(u:(Bool,Option<Unit>,Set<Unit>))=>count(u.2)+(if u.1=some(unit) then 2 else 0)+(if u.0 then 1 else 0));
view multi():Bool=(fn(b:Bool,o:Option<Unit>,s:Set<Unit>)=>(if b then 1 else 0)+(if o=some(unit) then 2 else 0)+count(s))=(fn(x:Bool,y:Option<Unit>,z:Set<Unit>)=>count(z)+(if y=some(unit) then 2 else 0)+(if x then 1 else 0));
view packed(s:Sample):Bool=(s.g,list<Term<(Bool)->Z>>[s.g,s.g],some(s.g),Box.Wrap(s.g))=((fn(t:Bool)=>if not t then 9 else 4),list<Term<(Bool)->Z>>[(fn(t:Bool)=>if not t then 9 else 4),s.g],some(fn(t:Bool)=>if not t then 9 else 4),Box.Wrap(fn(t:Bool)=>if not t then 9 else 4));
view member(s:Sample):Bool=(fn(t:Bool)=>if not t then 9 else 4) in list<Term<(Bool)->Z>>[(fn(t:Bool)=>if t then 5 else 9),s.g];
view arg(s:Sample):Bool=(fn(f:Term<(Bool)->Z>)=>f=(fn(t:Bool)=>if not t then 9 else 4))(s.g);
view higher():Bool=(fn(b:Bool)=>if b then (fn(x:Bool)=>if x then 4 else 9) else (fn(x:Bool)=>if x then 4 else 9))=(fn(c:Bool)=>fn(y:Bool)=>if not y then 9 else 4);
view choose(s:Sample):Term<(Bool)->Z> = if s.p then (fn(t:Bool)=>if not t then 9 else 4) else (fn(t:Bool)=>if t then 5 else 9);
view stable(s:Sample):Term<(Bool)->Z> = if s.p then choose(s) else s.g;
view unstable(s:Sample):Term<(Bool)->Z> = if s.p then choose(s) else (fn(t:Bool)=>if t then 7 else 9);
view branch(s:Sample):Term<(Bool)->Z> = if s.p then s.g else (fn(t:Bool)=>if not t then 9 else 4);
view unresolved(s:Sample):Term<(Z,Z)->Z> = if s.p then s.f else (fn(a:Z,b:Z)=>a+a-b);
view seed():Z=1;
law required prior():false;
view andSkip():Bool=(fn(b:Bool)=>b and ((fn()=>0)=(fn()=>0)))(false);
view orSkip():Bool=(fn(b:Bool)=>b or ((fn()=>0)=(fn()=>0)))(true);
view impliesSkip():Bool=(fn(b:Bool)=>b implies ((fn()=>0)=(fn()=>0)))(false);
view allSkip():Bool=(fn()=>forall b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else false)();
view anySkip():Bool=(fn()=>exists b in list<Bool>[true,false] . if b then true else ((fn()=>0)=(fn()=>0)))();
view andNeeded():Bool=(fn(b:Bool)=>b and ((fn()=>0)=(fn()=>0)))(true);
view allNeeded():Bool=(fn()=>forall b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else true)();
view anyNeeded():Bool=(fn()=>exists b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else false)();
"#;
pub fn law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Terms {{ use vocabulary Terms version \"1\" digest \"{digest}\"; {SCRIPT} }}"
    )
}
pub fn archmap(digest: &str, revision: &str) -> String {
    source_terms::archmap(digest, revision)
}
