pub const DEFINITIONS: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Terms","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Terms.Sample","meaning":"Sample","parameters":[],"fields":[{"name":"f","type":["Term",["Z","Z"],"Z"],"meaning":"f"},{"name":"g","type":["Term",["Bool"],"Z"],"meaning":"g"},{"name":"h","type":"Z","meaning":"h"},{"name":"missing","type":["Term",["Z","Z"],"Z"],"meaning":"missing"},{"name":"inspect","type":["Term",[["Data","Terms.Choice"]],"Z"],"meaning":"inspect"},{"name":"make","type":["Term",["Z"],["Data","Terms.Choice"]],"meaning":"make"}],"alignments":[]},{"kind":"data","name":"Terms.Choice","meaning":"Choice","constructors":[{"name":"Left","arguments":["Z"],"meaning":"left"},{"name":"Right","arguments":[],"meaning":"right"}]}]}]}"#;
pub const SCRIPT: &str = r#"
view applied(s:Sample):Z=s.f(7,3);
view constant():Z=(fn()=>3)();
view wrapped(s:Sample):(Term<(Z,Z)->Z>,Option<Term<(Z,Z)->Z>>,List<Term<(Z,Z)->Z>>) = let f=s.f in (f,some(f),list<Term<(Z,Z)->Z>>[f,f]);
view viaTuple(s:Sample):Z=let fs=(s.f,s.f) in fs.0(7,3);
view no():Bool=(fn()=>false)();
law required falseTerm():(fn()=>false)();
view matched(s:Sample):Z=s.inspect(s.make(5));
view zeroConstructor(s:Sample):Z=s.inspect((fn()=>Terms.Choice.Right)());
view finite():Bool=(fn()=>forall b:Bool . b or not b)();
view containers():(Z,Set<Z>,Option<Q>)=(fn(xs:List<Z>)=>(sum(xs),set{y+1 | y in xs where y>0},some(rat(1,2))))(list<Z>[2,2,0]);
view fp():Fp(5) =(fn(x:Fp(5))=>x+x)(3);
view nestedFunction():Z=((fn()=>fn(z:Z)=>z+1)())(4);
view termArgument(s:Sample):Term<(Z,Z)->Z> = (fn(f:Term<(Z,Z)->Z>)=>f)(s.f);
view inline():Q=(fn(x:Q)=>x+rat(1,2))(rat(1,2));
view inspector(s:Sample):Term<(Choice)->Z> = s.inspect;
view quantifier():Term<()->Bool> = fn()=>forall b:Bool . b or not b;
view read(s:Sample):Term<(Z,Z)->Z> =s.f;
view chosen(s:Sample):Z=s.g(false);
view absent(s:Sample):Z=s.missing(7,3);
view unknown(s:Sample):Z=s.f(s.h,3);
view seed():Z=1;
law required prior():false;
"#;
pub fn law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Terms {{ use vocabulary Terms version \"1\" digest \"{digest}\"; {SCRIPT} }}"
    )
}
pub fn archmap(digest: &str, revision: &str) -> String {
    r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Terms","version":"1","digest":"DIGEST"}],"sources":[{"id":"src","uri":"urn:fixture:terms","revision":"REVISION","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}],"origins":[{"id":"base","mode":"specification","method":"closed terms","locations":[{"source":"src","path":"terms.model","span":[0,2]}]}],"snapshots":[{"id":"v","origin":"base","subjects":[{"id":"s","type":"Terms.Sample","origin":"base"}],"atoms":[{"id":"inspect","subject":"s","field":"Terms.Sample.inspect","value":{"params":["c"],"body":"match c {Left(n)=>n+1;Right=>0;}"},"origin":"base"},{"id":"make","subject":"s","field":"Terms.Sample.make","value":{"params":["z"],"body":"Left(z)"},"origin":"base"},{"id":"f","subject":"s","field":"Terms.Sample.f","value":{"params":["x","y"],"body":"let twice=2*x in twice-y"},"origin":"base"},{"id":"g","subject":"s","field":"Terms.Sample.g","value":{"params":["b"],"body":"if b then 4 else 9"},"origin":"base"}]}]}"#.replace("DIGEST",digest).replace("REVISION",revision)
}
