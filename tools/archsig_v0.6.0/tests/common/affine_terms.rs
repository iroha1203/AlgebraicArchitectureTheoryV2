mod terms {
    include!("terms.rs");
}
pub fn definitions() -> String {
    terms::DEFINITIONS.replace(r#"{"name":"h","type":"Z","meaning":"h"}"#,r#"{"name":"h","type":"Z","meaning":"h"},{"name":"k","type":"Z","meaning":"k"},{"name":"q","type":"Q","meaning":"q"},{"name":"p","type":"Bool","meaning":"p"}"#)
}
pub const SCRIPT: &str = r#"
view same(s:Sample):Bool=s.f=(fn(a:Z,b:Z)=>a+a-b);
view different(s:Sample):Bool=s.f!=(fn(a:Z,b:Z)=>a+a-b+1);
law required equality(s:Sample):s.f=(fn(a:Z,b:Z)=>a+a-b);
law required unequal(s:Sample):s.f=(fn(a:Z,b:Z)=>a+a-b+1);
view rational():Bool=(fn(q:Q)=>q+rat(1,2)+rat(1,2))=(fn(x:Q)=>x+1);
view tuple():Bool=(fn(t:(Z,Q))=>(t.0+t.0,t.1+rat(1,2)+rat(1,2)))=(fn(u:(Z,Q))=>(2*u.0,u.1+1));
view mixed():Bool=(fn(b:Bool,x:Z)=>if b then x+x else x+1)=(fn(c:Bool,y:Z)=>if not c then 1+y else 2*y);
view coefficient(s:Sample):Bool=s.f!=(fn(a:Z,b:Z)=>2*a-2*b);
view qCoefficient():Bool=(fn(q:Q)=>rat(1,2)*q+1)!=(fn(x:Q)=>rat(2,3)*x+1);
view tupleCoefficient():Bool=(fn(t:(Z,Q))=>t.1+1)!=(fn(u:(Z,Q))=>u.1+u.1+1);
view tupleArithmetic():Bool=(fn(t:(Z,Q))=>-(t+t))=(fn(u:(Z,Q))=>(-2*u.0,-2*u.1));
view aggregation():Bool=(fn(x:Z)=>sum(list<Z>[x,x,1]))=(fn(y:Z)=>2*y+1);
view finiteBody():Bool=(fn(x:Z)=>if forall b:Bool . (x-x=0) or b then x+1 else x+2)=(fn(y:Z)=>y+1);
view cancel(s:Sample):Z=s.f(s.h,s.h+s.h);
view delta(s:Sample):Z=s.f(s.h+1,s.h+s.h);
view cancelEquality(s:Sample):Bool=s.f(s.h,s.h)=s.h;
view independent(s:Sample):Bool=s.f(s.h,s.k)=s.h;
law required universal(s:Sample,z:Z):s.f(z,z)=z;
view explicit(s:Sample):Bool=forall z:Z . s.f(z,z)=z;
view qcancel(s:Sample):Q=(fn(q:Q)=>q-q)(s.q);
view tupleCancel(s:Sample):(Z,Q)=(fn(t:(Z,Q))=>(t.0-t.0,t.1-t.1))((s.h,s.q));
view opaqueText():Bool=(fn(x:Text)=>3)=(fn(y:Text)=>4);
view opaque():Bool=(fn(x:Z)=>x*x)=(fn(y:Z)=>y*y+1);
view opaqueMissing(s:Sample):Z=(fn(x:Z)=>x*x)(s.h);
view concreteNonlinear():Z=(fn(x:Z)=>x*x)(3);
view finiteNonlinear():Bool=(fn(b:Bool)=>if b then 3*3 else 2*2)=(fn(c:Bool)=>if c then 9 else 4);
law required outside(s:Sample,z:Z):(fn(x:Z)=>x*x)(z)=z;
view inner(s:Sample,x:Z):Z=s.f(x,x);
law required viaView(s:Sample,z:Z):inner(s,z)=z;
view letCancel(s:Sample):Z=let a=s.h in s.f(a,a+a);
view choice(s:Sample):Term<(Z)->Z> =if s.p then (fn(x:Z)=>x+1) else (fn(y:Z)=>1+y);
view affineStable(s:Sample):Z=choice(s)(s.h)-s.h;
view partial(s:Sample):Z=(fn(x:Z,y:Z)=>x-x+y)(s.h,1);
view needMissing(s:Sample):Z=s.missing(s.h,s.h);
view seed():Z=1;
law required prior():false;
"#;
pub fn law(digest: &str) -> String {
    format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Terms {{use vocabulary Terms version \"1\" digest \"{digest}\";{SCRIPT}}}"
    )
}
pub fn archmap(digest: &str, revision: &str) -> String {
    terms::archmap(digest, revision)
}
