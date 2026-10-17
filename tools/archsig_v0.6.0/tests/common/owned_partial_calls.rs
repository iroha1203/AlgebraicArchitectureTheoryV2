use archsig as fixture_archsig;
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_compound_calls.rs");
}
use archsig::observed::input::InputSources;
pub const SCRIPT: &str = r#"
view pcAccept(a:System,x:(State[a],Z)):Bool=true;
view pcReturn(a:System,p:State,z:Z):(State[a],Z)=(p,z);
view pcQ(a:System,x:(State[a],Q)):Q=x.1+rat(1,2)+rat(1,2);
law required pcQAffine(a:System,p:State,q:Q):pcQ(a,(p,q))=q+1;
view pcPick(a:System,x:(State[a],Z)):Z=x.1;
view pcList(a:System,x:List<(State[a],Z)>):Bool=true;
view pcListReturn(a:System,p:State,z:Z):List<(State[a],Z)> =list<(State,Z)>[(p,z),(p,z+1)];
view pcIgnoreList(xs:List<(State,Z)>):Bool=true;
law required pcReturnedList(a:System,p:State,z:Z):pcIgnoreList(pcListReturn(a,p,z));
view pcNested(a:System,b:System,x:((State[a],Z),(State[b],Q))):Bool=true;
law required pcGood(a:System,p:State,z:Z):pcAccept(a,(p,z));
law required pcReturned(a:System,p:State,z:Z):pcReturn(a,p,z).1=z;
law required pcAffine(a:System,p:State,z:Z):pcPick(a,(p,z))=z;
law required pcListGood(a:System,p:State,q:State,z:Z):pcList(a,list<(State,Z)>[(p,z),(q,z+1),(p,z)]);
law required pcNestedGood(a:System,b:System,p:State,q:State,z:Z,r:Q):pcNested(a,b,((p,z),(q,r)));
view pcMissing(a:System,p:State,q:State):Bool=pcList(a,list<(State,Z)>[(p,q.free),(p,q.free+1),(p,q.free)]);
view pcMissingAffine(a:System,p:State,q:State):Z=pcPick(a,(p,q.free))-q.free;
view pcIgnoreNumeric(z:Z):Z=0;
view pcPendingPlain(a:System,e:Reserve,p:State):Bool=pcAccept(a,(p,pcIgnoreNumeric(read(a,e.to))));
view pcPendingLet(a:System,e:Reserve):Bool=let n=read(a,e.to) in true;
view pcPendingIf(a:System,e:Reserve):Bool=if accept(a,e.to) then true else true;
view pcPendingProjection(a:System,e:Reserve):Z=(read(a,e.to),0).1;
view pcPendingField(a:System,e:Reserve):Z=(narrow(a,e.to)).free;
view pcPendingBool(a:System,e:Reserve):Bool=ignoreBool(accept(a,e.to) or true);
view pcPendingQuant(a:System,e:Reserve):Bool=forall b:Bool.ignoreBool(accept(a,e.to));
view pcSkipIf(a:System,e:Reserve):Bool=if false then accept(a,e.to) else true;
view pcSkipOr(a:System,e:Reserve):Bool=true or accept(a,e.to);
law required pcPendingAffine(a:System,e:Reserve,z:Z):ignoreZ(narrow(a,e.to),z)=z;
law required pcPendingUniversal(a:System,e:Reserve,p:State,z:Z):pcAccept(a,(p,ignoreZ(narrow(a,e.to),z)));
view pcUnknownNumeric(a:System,e:Reserve,p:State):Bool=pcAccept(a,(p,read(a,e.to)));
view pcPair(a:System,x:(State[a],State[a],Z)):Bool=true;
view pcMixed(a:System,e:Reserve,p:State,q:State):Bool=pcPair(a,(e.to,p,q.free));
view pcMixedReverse(a:System,e:Reserve,p:State,q:State):Bool=pcPair(a,(p,e.to,q.free));
view pcUnknown(a:System,e:Reserve,q:State):Bool=pcAccept(a,(e.to,q.free));
view pcDiscard(x:Bool):Bool=true;
law required pcIgnored(a:System,p:State,z:Z):pcDiscard(pcAccept(a,(p,z)));
"#;
pub fn missing_reference_input() -> InputSources {
    extend(base::missing_member_input())
}
pub fn input(unknown: bool, revision: &str) -> InputSources {
    extend(base::input(unknown, revision))
}
fn extend(input: InputSources) -> InputSources {
    let law = String::from_utf8(input.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
        .into_bytes();
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law,
        input.archmap().bytes().to_vec(),
    )
}
