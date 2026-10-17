use archsig as fixture_archsig;
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_partial_calls.rs");
}
use archsig::observed::input::InputSources;
pub const SCRIPT: &str = r#"
view ocSome(a:System,x:Option<(State[a],Z)>):Bool=true;
view ocSet(a:System,x:Set<(State[a],Z)>):Bool=true;
view ocNested(a:System,b:System,x:Option<List<Set<((State[a],Z),Option<(State[b],Q)>)>>>):Bool=true;
law required ocSomeGood(a:System,p:State,z:Z):ocSome(a,some((p,z)));
law required ocSetGood(a:System,p:State,q:State,z:Z):ocSet(a,set<(State,Z)>{(p,z),(q,z+1),(p,z)});
law required ocNestedGood(a:System,b:System,p:State,q:State,z:Z,r:Q):ocNested(a,b,some(list<Set<((State,Z),Option<(State,Q)>)>>[set<((State,Z),Option<(State,Q)>)>{((p,z),some((q,r)))}]));
view ocReturn(a:System,p:State,z:Z):Option<(State[a],Z)> =some((p,z));
view ocReturnSet(a:System,p:State,z:Z):Set<(State[a],Z)> =set<(State,Z)>{(p,z),(p,z+1),(p,z)};
view ocIgnore(x:Option<(State,Z)>):Bool=true;
view ocIgnoreSet(x:Set<(State,Z)>):Bool=true;
law required ocReturned(a:System,p:State,z:Z):ocIgnore(ocReturn(a,p,z));
law required ocReturnedSet(a:System,p:State,z:Z):ocIgnoreSet(ocReturnSet(a,p,z));
view ocMissing(a:System,p:State,q:State):Bool=ocSome(a,some((p,q.free)));
view ocMissingSet(a:System,p:State,q:State):Bool=ocSet(a,set<(State,Z)>{(p,q.free),(p,q.free+1),(p,q.free)});
view ocPending(a:System,e:Reserve,p:State):Bool=ocSome(a,some((p,read(a,e.to))));
view ocPendingSet(a:System,e:Reserve,p:State):Bool=ocSet(a,set<(State,Z)>{(p,read(a,e.to)),(p,0)});
view ocMixed(a:System,e:Reserve,p:State,q:State):Bool=ocSet(a,set<(State,Z)>{(e.to,q.free),(p,q.free),(p,q.free)});
view ocMixedReverse(a:System,e:Reserve,p:State,q:State):Bool=ocSet(a,set<(State,Z)>{(p,q.free),(e.to,q.free),(p,q.free)});
view ocPendingReturn(a:System,e:Reserve,p:State):Option<(State[a],Z)> =some((p,read(a,e.to)));
view ocPendingReturnSet(a:System,e:Reserve,p:State):Set<(State[a],Z)> =set<(State,Z)>{(p,read(a,e.to)),(p,0)};
view ocPendingReturnUse(a:System,e:Reserve,p:State):Bool=ocIgnore(ocPendingReturn(a,e,p));
view ocPendingReturnSetUse(a:System,e:Reserve,p:State):Bool=ocIgnoreSet(ocPendingReturnSet(a,e,p));
view ocStopAccept(a:System,x:Option<Set<(State[a],Z)>>):Bool=true;
view ocStop(a:System,p:State,q:State):Bool=ocStopAccept(a,some(set<(State,Z)>{(p,q.free),(p,q.free+1),(p,q.free)}));
view ocEmptyValues(a:System):(Option<(State[a],Z)>,Set<(State[a],Z)>,Z)=(none<(State,Z)>,set<(State,Z)>{},0);
view ocEmptyValuesUse(a:System):(Option<(State,Z)>,Set<(State,Z)>,Z)=ocEmptyValues(a);
view ocUnknown(a:System,e:Reserve,q:State):Bool=ocSome(a,some((e.to,q.free)));
view ocEmpty(a:System):Bool=ocSome(a,none<(State,Z)>) and ocSet(a,set<(State,Z)>{});
view ocCount(a:System,p:State,q:State):Z=count(set<(State,Z)>{(p,q.free),(p,p.free),(p,q.free)});
view ocKnownSet(a:System,p:State):Bool=set<(State,Z)>{(p,0),(p,1),(p,0)}=set<(State,Z)>{(p,1),(p,0)};
"#;
pub fn input(unknown: bool, revision: &str) -> InputSources {
    extend(base::input(unknown, revision))
}
pub fn missing_reference_input() -> InputSources {
    extend(base::missing_reference_input())
}
fn extend(input: InputSources) -> InputSources {
    let law = String::from_utf8(input.law().bytes().to_vec())
        .unwrap()
        .replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT));
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        input.archmap().bytes().to_vec(),
    )
}
