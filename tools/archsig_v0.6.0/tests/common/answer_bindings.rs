use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("owned_map_calls.rs");
}
pub const PACK: &str = "(Z,Q,Fp(5),Bool,Text,Unit,List<Z>,Set<Z>,Option<Z>,Reservations.State,Map<Reservations.State,Reservations.State>,Term<(Z)->Z>)";
pub const SCRIPT: &str = r#"
view abSeed():Z=2;
view abDouble(x:Z):Z=x+x;
view abIdentity(x:Z):Z=x;
law required abFour(x:Z):x=4;
law required abUniversal(x:Z):forall z:Z.x+z=z+x;
view abPack(p:Reservations.State,m:Reservations.Migration):VALUE_TUPLE=(2,rat(1,2),4,false,"answer",unit,list<Z>[2,1,2],set<Z>{2,1,2},some(0),p,m.states,fn(z:Z)=>z+1);
view abCopy(x:VALUE_TUPLE):VALUE_TUPLE=x;
view abUse(x:VALUE_TUPLE):(Z,Q,Fp(5),Bool,Reservations.State,Reservations.State,Z)=(x.0+1,x.1+rat(1,2),x.2+2,not x.3,x.9,x.10(x.9),x.11(2));
view abReference(p:Reservations.State):Reservations.State=p;
view abFree(p:Reservations.State):Z=p.free;
view abFalse():Bool=false;
law required abPrior():false;
view abKeep(x:Z,p:Reservations.State):Z=x+(p.free-p.free);
view abBool(x:Bool):Bool=x;
law required abRequire(x:Bool):x;

"#;
pub fn input(revision: &str) -> InputSources {
    input_mode("known", revision)
}
pub fn input_mode(mode: &str, revision: &str) -> InputSources {
    let input = base::input(mode, revision);
    let law = String::from_utf8(input.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.replace(
            base::SCRIPT,
            &(base::SCRIPT.to_owned() + &SCRIPT.replace("VALUE_TUPLE", PACK)),
        )
        .into_bytes(),
        input.archmap().bytes().to_vec(),
    )
}
#[allow(dead_code)]
mod tree {
    include!("recursive_tree.rs");
}
pub fn tree_input(revision: &str) -> InputSources {
    let checked =
        archsig::definition::check_definitions(&[("definition0", tree::DEFINITIONS.as_bytes())])
            .unwrap();
    let digest = &checked.vocabularies["Trees"].digest;
    InputSources::from_bytes(
        vec![tree::DEFINITIONS.as_bytes().to_vec()],
        tree::law(digest, "").into_bytes(),
        tree::archmap(digest, false, revision).into_bytes(),
    )
}
