use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("answer_dependencies.rs");
}
pub const SCRIPT: &str = r#"
view apMap(f:Map<Reservations.State,Reservations.State>,p:Reservations.State):Reservations.State=f(p);
view apTerm(f:Term<(Z)->Z>):Z=f(2);
view apNested():List<Option<(Z,List<Z>)>> =list<Option<(Z,List<Z>)>>[some((2,list<Z>[3,4]))];
view apMissing(p:Reservations.State):List<Z> =list<Z>[p.free];
view apNone():Option<Z> =none<Z>;
view apEmpty():List<Z> =list<Z>[];
view apUnsupported():(Bool,Unit)=(adOpaque(),unit);
view apQ(x:Q):Q=x;
view apFp(x:Fp(5)):Fp(5)=x;
view apText(x:Text):Text=x;
view apUnit(x:Unit):Unit=x;
view apList(x:List<Z>):List<Z> =x;
view apSet(x:Set<Z>):Set<Z> =x;
view apOption(x:Option<Z>):Option<Z> =x;
"#;
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::input(mode, revision);
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    assert_eq!(law.matches(base::SCRIPT).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(base::SCRIPT, &(base::SCRIPT.to_owned() + SCRIPT))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
#[allow(dead_code)]
mod tree {
    include!("recursive_tree.rs");
}
pub fn tree_input(missing: bool, revision: &str) -> InputSources {
    let d =
        archsig::definition::check_definitions(&[("definition0", tree::DEFINITIONS.as_bytes())])
            .unwrap();
    let digest = &d.vocabularies["Trees"].digest;
    InputSources::from_bytes(vec![tree::DEFINITIONS.as_bytes().to_vec()],tree::law(digest,"view acceptsPair(t:Tree,x:Z):Z=x;view integer(x:Z):Z=x+1;view leaf():Tree=Leaf(2);view empty():Tree=Empty;law required two(x:Z):forall z:Z.x+z=z+x;").into_bytes(),tree::archmap(digest,missing,revision).into_bytes())
}
