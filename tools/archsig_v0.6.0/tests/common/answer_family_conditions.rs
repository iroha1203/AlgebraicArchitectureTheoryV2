use archsig as fixture_archsig;
use archsig::observed::input::InputSources;
#[allow(dead_code)]
mod base {
    use super::fixture_archsig as archsig;
    include!("answer_projection_conditions.rs");
}
pub fn input(mode: &str, revision: &str) -> InputSources {
    let i = base::input(mode, revision);
    let law = String::from_utf8(i.law().bytes().to_vec()).unwrap();
    let anchor = "view acRoot(a:Reservations.System):Reservations.System=a;";
    let extra = r#"
view afTruth():Bool=true;
law required afFinite(x:Z,b:Bool):x=2;
law required afNumeric(x:Z,z:Z):x+z=z+x;
law required afRational(x:Q,q:Q):x+q=q+x;
law required afMixed(x:Z,b:Bool,z:Z):if b then x+z=z+x else x+z=z+x;
law required afRef(p:Reservations.State,b:Bool):p=p;
law required afRoot(a:Reservations.System,b:Bool):a=a;
law required afBool(c:Bool,b:Bool):c;
law required afMany(a:Reservations.System,x:Z,y:Z,c:Bool,b:Bool):if c then x+y=x+y else x=y;
"#;
    assert_eq!(law.matches(anchor).count(), 1);
    InputSources::from_bytes(
        i.definitions().iter().map(|d| d.bytes().to_vec()).collect(),
        law.replace(anchor, &(anchor.to_owned() + extra))
            .into_bytes(),
        i.archmap().bytes().to_vec(),
    )
}
