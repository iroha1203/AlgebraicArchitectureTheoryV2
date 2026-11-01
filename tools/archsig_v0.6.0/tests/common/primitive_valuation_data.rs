
use archsig_common::{control::Control};
use archsig_input::{input::{CheckedInputs, InputSources, check_inputs}};
use std::sync::Arc;
mod base {
    include!("object_view_compatibility_data.rs");
}
pub const BODY: &str = "view complex(c:Part):Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>let x=if n=0 then Token.Left(n+1) else Token.Right(n) in match x{Left(k)=>k;Right(k)=>k;};view programs(c:Part):List<Term<(Fp(2))->Fp(2)>> =c.programs;view literal(c:Part):Term<(Fp(2))->Fp(2)> =fn(n:Fp(2))=>n+1;view packet(c:Part):Packet=c.packet;view sequence(c:Part):List<Bool> =c.sequence;view empty(c:Part):List<Vacant> =c.empty;view text(c:Part):Text=c.text;view bundle(c:Part):(List<Bool>,Option<Text>) =c.bundle;view program(c:Part):Term<(Fp(2))->Fp(2)> =c.program;view applied(c:Part):Fp(2)=c.program(0);view plus(n:Fp(2)):Fp(2)=n+1; view value(c:Part):Fp(2)=let n=plus(c.quantity) in n+c.quantity;view selected(c:Part):Fp(2)=if c.flag then c.quantity else c.other;view through(c:Part):Fp(2)=c.link.quantity;view pair(c:Part):Fp(2)=c.pair.0;view choice(c:Part):Fp(2)=match c.choice{Left(n)=>n;Right(n)=>n+1;};law required guarded(c:Part) when c.flag:c.quantity=0;view missing(c:Part):Fp(3)=c.third;view ratio(c:Part):Q=c.ratio;view integer(c:Part):Z=c.integer;view family(r:Root):Set<Part> =Part[r];view accept(r:Root,x:Part[r]):Bool=true;view narrow(r:Root,x:Part):Part[r]=x;view argument(c:Part,r:Root):Bool=accept(r,c);view returned(c:Part,r:Root):Part=narrow(r,c);";
pub const MAP: &str = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pattern","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"内部代入の独立入力。","locations":[],"note":"内部候補試験。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"root","type":"Pattern.Root","origin":"model"},{"id":"r2","type":"Pattern.Root","origin":"model"},{"id":"p","type":"Pattern.Part","origin":"model"},{"id":"q","type":"Pattern.Part","origin":"model"}],"atoms":[{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"xp","subject":"p","field":"Pattern.Part.quantity","value":"0","origin":"model"},{"id":"xq","subject":"q","field":"Pattern.Part.quantity","value":"1","origin":"model"},{"id":"yp","subject":"p","field":"Pattern.Part.other","value":"1","origin":"model"},{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"model"},{"id":"lp","subject":"p","field":"Pattern.Part.link","value":["v","p"],"origin":"model"},{"id":"pp","subject":"p","field":"Pattern.Part.pair","value":["0",true],"origin":"model"},{"id":"cp","subject":"p","field":"Pattern.Part.choice","value":{"tag":"Left","args":["0"]},"origin":"model"}]}]}"#;
pub fn inputs() -> Arc<CheckedInputs> {
    with_map(MAP)
}
pub fn with_map(map: &str) -> Arc<CheckedInputs> {
    with_body(map, BODY)
}
pub fn with_body(map: &str, body: &str) -> Arc<CheckedInputs> {
    let fields = r#"{"name":"programs","type":["List",["Term",[["Fp","2"]],["Fp","2"]]],"meaning":"閉じた関数の列。"},{"name":"packet","type":["Data","Pattern.Packet"],"meaning":"入れ子constructor。"},{"name":"sequence","type":["List","Bool"],"meaning":"順序列。"},{"name":"empty","type":["List",["Ref","Pattern.Vacant"]],"meaning":"唯一の空列。"},{"name":"text","type":"Text","meaning":"文字列。"},{"name":"bundle","type":["Tuple",["List","Bool"],["Option","Text"]],"meaning":"入れ子値。"},{"name":"program","type":["Term",[["Fp","2"]],["Fp","2"]],"meaning":"閉じた関数。"},{"name":"quantity","type":["Fp","2"],"meaning":"値。"},{"name":"other","type":["Fp","2"],"meaning":"別値。"},{"name":"third","type":["Fp","3"],"meaning":"欠測値。"},{"name":"ratio","type":"Q","meaning":"有理値。"},{"name":"integer","type":"Z","meaning":"整数値。"},{"name":"table","type":["Map",["Ref","Pattern.Part"],["Ref","Pattern.Part"]],"meaning":"全域表。"},{"name":"nested","type":["Tuple","Unit",["Map",["Ref","Pattern.Part"],["Ref","Pattern.Part"]]],"meaning":"入れ子表。"},{"name":"ownedtable","type":["Map",["Owned","Pattern.Part","owner"],["Owned","Pattern.Part","owner"]],"meaning":"所属表。"},{"name":"emptytable","type":["Map",["Ref","Pattern.Vacant"],["Ref","Pattern.Part"]],"meaning":"空の始域。"},{"name":"flag","type":"Bool","meaning":"条件。"},{"name":"link","type":["Ref","Pattern.Part"],"meaning":"参照。"},{"name":"pair","type":["Tuple",["Fp","2"],"Bool"],"meaning":"積。"},{"name":"choice","type":["Data","Pattern.Token"],"meaning":"選択。"}"#;
    let d=base::D.replacen(r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,fields,1).replace(r#"{"kind":"entity","name":"Pattern.Root""#,r#"{"kind":"data","name":"Pattern.Packet","meaning":"入れ子値。","constructors":[{"name":"Wrap","meaning":"包む。","arguments":[["List","Bool"],"Text"]}]},{"kind":"data","name":"Pattern.Token","meaning":"有限選択。","constructors":[{"name":"Left","meaning":"左。","arguments":[["Fp","2"]]},{"name":"Right","meaning":"右。","arguments":[["Fp","2"]]}]},{"kind":"entity","name":"Pattern.Root""#);
    let defs = archsig_input::definition::check_definitions(&[("definition0", d.as_bytes())]).unwrap();
    let digest = &defs.vocabularies()["Pattern"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";{body}}}"
    );
    Arc::new(
        check_inputs(
            InputSources::from_bytes(
                vec![d.into_bytes()],
                law.into_bytes(),
                map.replace("@DIGEST@", digest).into_bytes(),
            ),
            &Control::unlimited(),
        )
        .unwrap(),
    )
}
