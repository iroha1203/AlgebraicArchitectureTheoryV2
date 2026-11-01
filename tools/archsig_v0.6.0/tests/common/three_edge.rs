//! 三点の座標と三辺の変位だけを入力し、行列・解・診断値は供給しない。
use archsig::{definition, input::InputSources};
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Coordinates","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Coordinates.System","meaning":"点と辺の所属先。","parameters":[],"fields":[],"alignments":[]},{"kind":"entity","name":"Coordinates.Point","meaning":"整数座標を持つ点。","parameters":[{"name":"owner","type":["Ref","Coordinates.System"],"meaning":"点の所属先。"}],"fields":[{"name":"coordinate","type":"Z","meaning":"点の座標。"}],"alignments":[]},{"kind":"arrow","name":"Coordinates.Shift","meaning":"二点間の指定変位。","parameters":[{"name":"owner","type":["Ref","Coordinates.System"],"meaning":"辺の所属先。"},{"name":"from","type":["Owned","Coordinates.Point","owner"],"meaning":"始点。"},{"name":"to","type":["Owned","Coordinates.Point","owner"],"meaning":"終点。"}],"fields":[{"name":"shift","type":"Z","meaning":"指定された変位。"}],"alignments":[]}]}]}"#;
pub fn input(gamma: Option<i64>) -> InputSources {
    let definitions = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies()["Coordinates"].digest;
    let mut subjects =
        vec![r#"{"id":"root","type":"Coordinates.System","origin":"model"}"#.to_owned()];
    let mut atoms = vec![];
    let mut atom = |subject: &str, field: &str, value: String| {
        atoms.push(format!(r#"{{"id":"{subject}-{field}","subject":"{subject}","field":"Coordinates.{field}","value":{value},"origin":"model"}}"#))
    };
    for p in ["p", "q", "r"] {
        subjects.push(format!(
            r#"{{"id":"{p}","type":"Coordinates.Point","origin":"model"}}"#
        ));
        atom(p, "Point.owner", r#"["triangle","root"]"#.into());
        atom(p, "Point.coordinate", r#""0""#.into());
    }
    for (edge, from, to, shift) in [
        ("a", "p", "q", Some(1)),
        ("b", "q", "r", Some(1)),
        ("c", "p", "r", gamma),
    ] {
        subjects.push(format!(
            r#"{{"id":"{edge}","type":"Coordinates.Shift","origin":"model"}}"#
        ));
        atom(edge, "Shift.owner", r#"["triangle","root"]"#.into());
        atom(edge, "Shift.from", format!(r#"["triangle","{from}"]"#));
        atom(edge, "Shift.to", format!(r#"["triangle","{to}"]"#));
        if let Some(shift) = shift {
            atom(edge, "Shift.shift", format!(r#""{shift}""#));
        }
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Coordinates","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"三辺の独立試験。","locations":[],"note":"座標と変位の原始値。"}}],"snapshots":[{{"id":"triangle","origin":"model","subjects":[{}],"atoms":[{}]}}]}}"#,
        subjects.join(","),
        atoms.join(",")
    );
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Coordinates {{ use vocabulary Coordinates version \"1\" digest \"{digest}\"; law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift; local Edge(e:Shift) reads e.shift,e.from.coordinate,e.to.coordinate; change move(p:Point,d:Z)=p with {{coordinate=p.coordinate+d}}; }}"
    );
    InputSources::from_bytes(
        vec![D.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
