use super::*;
use archsig_common::{control::quiet, names::QualifiedName};
use archsig_input::input::{CheckedInputs, InputSources, check_inputs};

fn inputs() -> CheckedInputs {
    let definition = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"RowBudget","version":"1","dependencies":[],"declarations":[
{"kind":"entity","name":"RowBudget.Row","meaning":"試験の参照型。","parameters":[],"fields":[],"alignments":[]},
{"kind":"data","name":"RowBudget.Pack","meaning":"長い有限constructor。","constructors":[{"name":"Only","meaning":"単位prefixと二分岐。","arguments":["Unit","Unit","Unit","Unit","Unit","Unit","Unit","Unit","Unit","Unit","Bool","Bool"]}]}
]}]}"#;
    let definitions =
        archsig_input::definition::check_definitions(&[("definition0", definition.as_bytes())])
            .unwrap();
    let digest = &definitions.vocabularies()["RowBudget"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary RowBudget version \"1\" digest \"{digest}\";view flag(c:Row):Bool=true;}}"
    );
    let map = r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"RowBudget","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"有限積の独立入力。","locations":[],"note":"少点の長行。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"row","type":"RowBudget.Row","origin":"model"}],"atoms":[]}]}"#;
    check_inputs(
        InputSources::from_bytes(
            vec![definition.as_bytes().to_vec()],
            law.into_bytes(),
            map.replace("@DIGEST@", digest).into_bytes(),
        ),
        &quiet(),
    )
    .unwrap()
}

fn expected_rows() -> Vec<Vec<Scalar>> {
    vec![
        vec![
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Bool(false),
            Scalar::Bool(false),
        ],
        vec![
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Bool(false),
            Scalar::Bool(true),
        ],
        vec![
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Bool(true),
            Scalar::Bool(false),
        ],
        vec![
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Unit,
            Scalar::Bool(true),
            Scalar::Bool(true),
        ],
    ]
}

#[test]
fn tuple_product_preserves_all_values_and_single_reservation_capacity() {
    let inputs = inputs();
    let types = vec![
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Unit,
        Type::Bool,
        Type::Bool,
    ];
    // values経由はallow_degenerate=falseの逐次productを通る。
    let result = values(
        &Type::Tuple(types.clone()),
        inputs.law(),
        &quiet(),
        &mut |_| unreachable!("参照候補はない"),
        &mut |_| {},
    )
    .unwrap();
    let expected = expected_rows()
        .into_iter()
        .map(Scalar::Tuple)
        .collect::<Vec<_>>();
    assert_eq!(result.values, expected);
    // 公開値契約とは別の内部資源予算。同型の単一予約を参照する。
    let budget = Vec::<Scalar>::with_capacity(12).capacity();
    for value in &result.values {
        assert_eq!(value.ty(), Type::Tuple(types.clone()));
        let Scalar::Tuple(row) = value else {
            panic!("Tuple")
        };
        assert_eq!(row.capacity(), budget);
    }
}

#[test]
fn data_product_preserves_constructor_values_and_single_reservation_capacity() {
    let inputs = inputs();
    let ty = Type::Data("RowBudget.Pack".into());
    // if_finite経由はallow_degenerate=trueの事前domain検査productを通る。
    let result = field_candidates_if_finite(&ty, inputs.law(), &quiet(), &mut |_| {
        unreachable!("参照候補はない")
    })
    .unwrap()
    .unwrap();
    let expected = expected_rows()
        .into_iter()
        .map(|args| Scalar::Data {
            family: "RowBudget.Pack".into(),
            constructor: QualifiedName::parse("RowBudget.Pack.Only".into()),
            args,
        })
        .collect::<Vec<_>>();
    assert!(result.missing.is_empty());
    assert_eq!(result.enumeration.values, expected);
    let budget = Vec::<Scalar>::with_capacity(12).capacity();
    for value in &result.enumeration.values {
        assert_eq!(value.ty(), ty);
        let Scalar::Data { args, .. } = value else {
            panic!("Data")
        };
        assert_eq!(args.capacity(), budget);
    }
}

fn pair(key: u8) -> (Scalar, Scalar) {
    (
        Scalar::Fp {
            modulus: "3".into(),
            value: key.into(),
        },
        Scalar::Unit,
    )
}
#[test]
fn map_candidates_preserve_total_and_partial_order_and_pair_capacity() {
    let inputs = inputs();
    let ty = Type::Map(Box::new(Type::Fp("3".into())), Box::new(Type::Unit));
    let total = values(
        &ty,
        inputs.law(),
        &quiet(),
        &mut |_| unreachable!("参照候補はない"),
        &mut |_| {},
    )
    .unwrap();
    assert_eq!(total.values.len(), 1);
    let Scalar::Map { pairs, .. } = &total.values[0] else {
        panic!("Map")
    };
    assert_eq!(pairs, &vec![pair(0), pair(1), pair(2)]);
    let partial = field_candidates(
        &ty,
        inputs.law(),
        &quiet(),
        &mut |_| unreachable!("参照候補はない"),
        &mut |_, _| unreachable!("Owned候補はない"),
        &mut |_| {},
    )
    .unwrap();
    let expected = vec![
        vec![],
        vec![pair(2)],
        vec![pair(1)],
        vec![pair(1), pair(2)],
        vec![pair(0)],
        vec![pair(0), pair(2)],
        vec![pair(0), pair(1)],
        vec![pair(0), pair(1), pair(2)],
    ];
    assert_eq!(partial.values.len(), expected.len());
    // Scalar::Mapの意味上のEqはpair順を無視するため、各pair列を直接照合する。
    for (value, expected) in partial.values.iter().zip(&expected) {
        let Scalar::Map { pairs, .. } = value else {
            panic!("Map")
        };
        assert_eq!(pairs, expected);
    }
    for value in total.values.iter().chain(&partial.values) {
        assert_eq!(value.ty(), ty);
        let Scalar::Map { pairs, .. } = value else {
            panic!("Map")
        };
        let budget = Vec::<(Scalar, Scalar)>::with_capacity(pairs.len()).capacity();
        assert_eq!(pairs.capacity(), budget);
    }
}
