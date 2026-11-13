use super::*;
use archsig_input::{
    input::{InputSources, check_inputs},
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn fixture() -> (archsig_input::input::CheckedInputs, String) {
    let definitions = include_str!("../../../../../tests/fixtures/counter.atoms.json")
        .replace("\"type\": \"Z\"", "\"type\": [\"List\", \"Z\"]")
        .replace(
            "\"declarations\": [",
            r#""declarations": [
            {"kind":"data","name":"Counter.Flag","meaning":"印",
             "constructors":[{"name":"On","arguments":[],"meaning":"有"}]},"#,
        );
    let checked =
        archsig_input::definition::check_definitions(&[("counter", definitions.as_bytes())])
            .unwrap();
    let digest = &checked.vocabularies()["Counter"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading CountCheck {{
 use vocabulary Counter version "1" digest "{digest}";
 view all(s: State): Bool = forall x in s.count . x = x;
 view keep_token(token: Z): Z = token;
 view flag(): Flag = Counter.Flag.On;
}}"#
    );
    let map = include_str!("../../../../../tests/fixtures/counter.archmap.json")
        .replace(
            "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11",
            digest,
        )
        .replace("\"value\": \"2\"", "\"value\": [\"2\", \"3\"]");
    let inputs = check_inputs(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.as_bytes().to_vec(),
            map.into_bytes(),
        ),
        &Control::unlimited(),
    )
    .unwrap_or_else(|failure| panic!("name token fixture issues: {:?}", failure.issues()));
    (inputs, law)
}

// Previous arena scan is an independent oracle, including canonical selection
// and constructors (which have no lexical binding).
fn arena_name(inputs: &archsig_input::input::CheckedInputs, span: (usize, usize)) -> Option<&str> {
    let law = inputs.law();
    let mut name = None;
    for (id, expr) in law.exprs().iter().enumerate() {
        if law.expr_type(id).is_some()
            && law.program().expressions.get(&expr.span) == Some(&id)
            && let ExprKind::Dotted(parts) = &expr.kind
            && let Some(first) = parts.first()
            && first.span == span
        {
            assert!(name.is_none_or(|previous| previous == first.name.as_str()));
            name = Some(first.name.as_str());
        }
    }
    name
}

#[test]
fn indexed_name_tokens_match_arena_for_all_spans_and_short_constructor_candidates() {
    let (inputs, source) = fixture();
    let control = Control::unlimited();
    let env = Environment::new(&inputs, &control).unwrap();
    for start in 0..=source.len() {
        for end in start..=source.len() {
            assert_eq!(
                env.find_name_token((start, end)).unwrap(),
                arena_name(&inputs, (start, end)),
                "{start}..{end}"
            );
        }
    }
    let start = source.find("s.count").unwrap();
    assert!(
        inputs.law().program().dotted_candidates[&(start, start + 1)].len() > 1,
        "parser short candidates are also indexed"
    );
    assert_eq!(env.find_name_token((start, start + 1)).unwrap(), Some("s"));
    assert_eq!(env.find_name_token((start, start + 7)).unwrap(), None);
    assert_eq!(env.find_name_token((start + 2, start + 7)).unwrap(), None);
    let start = source.rfind("token").unwrap();
    assert_eq!(
        env.find_name_token((start, start + 5)).unwrap(),
        Some("token")
    );
    assert_eq!(env.find_name_token((start + 1, start + 5)).unwrap(), None);
    let start = source.find("Counter.Flag.On").unwrap();
    assert_eq!(
        env.find_name_token((start, start + 7)).unwrap(),
        Some("Counter")
    );
    assert_eq!(env.find_name_token((start, start + 15)).unwrap(), None);
}

#[test]
fn indexed_name_token_observer_stop_propagates_with_and_without_candidates() {
    let (inputs, source) = fixture();
    let start = source.rfind("token").unwrap();
    for span in [(start, start + 5), (start + 1, start + 5)] {
        let armed = Rc::new(Cell::new(false));
        let probes = Rc::new(Cell::new(0));
        let (arm, count) = (armed.clone(), probes.clone());
        let control = Control::new(move |_| {
            count.set(count.get() + 1);
            arm.replace(false).then_some(Signal::Term)
        });
        let env = Environment::new(&inputs, &control).unwrap();
        let arm = armed.clone();
        env.observe_optional_name_token(move |actual, _| {
            assert_eq!(actual, span);
            arm.set(true);
        });
        let previous = env
            .state
            .optional_name_context
            .scoped(Some(Default::default()));
        assert!(matches!(
            env.find_name_token(span),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
        previous.restore();
        let frozen = probes.get();
        assert!(matches!(
            env.find_name_token(span),
            Err(ValidationFailure::Stop(Signal::Term))
        ));
        assert_eq!(probes.get(), frozen, "stopped Control does not probe again");
    }
}
