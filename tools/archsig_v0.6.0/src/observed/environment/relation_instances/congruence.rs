//! 元relation両辺を種に、長さを保つ書換えの到達成分と導出を生成する。
use super::*;
use std::collections::{BTreeMap, VecDeque};

type Reference = (String, String, String);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::observed) struct Word {
    pub source: Reference,
    pub target: Reference,
    pub generators: Vec<Reference>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Seed {
    pub instance: usize,
    pub right: bool,
    pub word: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct Rewrite {
    pub from: usize,
    pub to: usize,
    pub instance: usize,
    pub right_to_left: bool,
    pub offset: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct ProofStep {
    pub edge: usize,
    pub backwards: bool,
}
// 呼出し側が現在の元Nodeを検査して取り出す、追加の計算operand。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::observed) struct QueryPath {
    pub path: PathValue,
    pub support: Vec<Fact>,
    pub scope: Scope,
}
#[derive(Clone, PartialEq, Eq)]
pub(in crate::observed) struct Congruence {
    sources: InputSources,
    reading: String,
    queries: Vec<QueryPath>,
    pub query_ids: Vec<usize>,
    pub relations: Option<RelationInstances>,
    pub words: Vec<Word>,
    pub seeds: Vec<Seed>,
    pub edges: Vec<Rewrite>,
    pub classes: Vec<usize>,
    pub unbalanced: Vec<usize>,
    pub support: Vec<Fact>,
    pub scope: Scope,
    complete: bool,
}
pub(in crate::observed) struct CongruenceFailure {
    pub cause: ValidationFailure,
    pub partial: Box<Congruence>,
}
impl std::fmt::Debug for CongruenceFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CongruenceFailure")
            .field("cause", &self.cause)
            .field("words", &self.partial.words.len())
            .finish()
    }
}
fn reference(v: &Scalar) -> Result<Reference, ValidationFailure> {
    match v {
        Scalar::Subject {
            snapshot,
            subject,
            entity,
        } => Ok((snapshot.clone(), subject.clone(), entity.clone())),
        _ => Err("合同語の生成元・端点が原始参照でない".into()),
    }
}
impl Word {
    fn from_path(path: &PathValue, c: &Control) -> Result<Self, ValidationFailure> {
        path.check(c)?;
        let mut generators = vec![];
        if let Some(step) = &path.step {
            for v in std::iter::once(&step.generator).chain(&step.word_tail) {
                tick(c)?;
                generators.push(reference(v)?);
            }
        }
        Ok(Self {
            source: reference(&path.object())?,
            target: reference(&path.target())?,
            generators,
        })
    }
}
fn root(classes: &[usize], mut n: usize, c: &Control) -> Result<usize, ValidationFailure> {
    for _ in 0..classes.len() {
        tick(c)?;
        let next = *classes.get(n).ok_or("合同類の位置がない")?;
        if next == n {
            return Ok(n);
        }
        n = next;
    }
    Err("合同類に循環がある".into())
}
impl Congruence {
    pub fn complete(&self) -> bool {
        self.complete
    }
    pub fn equivalent(
        &self,
        a: usize,
        b: usize,
        c: &Control,
    ) -> Result<Option<bool>, ValidationFailure> {
        tick(c)?;
        if !self.complete {
            return Ok(None);
        }
        Ok(Some(
            root(&self.classes, a, c)? == root(&self.classes, b, c)?,
        ))
    }
    pub fn derivation(
        &self,
        a: usize,
        b: usize,
        c: &Control,
    ) -> Result<Option<Vec<ProofStep>>, ValidationFailure> {
        if self.equivalent(a, b, c)? != Some(true) {
            return Ok(None);
        }
        let mut pending = VecDeque::from([a]);
        let mut previous = BTreeMap::from([(a, None)]);
        while let Some(at) = pending.pop_front() {
            tick(c)?;
            if at == b {
                break;
            }
            for (index, edge) in self.edges.iter().enumerate() {
                tick(c)?;
                let next = if edge.from == at {
                    Some((edge.to, false))
                } else if edge.to == at {
                    Some((edge.from, true))
                } else {
                    None
                };
                if let Some((next, backwards)) = next {
                    if !previous.contains_key(&next) {
                        previous.insert(
                            next,
                            Some((
                                at,
                                ProofStep {
                                    edge: index,
                                    backwards,
                                },
                            )),
                        );
                        pending.push_back(next);
                    }
                }
            }
        }
        let mut at = b;
        let mut proof = vec![];
        while at != a {
            tick(c)?;
            let (from, step) = previous
                .get(&at)
                .and_then(|p| p.as_ref())
                .ok_or("同じ合同類の導出がない")?;
            proof.push(step.clone());
            at = *from;
        }
        proof.reverse();
        tick(c)?;
        Ok(Some(proof))
    }
    pub fn recheck(&self, inputs: &CheckedInputs, c: &Control) -> Result<(), CongruenceFailure> {
        self.recheck_queries(inputs, &[], c)
    }
    pub fn recheck_queries(
        &self,
        inputs: &CheckedInputs,
        queries: &[QueryPath],
        c: &Control,
    ) -> Result<(), CongruenceFailure> {
        if &self.sources != inputs.sources() {
            return Err(CongruenceFailure {
                cause: "合同成分の元三入力が違う".into(),
                partial: Box::new(self.clone()),
            });
        }
        let expected = with_queries(inputs, &self.reading, queries, c)?;
        let result = (|| {
            tick(c)?;
            if self != &expected {
                return Err("合同成分が元関係・到達語・導出と違う".into());
            }
            Ok(())
        })();
        result.map_err(|cause| CongruenceFailure {
            cause,
            partial: Box::new(expected),
        })
    }
    fn insert(
        &mut self,
        word: Word,
        index: &mut BTreeMap<Word, usize>,
        c: &Control,
    ) -> Result<usize, ValidationFailure> {
        tick(c)?;
        if let Some(at) = index.get(&word) {
            return Ok(*at);
        }
        let at = self.words.len();
        index.insert(word.clone(), at);
        self.words.push(word);
        self.classes.push(at);
        Ok(at)
    }
}
struct Rule {
    instance: usize,
    left: Word,
    right: Word,
}
fn closure(out: &mut Congruence, c: &Control) -> Result<(), ValidationFailure> {
    let table = out.relations.as_ref().ok_or("元relation表がない")?;
    let mut rules = vec![];
    for (instance, row) in table.instances.iter().enumerate() {
        tick(c)?;
        if row.state != RelationState::Established {
            continue;
        }
        let (Some(Scalar::Path(a)), Some(Scalar::Path(b))) = (&row.left, &row.right) else {
            return Err("成立relationの元Pathがない".into());
        };
        let left = Word::from_path(a, c)?;
        let right = Word::from_path(b, c)?;
        if left.source != right.source || left.target != right.target {
            return Err("成立relationの実端点が違う".into());
        }
        rules.push(Rule {
            instance,
            left,
            right,
        });
    }
    let verified = table.conditions_verified();
    let mut index = BTreeMap::new();
    for rule in &rules {
        for (right, word) in [(false, &rule.left), (true, &rule.right)] {
            let word = out.insert(word.clone(), &mut index, c)?;
            out.seeds.push(Seed {
                instance: rule.instance,
                right,
                word,
            });
        }
        if rule.left.generators.len() != rule.right.generators.len() {
            out.unbalanced.push(rule.instance);
        }
    }
    for query in out.queries.clone() {
        tick(c)?;
        if query.path.reading != out.reading {
            return Err("追加Pathのreadingが元関係と違う".into());
        }
        let word = Word::from_path(&query.path, c)?;
        let at = out.insert(word, &mut index, c)?;
        out.query_ids.push(at);
        out.support.extend(query.support);
        out.scope.merge(&query.scope);
    }
    out.support.sort();
    out.support.dedup();
    if !verified || !out.unbalanced.is_empty() {
        return Ok(());
    }
    let mut cursor = 0;
    while cursor < out.words.len() {
        tick(c)?;
        let word = out.words[cursor].clone();
        for rule in &rules {
            for (right_to_left, from, to) in [
                (false, &rule.left, &rule.right),
                (true, &rule.right, &rule.left),
            ] {
                tick(c)?;
                let n = from.generators.len();
                // 空語の確認済み関係は同じ実対象の反射律であり、語を変えない。
                if n == 0 || n > word.generators.len() {
                    continue;
                }
                for offset in 0..=word.generators.len() - n {
                    tick(c)?;
                    if word.generators[offset..offset + n] != from.generators[..]
                        || (offset == 0 && word.source != from.source)
                        || (offset + n == word.generators.len() && word.target != from.target)
                    {
                        continue;
                    }
                    // 非空の同じ生成元列は同じ実端点を持つ。確認済み関係で置換するため文脈の型も保つ。
                    let mut next = Word {
                        source: word.source.clone(),
                        target: word.target.clone(),
                        generators: vec![],
                    };
                    for generator in word.generators[..offset]
                        .iter()
                        .chain(&to.generators)
                        .chain(&word.generators[offset + n..])
                    {
                        tick(c)?;
                        next.generators.push(generator.clone());
                    }
                    let next = out.insert(next, &mut index, c)?;
                    let a = root(&out.classes, cursor, c)?;
                    let b = root(&out.classes, next, c)?;
                    if a != b {
                        out.classes[a.max(b)] = a.min(b);
                        out.edges.push(Rewrite {
                            from: cursor,
                            to: next,
                            instance: rule.instance,
                            right_to_left,
                            offset,
                        });
                    }
                }
            }
        }
        cursor += 1;
    }
    for at in 0..out.classes.len() {
        let class = root(&out.classes, at, c)?;
        out.classes[at] = class;
    }
    tick(c)?;
    out.complete = true;
    Ok(())
}
pub(in crate::observed) fn congruence(
    inputs: &CheckedInputs,
    reading: &str,
    c: &Control,
) -> Result<Congruence, CongruenceFailure> {
    with_queries(inputs, reading, &[], c)
}
pub(in crate::observed) fn with_queries(
    inputs: &CheckedInputs,
    reading: &str,
    queries: &[QueryPath],
    c: &Control,
) -> Result<Congruence, CongruenceFailure> {
    let mut out = Congruence {
        sources: inputs.sources().clone(),
        reading: reading.into(),
        queries: queries.to_vec(),
        query_ids: vec![],
        relations: None,
        words: vec![],
        seeds: vec![],
        edges: vec![],
        classes: vec![],
        unbalanced: vec![],
        support: vec![],
        scope: Scope::default(),
        complete: false,
    };
    match relation_instances(inputs, reading, c) {
        Ok(table) => {
            out.support = table.support.clone();
            out.scope = table.scope.clone();
            out.relations = Some(table);
        }
        Err(failure) => {
            out.support = failure.partial.support.clone();
            out.scope = failure.partial.scope.clone();
            out.relations = Some(*failure.partial);
            return Err(CongruenceFailure {
                cause: failure.cause,
                partial: Box::new(out),
            });
        }
    }
    if let Err(cause) = closure(&mut out, c) {
        out.complete = false;
        return Err(CongruenceFailure {
            cause,
            partial: Box::new(out),
        });
    }
    Ok(out)
}
#[cfg(test)]
mod tests;
