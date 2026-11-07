//! 有限の局所関係を保持し、要求された固定条件の下で結合・復元する。
use super::super::result::ValidationFailure;
use archsig_common::control::{Checkpoint, Control};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(in crate::observed) struct Relation {
    pub columns: Vec<usize>,
    pub rows: Arc<Vec<Vec<usize>>>,
}
#[derive(Debug)]
struct Component {
    variables: Vec<usize>,
    relations: Vec<usize>,
}
#[derive(Debug)]
pub(in crate::observed) struct Problem {
    sizes: Vec<usize>,
    relations: Vec<Relation>,
    incident: Vec<Vec<usize>>,
    components: Vec<Component>,
    component_of: Vec<usize>,
    impossible: bool,
}
fn tick(c: &Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::PrimitiveValuation)?;
    Ok(())
}
impl Problem {
    pub fn new(
        sizes: Vec<usize>,
        mut relations: Vec<Relation>,
        c: &Control,
    ) -> Result<Self, ValidationFailure> {
        tick(c)?;
        let mut parent = (0..sizes.len()).collect::<Vec<_>>();
        fn root(parent: &[usize], mut at: usize) -> usize {
            while parent[at] != at {
                at = parent[at];
            }
            at
        }
        let mut incident = vec![vec![]; sizes.len()];
        let mut impossible = sizes.contains(&0);
        for (i, relation) in relations.iter_mut().enumerate() {
            tick(c)?;
            if relation.columns.windows(2).any(|pair| pair[0] >= pair[1])
                || relation.columns.iter().any(|v| *v >= sizes.len())
                || relation.rows.iter().any(|row| {
                    row.len() != relation.columns.len()
                        || row
                            .iter()
                            .zip(&relation.columns)
                            .any(|(v, col)| *v >= sizes[*col])
                })
            {
                return Err(internal!("有限関係の座標・値域が不適合").into());
            }
            if relation.rows.windows(2).any(|w| w[0] >= w[1]) {
                let rows = Arc::make_mut(&mut relation.rows);
                rows.sort();
                rows.dedup();
            }
            impossible |= relation.rows.is_empty();
            for &variable in &relation.columns {
                tick(c)?;
                incident[variable].push(i);
                let first = root(&parent, relation.columns[0]);
                let next = root(&parent, variable);
                parent[next] = first;
            }
        }
        let mut components: Vec<Component> = vec![];
        let mut roots = std::collections::BTreeMap::new();
        let mut component_of = vec![];
        for variable in 0..sizes.len() {
            tick(c)?;
            let r = root(&parent, variable);
            let index = *roots.entry(r).or_insert_with(|| {
                components.push(Component {
                    variables: vec![],
                    relations: vec![],
                });
                components.len() - 1
            });
            component_of.push(index);
            components[index].variables.push(variable);
        }
        for (i, relation) in relations.iter().enumerate() {
            tick(c)?;
            if let Some(&v) = relation.columns.first() {
                components[component_of[v]].relations.push(i);
            }
        }
        Ok(Self {
            sizes,
            relations,
            incident,
            components,
            component_of,
            impossible,
        })
    }
    // 接続を調べた同じ関係を、後続のLaw因子と所有権ごと結合する。
    pub fn into_relations(self) -> Vec<Relation> {
        self.relations
    }
    #[cfg(test)]
    pub(in crate::observed) fn relation_shape(&self) -> (usize, usize, usize) {
        (
            self.relations.len(),
            self.relations.iter().map(|r| r.rows.len()).sum(),
            self.relations
                .iter()
                .map(|r| r.columns.len())
                .max()
                .unwrap_or(0),
        )
    }
    /// 固定した入力座標を除き、残る局所関係の行を共有する。
    pub fn cofactor(&self, pins: &[Option<usize>], c: &Control) -> Result<Self, ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) {
            return Err(internal!("入力の固定座標が不適合").into());
        }
        let mut sizes = vec![];
        let mut map = vec![];
        for (i, size) in self.sizes.iter().enumerate() {
            tick(c)?;
            map.push(if pins[i].is_none() {
                let at = sizes.len();
                sizes.push(*size);
                Some(at)
            } else {
                None
            });
        }
        let mut relations = vec![];
        for relation in &self.relations {
            tick(c)?;
            let columns = relation
                .columns
                .iter()
                .filter_map(|old| map[*old])
                .collect();
            let rows = if relation.columns.iter().all(|old| pins[*old].is_none()) {
                relation.rows.clone()
            } else {
                let mut kept = vec![];
                for row in relation.rows.iter() {
                    tick(c)?;
                    if relation
                        .columns
                        .iter()
                        .zip(row)
                        .all(|(old, v)| pins[*old].is_none_or(|p| p == *v))
                    {
                        kept.push(
                            relation
                                .columns
                                .iter()
                                .zip(row)
                                .filter_map(|(old, v)| map[*old].map(|_| *v))
                                .collect(),
                        );
                    }
                }
                Arc::new(kept)
            };
            relations.push(Relation { columns, rows });
        }
        Self::new(sizes, relations, c)
    }
    /// 元parameterを共有し、各入力の内部座標を別にした共通解を構成する。
    pub fn join(
        problems: &[&Self],
        parameters: usize,
        c: &Control,
    ) -> Result<(Self, Vec<Vec<usize>>), ValidationFailure> {
        let first = problems.first().ok_or(internal!("共通解の入力族が空"))?;
        if parameters > first.sizes.len() {
            return Err(internal!("共通parameterの幅が不適合").into());
        }
        let mut sizes = first.sizes[..parameters].to_vec();
        let mut maps = vec![];
        let mut relations = vec![];
        for problem in problems {
            tick(c)?;
            if problem.sizes.get(..parameters) != Some(&sizes[..parameters]) {
                return Err(internal!("共通parameterの値域が異なる").into());
            }
            let mut map = (0..parameters).collect::<Vec<_>>();
            for size in &problem.sizes[parameters..] {
                tick(c)?;
                map.push(sizes.len());
                sizes.push(*size);
            }
            for relation in &problem.relations {
                tick(c)?;
                relations.push(Relation {
                    columns: relation.columns.iter().map(|old| map[*old]).collect(),
                    rows: relation.rows.clone(),
                });
            }
            maps.push(map);
        }
        Ok((Self::new(sizes, relations, c)?, maps))
    }
    pub fn relations(&self) -> &[Relation] {
        &self.relations
    }
    pub fn share_rows(
        &mut self,
        pool: &mut std::collections::BTreeSet<Arc<Vec<Vec<usize>>>>,
        c: &Control,
    ) -> Result<(), ValidationFailure> {
        for relation in &mut self.relations {
            tick(c)?;
            if let Some(rows) = pool.get(&relation.rows) {
                relation.rows = rows.clone();
            } else {
                pool.insert(relation.rows.clone());
            }
        }
        Ok(())
    }
    pub fn variables(&self) -> usize {
        self.sizes.len()
    }
    fn accepts(
        &self,
        relation: usize,
        point: &[Option<usize>],
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        let relation = &self.relations[relation];
        for row in relation.rows.iter() {
            tick(c)?;
            if relation
                .columns
                .iter()
                .zip(row)
                .all(|(v, x)| point[*v].is_none_or(|p| p == *x))
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn compatible(
        &self,
        variable: usize,
        point: &[Option<usize>],
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        for &relation in &self.incident[variable] {
            if !self.accepts(relation, point, c)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn walk(
        &self,
        component: usize,
        point: &mut [Option<usize>],
        c: &Control,
        mut visit: impl FnMut(&[Option<usize>]) -> bool,
    ) -> Result<(), ValidationFailure> {
        self.walk_try(component, point, c, |point| Ok(visit(point)))
    }
    fn walk_try(
        &self,
        component: usize,
        point: &mut [Option<usize>],
        c: &Control,
        mut visit: impl FnMut(&mut [Option<usize>]) -> Result<bool, ValidationFailure>,
    ) -> Result<(), ValidationFailure> {
        let component = &self.components[component];
        for &relation in &component.relations {
            if !self.accepts(relation, point, c)? {
                return Ok(());
            }
        }
        let free = component
            .variables
            .iter()
            .copied()
            .filter(|v| point[*v].is_none())
            .collect::<Vec<_>>();
        if free.is_empty() {
            visit(point)?;
            return Ok(());
        }
        let mut next = vec![0; free.len()];
        let mut depth = 0;
        loop {
            tick(c)?;
            let variable = free[depth];
            if next[depth] == self.sizes[variable] {
                point[variable] = None;
                next[depth] = 0;
                if depth == 0 {
                    return Ok(());
                }
                depth -= 1;
                continue;
            }
            point[variable] = Some(next[depth]);
            next[depth] += 1;
            if !self.compatible(variable, point, c)? {
                continue;
            }
            if depth + 1 == free.len() {
                if !visit(point)? {
                    for v in free {
                        point[v] = None;
                    }
                    return Ok(());
                }
            } else {
                depth += 1;
            }
        }
    }
    /// 明示的に全点を消費する演算へ、成分の解を一つずつ渡す。
    pub fn visit_solutions(
        &self,
        pins: &[Option<usize>],
        c: &Control,
        mut visit: impl FnMut(&[usize]) -> Result<(), ValidationFailure>,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) {
            return Err(internal!("有限問題の固定座標が不適合").into());
        }
        if self.impossible {
            return Ok(());
        }
        fn components<F: FnMut(&[usize]) -> Result<(), ValidationFailure>>(
            p: &Problem,
            i: usize,
            point: &mut [Option<usize>],
            c: &Control,
            visit: &mut F,
        ) -> Result<(), ValidationFailure> {
            stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
                tick(c)?;
                if i == p.components.len() {
                    let values = point
                        .iter()
                        .copied()
                        .collect::<Option<Vec<_>>>()
                        .ok_or(internal!("全成分の元座標が確定していない"))?;
                    return visit(&values);
                }
                p.walk_try(i, point, c, |point| {
                    components(p, i + 1, point, c, visit)?;
                    Ok(true)
                })
            })
        }
        components(self, 0, &mut pins.to_vec(), c, &mut visit)
    }
    fn valid_pins(&self, pins: &[Option<usize>]) -> bool {
        pins.len() == self.sizes.len()
            && pins
                .iter()
                .zip(&self.sizes)
                .all(|(v, size)| v.is_none_or(|v| v < *size))
    }
    pub fn exists(&self, pins: &[Option<usize>], c: &Control) -> Result<bool, ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) {
            return Err(internal!("有限問題の固定座標が不適合").into());
        }
        if self.impossible {
            return Ok(false);
        }
        let mut point = pins.to_vec();
        for i in 0..self.components.len() {
            let mut exists = false;
            self.walk(i, &mut point, c, |_| {
                exists = true;
                false
            })?;
            if !exists {
                return Ok(false);
            }
        }
        Ok(true)
    }
    /// 生成中の依存探索に必要な一つの合法点。件数は計算しない。
    pub fn witness(
        &self,
        pins: &[Option<usize>],
        c: &Control,
    ) -> Result<Option<Vec<usize>>, ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) {
            return Err(internal!("証人の固定座標が不適合").into());
        }
        if self.impossible {
            return Ok(None);
        }
        let mut point = pins.to_vec();
        for i in 0..self.components.len() {
            let variables = &self.components[i].variables;
            let mut found = None;
            self.walk(i, &mut point, c, |values| {
                found = Some(
                    variables
                        .iter()
                        .map(|v| (*v, values[*v]))
                        .collect::<Vec<_>>(),
                );
                false
            })?;
            let Some(found) = found else {
                return Ok(None);
            };
            for (column, value) in found {
                point[column] = value;
            }
        }
        Ok(Some(
            point
                .into_iter()
                .collect::<Option<Vec<_>>>()
                .ok_or(internal!("証人の座標が未確定"))?,
        ))
    }
    fn count(
        &self,
        component: usize,
        pins: &mut [Option<usize>],
        c: &Control,
    ) -> Result<BigUint, ValidationFailure> {
        let mut count = BigUint::zero();
        self.walk(component, pins, c, |_| {
            count += 1_u32;
            true
        })?;
        Ok(count)
    }
    /// 番号を指定したときだけ必要なfiberを数え、全候補の列を保持せず元座標へ戻す。
    pub fn candidate(
        &self,
        pins: &[Option<usize>],
        mut index: BigUint,
        c: &Control,
    ) -> Result<Option<Vec<usize>>, ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) {
            return Err(internal!("有限問題の固定座標が不適合").into());
        }
        if self.impossible {
            return Ok(None);
        }
        let mut point = pins.to_vec();
        let mut counts = (0..self.components.len())
            .map(|i| self.count(i, &mut point, c))
            .collect::<Result<Vec<_>, _>>()?;
        let mut remaining = counts.iter().fold(BigUint::one(), |a, b| a * b);
        if index >= remaining {
            return Ok(None);
        }
        for variable in 0..self.sizes.len() {
            tick(c)?;
            if point[variable].is_some() {
                continue;
            }
            let component = self.component_of[variable];
            let other = &remaining / &counts[component];
            let mut selected = false;
            for value in 0..self.sizes[variable] {
                tick(c)?;
                point[variable] = Some(value);
                let count = self.count(component, &mut point, c)?;
                let block = &other * &count;
                if index < block {
                    counts[component] = count;
                    remaining = block;
                    selected = true;
                    break;
                }
                index -= block;
            }
            if !selected {
                return Err(internal!("有限fiberの候補復元が不整合").into());
            }
        }
        Ok(Some(
            point
                .into_iter()
                .map(|v| v.expect("全有限座標を復元済み"))
                .collect(),
        ))
    }
    #[cfg(test)]
    pub fn member(
        &self,
        pins: &[Option<usize>],
        point: &[usize],
        c: &Control,
    ) -> Result<bool, ValidationFailure> {
        tick(c)?;
        if !self.valid_pins(pins) || point.len() != self.sizes.len() {
            return Ok(false);
        }
        if self.impossible
            || point.iter().zip(&self.sizes).any(|(v, size)| *v >= *size)
            || pins
                .iter()
                .zip(point)
                .any(|(p, v)| p.is_some_and(|p| p != *v))
        {
            return Ok(false);
        }
        let point = point.iter().map(|v| Some(*v)).collect::<Vec<_>>();
        for relation in 0..self.relations.len() {
            if !self.accepts(relation, &point, c)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn c() -> Control {
        archsig_common::control::quiet()
    }
    fn model(cross: bool) -> Problem {
        let mut relations = vec![
            Relation {
                columns: vec![0],
                rows: vec![vec![1]].into(),
            },
            Relation {
                columns: vec![0, 1],
                rows: vec![vec![0, 0], vec![1, 1]].into(),
            },
            Relation {
                columns: vec![1, 2],
                rows: vec![vec![0, 0], vec![1, 1]].into(),
            },
        ];
        if cross {
            relations.push(Relation {
                columns: vec![3, 4],
                rows: vec![vec![0, 0], vec![1, 1]].into(),
            });
        }
        Problem::new(vec![2; 6], relations, &c()).unwrap()
    }
    #[test]
    fn every_relation_and_consumer_checkpoint_preserves_interruption() {
        use std::{cell::Cell, rc::Rc};
        let run = |stop: Option<usize>| {
            let count = Rc::new(Cell::new(0));
            let seen = count.clone();
            let c = Control::new(move |_| {
                seen.set(seen.get() + 1);
                stop.filter(|n| *n == seen.get())
                    .map(|_| archsig_common::control::Signal::Term)
            });
            let result = (|| {
                let p = Problem::new(
                    vec![2, 2],
                    vec![Relation {
                        columns: vec![0, 1],
                        rows: vec![vec![0, 0], vec![1, 1]].into(),
                    }],
                    &c,
                )?;
                assert!(p.exists(&[None, None], &c)?);
                assert_eq!(p.witness(&[Some(1), None], &c)?, Some(vec![1, 1]));
                let mut reduced = p.cofactor(&[None, Some(1)], &c)?;
                reduced.share_rows(&mut std::collections::BTreeSet::new(), &c)?;
                let (joined, _) = Problem::join(&[&reduced, &reduced], 1, &c)?;
                assert_eq!(joined.witness(&[None], &c)?, Some(vec![1]));
                let point = p.candidate(&[None, None], BigUint::one(), &c)?.unwrap();
                assert!(p.member(&[None, None], &point, &c)?);
                let mut count = 0;
                p.visit_solutions(&[None, None], &c, |_| {
                    count += 1;
                    Ok(())
                })?;
                assert_eq!(count, 2);
                Ok::<_, ValidationFailure>(())
            })();
            (result, count.get())
        };
        let (result, count) = run(None);
        result.unwrap();
        for at in 1..=count {
            assert!(
                matches!(run(Some(at)).0, Err(ValidationFailure::Stop(_))),
                "checkpoint {at}"
            );
        }
    }

    #[test]
    fn local_join_restores_exact_original_assignments_for_every_range() {
        for cross in [false, true] {
            let p = model(cross);
            for mask in 0..8 {
                let pins = (0..6)
                    .map(|i| (i < 3 && mask & (1 << i) == 0).then_some(0))
                    .collect::<Vec<_>>();
                let expected = (0..64)
                    .map(|n| (0..6).map(|i| (n >> (5 - i)) & 1).collect::<Vec<_>>())
                    .filter(|v| {
                        v[0] == 1
                            && v[0] == v[1]
                            && v[1] == v[2]
                            && (!cross || v[3] == v[4])
                            && pins.iter().zip(v).all(|(p, v)| p.is_none_or(|p| p == *v))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(p.exists(&pins, &c()).unwrap(), !expected.is_empty());
                for (i, v) in expected.iter().enumerate() {
                    let actual = p.candidate(&pins, BigUint::from(i), &c()).unwrap().unwrap();
                    assert_eq!(&actual, v);
                    assert!(p.member(&pins, &actual, &c()).unwrap());
                }
                assert!(
                    p.candidate(&pins, BigUint::from(expected.len()), &c())
                        .unwrap()
                        .is_none()
                );
            }
        }
    }
    #[test]
    fn arbitrary_precision_selection_does_not_expand_independent_global_product() {
        let p = Problem::new(vec![2; 54], vec![], &c()).unwrap();
        let last = (BigUint::one() << 54_usize) - BigUint::one();
        assert_eq!(
            p.candidate(&vec![None; 54], last, &c()).unwrap(),
            Some(vec![1; 54])
        );
    }
    #[test]
    fn deterministic_update_keeps_unused_parameter_fiber_and_nonzero_identity() {
        // p,q are original parameters; v=p. q remains a separate free component.
        let p = Problem::new(
            vec![2; 3],
            vec![Relation {
                columns: vec![0, 2],
                rows: vec![vec![0, 0], vec![1, 1]].into(),
            }],
            &c(),
        )
        .unwrap();
        let pins = vec![None, None, Some(1)];
        assert_eq!(
            p.candidate(&pins, BigUint::zero(), &c()).unwrap(),
            Some(vec![1, 0, 1])
        );
        assert_eq!(
            p.candidate(&pins, BigUint::one(), &c()).unwrap(),
            Some(vec![1, 1, 1])
        );
        assert!(
            p.candidate(&pins, BigUint::from(2_u32), &c())
                .unwrap()
                .is_none()
        );
        let reversed = Problem::new(
            vec![2; 2],
            vec![Relation {
                columns: vec![0, 1],
                rows: vec![vec![0, 1], vec![1, 0]].into(),
            }],
            &c(),
        )
        .unwrap();
        assert_eq!(
            reversed
                .candidate(&[None, Some(0)], BigUint::zero(), &c())
                .unwrap(),
            Some(vec![1, 0])
        );
    }
    #[test]
    fn empty_products_false_relations_and_invalid_members_are_distinct() {
        let unit = Problem::new(vec![], vec![], &c()).unwrap();
        assert!(unit.exists(&[], &c()).unwrap());
        assert_eq!(
            unit.candidate(&[], BigUint::zero(), &c()).unwrap(),
            Some(vec![])
        );
        let empty = Problem::new(
            vec![],
            vec![Relation {
                columns: vec![],
                rows: vec![].into(),
            }],
            &c(),
        )
        .unwrap();
        assert!(!empty.exists(&[], &c()).unwrap());
        assert!(!unit.member(&[], &[0], &c()).unwrap());
        assert!(
            Problem::new(
                vec![2],
                vec![Relation {
                    columns: vec![0],
                    rows: vec![vec![2]].into()
                }],
                &c()
            )
            .is_err()
        );
    }
}
