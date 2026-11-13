//! 同じ検査epochの不変Graphから、Contextごとの候補位置だけを索引化する。
use super::*;
use std::{ops::Range, rc::Rc};

#[derive(Default)]
pub(super) struct ContextIndex {
    covered_len: usize,
    positions: BTreeMap<super::super::call::Context, Rc<Vec<usize>>>,
}

impl ContextIndex {
    pub(super) fn checkpoint(&self) -> usize {
        self.covered_len
    }
    pub(super) fn rollback(&mut self, covered: usize) {
        self.covered_len = self.covered_len.min(covered);
        self.positions.retain(|_, positions| {
            let length = positions.partition_point(|&position| position < self.covered_len);
            if length < positions.len() {
                Rc::make_mut(positions).truncate(length);
            }
            !positions.is_empty()
        });
    }
}

pub(super) enum CandidateIndices {
    All(Range<usize>),
    Context {
        positions: Rc<Vec<usize>>,
        next: usize,
        end: usize,
    },
}
impl Iterator for CandidateIndices {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        match self {
            Self::All(range) => range.next(),
            Self::Context {
                positions,
                next,
                end,
            } => {
                if *next == *end {
                    None
                } else {
                    let index = positions[*next];
                    *next += 1;
                    Some(index)
                }
            }
        }
    }
}

impl Environment<'_> {
    pub(super) fn context_candidates(
        &self,
        graph: &Graph,
        limit: usize,
    ) -> Result<CandidateIndices, ValidationFailure> {
        let limit = limit.min(graph.nodes.len());
        // nested sessionだけでは同一Graphとは限らない。context_atのactive fallbackも保つ。
        if self.state.validation_graph.get() != Some(graph as *const Graph)
            || graph.contexts.len() != graph.nodes.len()
        {
            return Ok(CandidateIndices::All(0..limit));
        }
        self.tick()?;
        // rootのsnapshot照合が成功したprefixだけを引き継ぎ、clear_validationで同時破棄する。
        let covered = self.results.cache.borrow().context_candidates.covered_len;
        if covered > graph.nodes.len() {
            return Ok(CandidateIndices::All(0..limit));
        }
        for position in covered..graph.nodes.len() {
            self.tick()?;
            let context = graph.context_at(position);
            let mut cache = self.results.cache.borrow_mut();
            let index = &mut cache.context_candidates;
            Rc::make_mut(index.positions.entry(context).or_default()).push(position);
            // appendとcovered_lenの更新の間では停止せず、途中停止でも整合したprefixを残す。
            index.covered_len = position + 1;
        }
        self.tick()?;
        let cache = self.results.cache.borrow();
        let index = &cache.context_candidates;
        let Some(positions) = index.positions.get(&self.current_context(graph)).cloned() else {
            return Ok(CandidateIndices::All(0..0));
        };
        let end = positions.partition_point(|&position| position < limit);
        // 所有Rcを返してRefCell借用を解放し、候補の再検査からの再入を許す。
        Ok(CandidateIndices::Context {
            positions,
            next: 0,
            end,
        })
    }
}

#[cfg(test)]
mod tests;
