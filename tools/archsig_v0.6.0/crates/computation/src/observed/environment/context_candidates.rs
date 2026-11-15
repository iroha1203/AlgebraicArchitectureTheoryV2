//! 同じ検査epochの不変Graphから、Contextごとの候補位置だけを索引化する。
use super::*;
use std::{ops::Range, rc::Rc};

#[derive(Default)]
pub(super) struct ContextIndex {
    covered_len: usize,
    positions: BTreeMap<super::super::call::Context, Rc<Vec<usize>>>,
    scratch: Option<ScratchContexts>,
}

struct ScratchContexts {
    cutoff: usize,
    changed: BTreeSet<super::super::call::Context>,
}

impl ContextIndex {
    pub(super) fn checkpoint(&mut self, cutoff: usize) {
        self.scratch = Some(ScratchContexts {
            cutoff,
            changed: BTreeSet::new(),
        });
    }

    fn append(&mut self, context: super::super::call::Context, position: usize) {
        debug_assert_eq!(position, self.covered_len);
        if let Some(scratch) = &mut self.scratch
            && position >= scratch.cutoff
        {
            scratch.changed.insert(context);
        }
        Rc::make_mut(self.positions.entry(context).or_default()).push(position);
        // Keep the indexed prefix consistent before the next stop checkpoint.
        self.covered_len = position + 1;
    }

    pub(super) fn rollback(&mut self) {
        let scratch = self.scratch.as_mut().expect("context index checkpoint");
        self.covered_len = self.covered_len.min(scratch.cutoff);
        for context in std::mem::take(&mut scratch.changed) {
            let mut entry = match self.positions.entry(context) {
                std::collections::btree_map::Entry::Occupied(entry) => entry,
                _ => unreachable!("indexed scratch context"),
            };
            let length = entry
                .get()
                .partition_point(|&position| position < scratch.cutoff);
            if length == 0 {
                entry.remove();
            } else {
                Rc::make_mut(entry.get_mut()).truncate(length);
            }
        }
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
            cache.context_candidates.append(context, position);
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
