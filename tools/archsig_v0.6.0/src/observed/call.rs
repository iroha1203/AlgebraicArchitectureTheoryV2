//! 呼出し出現と実引数 Evaluation の非公開索引。wire の Source 引数も同じ既出辺を持つ。
use super::result::NodeRef;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Context {
    pub request: usize,
    pub frame: Option<usize>,
}

#[derive(Clone, Debug)]
pub(super) struct Frame {
    pub caller: Context,
    pub source: NodeRef,
    pub arguments: Vec<NodeRef>,
}
