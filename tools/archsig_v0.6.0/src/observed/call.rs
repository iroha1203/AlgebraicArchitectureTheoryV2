//! 呼出し出現と実引数 Evaluation の非公開索引。wire の Source 引数も同じ既出辺を持つ。
use super::result::NodeRef;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Context {
    pub request: usize,
    pub frame: Option<usize>,
    pub iteration: Option<usize>,
    pub instance: Option<usize>,
}

#[derive(Clone, Debug)]
pub(super) struct Frame {
    pub caller: Context,
    pub source: NodeRef,
    pub arguments: Vec<NodeRef>,
}

/// List位置とSetの意味上の要素を区別する。Setの表示ordinalをidentityにしない。
#[derive(Clone, Debug)]
pub(super) enum Member {
    ListPosition(usize),
    SetElement(super::result::Scalar),
}
#[derive(Clone, Debug)]
pub(super) struct Iteration {
    pub caller: Context,
    pub source: NodeRef,
    /// In/内包では元collection Evaluation、型量化では実finite Domain。
    pub domain: NodeRef,
    pub member: Member,
    pub finite: Option<NodeRef>,
}

/// 元Law族の一組。番号は格納索引だけで、identityは元Sourceと実直積member。
#[derive(Clone, Debug)]
pub(super) struct Instance {
    pub caller: Context,
    pub source: NodeRef,
    pub domain: NodeRef,
    pub member: NodeRef,
}
