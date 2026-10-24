//! native構成の元producerと既出入力を、生成・消費の両経路で検査する。
use super::{
    call::Context,
    control::{Checkpoint, Control},
    environment::Environment,
    result::{Graph, NodeRef, ValidationFailure},
};

fn tick(c: &mut Control) -> Result<(), ValidationFailure> {
    c.checkpoint(Checkpoint::NativeResultNode)?;
    Ok(())
}

pub(super) fn saved_context(g: &Graph, r: NodeRef) -> Result<Context, ValidationFailure> {
    if g.contexts.len() != g.nodes.len() {
        return Err("native構成のnode表と保存Context表の長さが違う".into());
    }
    g.contexts
        .get(r.0)
        .copied()
        .ok_or_else(|| "native構成の元nodeに保存Contextがない".into())
}

/// 構成開始より前の元入力だけを保持する。計算結果の正しさは各構成の検査器が担う。
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Boundary {
    start: usize,
    producer: Context,
    architecture: NodeRef,
    inputs: Vec<NodeRef>,
}
impl Boundary {
    pub(super) fn capture(
        env: &Environment<'_>,
        g: &Graph,
        architecture: NodeRef,
        inputs: Vec<NodeRef>,
        c: &mut Control,
    ) -> Result<Self, ValidationFailure> {
        tick(c)?;
        let producer = saved_context(g, architecture)?;
        if g.active != producer
            || producer.frame.is_some()
            || producer.instance.is_some()
            || producer.iteration.is_some()
            || producer.case.is_some()
        {
            return Err("native構成の生成が元Architectureのroot Contextでない".into());
        }
        let boundary = Self {
            start: g.nodes.len(),
            producer,
            architecture,
            inputs,
        };
        boundary.recheck(env, g, boundary.start, c)?;
        Ok(boundary)
    }
    pub(super) fn start(&self) -> usize {
        self.start
    }
    pub(super) fn inputs(&self) -> &[NodeRef] {
        &self.inputs
    }
    pub(super) fn recheck(
        &self,
        env: &Environment<'_>,
        g: &Graph,
        at: usize,
        c: &mut Control,
    ) -> Result<(), ValidationFailure> {
        tick(c)?;
        // 保存済みnodeと挿入位置のcandidateを区別し、欠落Contextをactiveで補わない。
        let actual = if at < g.nodes.len() {
            saved_context(g, NodeRef(at))?
        } else if at == g.nodes.len() && g.contexts.len() == g.nodes.len() {
            g.active
        } else {
            return Err("native構成の保存位置またはContextがない".into());
        };
        if self.start > at
            || actual != self.producer
            || saved_context(g, self.architecture)? != self.producer
        {
            return Err("native構成の開始位置または元producerが違う".into());
        }
        // 全参照を検査してから再帰する。後続wrapperや自己参照へ再入しない。
        for r in std::iter::once(&self.architecture).chain(&self.inputs) {
            tick(c)?;
            if r.0 >= self.start {
                return Err("native構成の元入力が構成開始より前でない".into());
            }
            saved_context(g, *r)?;
        }
        for r in std::iter::once(&self.architecture).chain(&self.inputs) {
            tick(c)?;
            env.recheck_node(g, g.get(*r)?, r.0)?;
        }
        Ok(())
    }
}
