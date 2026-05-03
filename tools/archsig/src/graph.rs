use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{Component, Edge, Signature};

pub(crate) fn compute_signature(components: &[Component], edges: &[Edge]) -> Signature {
    let graph = Graph::from_components_and_edges(components, edges);
    let sccs = graph.strongly_connected_components();
    let has_cycle = sccs.iter().any(|scc| {
        scc.len() > 1
            || scc
                .first()
                .is_some_and(|node| graph.neighbors(node).iter().any(|target| target == node))
    });

    Signature {
        has_cycle: usize::from(has_cycle),
        scc_max_size: sccs.iter().map(Vec::len).max().unwrap_or(0),
        max_depth: graph.max_bounded_depth(),
        fanout_risk: graph.unique_edge_count(),
        boundary_violation_count: 0,
        abstraction_violation_count: 0,
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Graph {
    nodes: BTreeSet<String>,
    adjacency: BTreeMap<String, BTreeSet<String>>,
}

impl Graph {
    pub(crate) fn from_components_and_edges(components: &[Component], edges: &[Edge]) -> Self {
        let mut nodes = BTreeSet::new();
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

        for component in components {
            nodes.insert(component.id.clone());
        }

        for edge in edges {
            nodes.insert(edge.source.clone());
            nodes.insert(edge.target.clone());
            adjacency
                .entry(edge.source.clone())
                .or_default()
                .insert(edge.target.clone());
        }

        for node in &nodes {
            adjacency.entry(node.clone()).or_default();
        }

        Self { nodes, adjacency }
    }

    fn neighbors(&self, node: &str) -> Vec<String> {
        self.adjacency
            .get(node)
            .map(|neighbors| neighbors.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn unique_edge_count(&self) -> usize {
        self.adjacency.values().map(BTreeSet::len).sum()
    }

    pub(crate) fn max_fanout(&self) -> usize {
        self.adjacency
            .values()
            .map(BTreeSet::len)
            .max()
            .unwrap_or(0)
    }

    pub(crate) fn reachable_cone_size(&self) -> usize {
        self.nodes
            .iter()
            .map(|node| self.reachable_from(node).len())
            .max()
            .unwrap_or(0)
    }

    fn reachable_from(&self, source: &str) -> BTreeSet<String> {
        let mut visited = BTreeSet::new();
        let mut stack = self.neighbors(source);
        while let Some(node) = stack.pop() {
            if node == source || !visited.insert(node.clone()) {
                continue;
            }
            stack.extend(self.neighbors(&node));
        }
        visited
    }

    fn strongly_connected_components(&self) -> Vec<Vec<String>> {
        let mut visited = HashSet::new();
        let mut order = Vec::new();
        for node in &self.nodes {
            self.dfs_order(node, &mut visited, &mut order);
        }

        let reversed = self.reversed();
        let mut visited = HashSet::new();
        let mut sccs = Vec::new();
        for node in order.iter().rev() {
            if visited.contains(node) {
                continue;
            }
            let mut scc = Vec::new();
            reversed.dfs_collect(node, &mut visited, &mut scc);
            scc.sort();
            sccs.push(scc);
        }
        sccs
    }

    fn dfs_order(&self, node: &str, visited: &mut HashSet<String>, order: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        for neighbor in self.neighbors(node) {
            self.dfs_order(&neighbor, visited, order);
        }
        order.push(node.to_string());
    }

    fn dfs_collect(&self, node: &str, visited: &mut HashSet<String>, scc: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        scc.push(node.to_string());
        for neighbor in self.neighbors(node) {
            self.dfs_collect(&neighbor, visited, scc);
        }
    }

    fn reversed(&self) -> Self {
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for node in &self.nodes {
            adjacency.entry(node.clone()).or_default();
        }

        for (source, targets) in &self.adjacency {
            for target in targets {
                adjacency
                    .entry(target.clone())
                    .or_default()
                    .insert(source.clone());
            }
        }

        Self {
            nodes: self.nodes.clone(),
            adjacency,
        }
    }

    fn max_bounded_depth(&self) -> usize {
        let fuel = self.nodes.len();
        let mut memo = HashMap::new();
        self.nodes
            .iter()
            .map(|node| self.bounded_depth_from(node, fuel, &mut memo))
            .max()
            .unwrap_or(0)
    }

    fn bounded_depth_from(
        &self,
        node: &str,
        fuel: usize,
        memo: &mut HashMap<(String, usize), usize>,
    ) -> usize {
        if fuel == 0 {
            return 0;
        }

        let key = (node.to_string(), fuel);
        if let Some(depth) = memo.get(&key) {
            return *depth;
        }

        let depth = self
            .neighbors(node)
            .iter()
            .map(|target| self.bounded_depth_from(target, fuel - 1, memo) + 1)
            .max()
            .unwrap_or(0);
        memo.insert(key, depth);
        depth
    }
}
