//! Best achievable modularity Q for a dependency graph.
//!
//! sentrux scores modularity as Newman's Q of the file graph, with one module
//! per folder (`module_of`). How high Q can go depends on the graph: a codebase
//! whose files all lean on a shared kernel cannot reach the theoretical
//! 1 - 1/k however its folders are arranged. This module estimates the best Q
//! the graph allows, so a gate can ask "is the folder layout close to the best
//! layout?" instead of "is the graph close to k disconnected islands?".
//!
//! The estimate is directed Louvain (Blondel et al. 2008, with the directed
//! modularity of Leicht & Newman 2008, the same Q sentrux reports), with one
//! constraint: files are only grouped with files under the same top-level
//! directory of the scan. Folders cannot span two top-level directories (two
//! projects, when the scan root is `src`), so a partition that mixes them is
//! not one any folder layout could reach. Louvain is a heuristic, so the result
//! is a lower bound on the true optimum; the one-module-per-top-level-directory
//! partition is also tried and the better of the two is returned.
//!
//! Everything iterates in sorted order, so the result is deterministic.

use crate::core::types::{CallEdge, FileNode, ImportEdge};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// The best partition found: its Q and how many modules it has.
#[derive(Debug, Clone, PartialEq)]
pub struct ModularityOptimum {
    pub modularity_q: f64,
    pub modules: usize,
}

/// The top-level directory of a scan-relative path (the file itself for root files).
pub fn top_level_dir(path: &str) -> &str {
    path.split('/').next().unwrap_or(path)
}

/// Estimate the best Q over partitions that keep each module inside one top-level directory.
/// Uses the same edges and nodes as `root_causes::compute_modularity_q`.
pub fn compute_modularity_optimum(
    import_edges: &[ImportEdge],
    call_edges: &[CallEdge],
    files: &[&FileNode],
) -> ModularityOptimum {
    let mut edge_set: BTreeSet<(&str, &str)> = BTreeSet::new();
    for e in import_edges {
        edge_set.insert((e.from_file.as_str(), e.to_file.as_str()));
    }
    for e in call_edges {
        edge_set.insert((e.from_file.as_str(), e.to_file.as_str()));
    }
    let mut names: BTreeSet<&str> = files
        .iter()
        .filter(|f| !f.is_dir && !f.lang.is_empty())
        .map(|f| f.path.as_str())
        .collect();
    for &(a, b) in &edge_set {
        names.insert(a);
        names.insert(b);
    }
    let names: Vec<&str> = names.into_iter().collect();
    let index: HashMap<&str, usize> = names.iter().enumerate().map(|(i, &n)| (n, i)).collect();
    let edges: Vec<(usize, usize)> = edge_set.iter().map(|&(a, b)| (index[a], index[b])).collect();
    let groups: Vec<&str> = names.iter().map(|n| top_level_dir(n)).collect();

    if edges.is_empty() {
        return ModularityOptimum { modularity_q: 1.0, modules: names.len() };
    }

    let louvain = louvain(names.len(), &edges, &groups);
    let by_group: Vec<usize> = {
        let ids: BTreeMap<&str, usize> = groups.iter().copied().collect::<BTreeSet<_>>()
            .into_iter().enumerate().map(|(i, g)| (g, i)).collect();
        groups.iter().map(|g| ids[g]).collect()
    };

    [louvain, by_group]
        .into_iter()
        .map(|p| ModularityOptimum { modularity_q: modularity(&edges, &p), modules: count(&p) })
        .fold(None, |best: Option<ModularityOptimum>, c| match best {
            Some(b) if b.modularity_q >= c.modularity_q => Some(b),
            _ => Some(c),
        })
        .expect("two candidates")
}

/// Directed Q = (1/m) * sum over edges inside a module, minus sum over modules of out * in / m^2.
fn modularity(edges: &[(usize, usize)], part: &[usize]) -> f64 {
    let m = edges.len() as f64;
    let mut out: HashMap<usize, f64> = HashMap::new();
    let mut inn: HashMap<usize, f64> = HashMap::new();
    let mut intra = 0.0;
    for &(a, b) in edges {
        *out.entry(part[a]).or_default() += 1.0;
        *inn.entry(part[b]).or_default() += 1.0;
        if part[a] == part[b] {
            intra += 1.0;
        }
    }
    let expected: f64 = out.iter().map(|(c, o)| o * inn.get(c).copied().unwrap_or(0.0)).sum::<f64>() / m;
    ((intra - expected) / m).clamp(-0.5, 1.0)
}

fn count(part: &[usize]) -> usize {
    part.iter().collect::<BTreeSet<_>>().len()
}

/// Louvain: move nodes between neighbouring communities while Q rises, then merge each
/// community into one node and repeat, until a whole level moves nothing.
fn louvain(n: usize, edges: &[(usize, usize)], groups: &[&str]) -> Vec<usize> {
    let m = edges.len() as f64;
    // Membership of every original node in the current level's super-nodes.
    let mut part: Vec<usize> = (0..n).collect();
    // Current level: weighted edges between super-nodes, and each super-node's group.
    let mut weights: BTreeMap<(usize, usize), f64> = BTreeMap::new();
    for &(a, b) in edges {
        *weights.entry((a, b)).or_default() += 1.0;
    }
    let mut level_groups: Vec<&str> = groups.to_vec();

    loop {
        let size = level_groups.len();
        let mut k_out = vec![0.0; size];
        let mut k_in = vec![0.0; size];
        let mut neighbours: Vec<BTreeMap<usize, f64>> = vec![BTreeMap::new(); size];
        for (&(a, b), &w) in &weights {
            k_out[a] += w;
            k_in[b] += w;
            if a != b {
                *neighbours[a].entry(b).or_default() += w;
                *neighbours[b].entry(a).or_default() += w;
            }
        }

        let mut community: Vec<usize> = (0..size).collect();
        let mut tot_out = k_out.clone();
        let mut tot_in = k_in.clone();
        let mut moved_any = false;
        let mut moved = true;
        while moved {
            moved = false;
            for s in 0..size {
                let current = community[s];
                tot_out[current] -= k_out[s];
                tot_in[current] -= k_in[s];
                let mut links: BTreeMap<usize, f64> = BTreeMap::new();
                for (&t, &w) in &neighbours[s] {
                    *links.entry(community[t]).or_default() += w;
                }
                let gain = |c: usize| {
                    links.get(&c).copied().unwrap_or(0.0) - (k_out[s] * tot_in[c] + k_in[s] * tot_out[c]) / m
                };
                let mut best = current;
                let mut best_gain = gain(current);
                for &c in links.keys() {
                    if level_groups[c] != level_groups[s] {
                        continue;
                    }
                    let g = gain(c);
                    if g > best_gain + 1e-12 {
                        best = c;
                        best_gain = g;
                    }
                }
                community[s] = best;
                tot_out[best] += k_out[s];
                tot_in[best] += k_in[s];
                if best != current {
                    moved = true;
                    moved_any = true;
                }
            }
        }
        if !moved_any {
            return part;
        }

        // Aggregate: renumber communities 0..c and fold the edges onto them.
        let ids: BTreeMap<usize, usize> = community.iter().copied().collect::<BTreeSet<_>>()
            .into_iter().enumerate().map(|(i, c)| (c, i)).collect();
        for p in part.iter_mut() {
            *p = ids[&community[*p]];
        }
        let mut next_groups = vec![""; ids.len()];
        for s in 0..size {
            next_groups[ids[&community[s]]] = level_groups[s];
        }
        let mut next: BTreeMap<(usize, usize), f64> = BTreeMap::new();
        for (&(a, b), &w) in &weights {
            *next.entry((ids[&community[a]], ids[&community[b]])).or_default() += w;
        }
        weights = next;
        level_groups = next_groups;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edge(a: &str, b: &str) -> ImportEdge {
        ImportEdge { from_file: a.into(), to_file: b.into() }
    }

    #[test]
    fn two_islands_reach_one_half() {
        let edges = vec![edge("p/a1", "p/a2"), edge("p/a2", "p/a1"), edge("p/b1", "p/b2"), edge("p/b2", "p/b1")];
        let best = compute_modularity_optimum(&edges, &[], &[]);
        assert!((best.modularity_q - 0.5).abs() < 1e-9, "got {}", best.modularity_q);
        assert_eq!(best.modules, 2);
    }

    #[test]
    fn modules_never_span_top_level_directories() {
        // One tight pair split across two projects, joined to nothing else: Louvain would
        // merge it, but no folder can hold both files, so the best is one module per project.
        let edges = vec![edge("x/a", "y/b"), edge("y/b", "x/a")];
        let best = compute_modularity_optimum(&edges, &[], &[]);
        assert_eq!(best.modules, 2);
        assert!((best.modularity_q - modularity(&[(0, 1), (1, 0)], &[0, 1])).abs() < 1e-9);
    }

    #[test]
    fn never_below_one_module_per_top_level_directory() {
        let edges = vec![edge("x/a", "x/b"), edge("x/b", "x/c"), edge("y/d", "x/a"), edge("y/d", "y/e")];
        let best = compute_modularity_optimum(&edges, &[], &[]);
        let by_project = modularity(&[(0, 1), (1, 2), (3, 0), (3, 4)], &[0, 0, 0, 1, 1]);
        assert!(best.modularity_q >= by_project - 1e-12);
    }

    #[test]
    fn no_edges_is_trivially_modular() {
        let best = compute_modularity_optimum(&[], &[], &[]);
        assert_eq!(best.modularity_q, 1.0);
    }
}
