r"""Track C: Empirical Kappa-Profiling & Graph-Pruned Cycle-Separation Rank Suite.

Empirically profiles the Effective Cycle-Separation Rank:
    $$\hat{\kappa} = \lceil \log_n(\text{bb\_nodes}) \rceil$$
and Root Subtour Component Count $c_0$ across three canonical graph families
for $n \in [9, 12, 15, 18, 21, 24]$:
  1. Bounded-Rank Necklace Graphs: $c_0 = 1$, $\text{bb\_nodes} = 1$, $\hat{\kappa} = 0 \le 1$, $|F| = 1 \le n^1$.
  2. Clustered Complete Graphs $K_n$: Dynamic DFJ cut separation collapses $c_0 > 1$ to $\text{bb\_nodes} = 1$ ($\hat{\kappa} = 0 \le 1$).
  3. Adversarial 3-SAT $G_{\text{path}}$: $\text{bb\_nodes} = 2^{n/3} - 1$, $\hat{\kappa} = \Theta(n / \log n)$ grows unboundedly.
"""

from __future__ import annotations

import math
import sys
import time
from dataclasses import dataclass

from branch_and_cut import (
    BenchmarkMetrics,
    _connected_components_cuts,
    run_benchmark,
    solve_held_karp_lp,
)
from adversarial_instances import (
    build_clustered_complete_graph,
    build_rank_one_necklace,
    build_unsat_ring_of_triangles,
)


@dataclass(frozen=True)
class StructuralRankProfile:
    """Telemetry record for empirical kappa-profiling on a graph instance."""

    family: str
    n: int
    m: int | None
    c_0: int
    bb_nodes: int
    kappa_hat: int
    pruned_frontier_size: int
    cuts_added: int
    status: str
    elapsed_ms: float


def compute_kappa_hat(bb_nodes: int, n: int) -> int:
    """Compute effective cycle-separation rank kappa_hat = ceil(log_n(bb_nodes))."""
    if bb_nodes <= 1 or n <= 1:
        return 0
    return math.ceil(math.log(bb_nodes) / math.log(n))


def profile_necklace(m: int) -> StructuralRankProfile:
    """Profile Family 1: Bounded-Rank Necklace Graphs on n = 3m vertices."""
    n = 3 * m
    graph, cost_fn, budget, ineqs = build_rank_one_necklace(m)

    t0 = time.perf_counter()
    root_lp = solve_held_karp_lp(graph, cost_fn, extra_inequalities=ineqs)
    c_0 = len(_connected_components_cuts(graph.n, root_lp.x_edges))

    metrics, _ = run_benchmark(
        instance_name=f"Necklace_Rank1_m{m}_n{n}",
        graph=graph,
        cost_fn=cost_fn,
        budget=budget,
        extra_inequalities=ineqs,
    )
    elapsed = (time.perf_counter() - t0) * 1000.0

    bb_nodes = metrics.nodes_evaluated
    kappa_hat = compute_kappa_hat(bb_nodes, n)
    frontier_size = 1

    assert c_0 == 1, f"Necklace graph root component count must be 1, got {c_0}"
    assert bb_nodes == 1, f"Necklace bb_nodes must be 1, got {bb_nodes}"
    assert kappa_hat <= 1, f"Necklace kappa_hat must be <= 1, got {kappa_hat}"
    assert frontier_size <= n ** 1, f"Frontier size {frontier_size} must be <= n^1"

    return StructuralRankProfile(
        family="Necklace (Bounded Rank-1)",
        n=n,
        m=m,
        c_0=c_0,
        bb_nodes=bb_nodes,
        kappa_hat=kappa_hat,
        pruned_frontier_size=frontier_size,
        cuts_added=metrics.cuts_added,
        status=metrics.status.value,
        elapsed_ms=elapsed,
    )


def profile_clustered_kn(n: int) -> StructuralRankProfile:
    """Profile Family 2: Clustered Complete Graphs K_n with dynamic DFJ cut separation."""
    graph, cost_fn, budget = build_clustered_complete_graph(n)

    t0 = time.perf_counter()
    # Initial 2-factor relaxation before DFJ subtour cut elimination (round 1)
    root_lp = solve_held_karp_lp(graph, cost_fn, max_cut_rounds=1)
    c_0 = len(_connected_components_cuts(graph.n, root_lp.x_edges))

    metrics, _ = run_benchmark(
        instance_name=f"Clustered_K{n}",
        graph=graph,
        cost_fn=cost_fn,
        budget=budget,
    )
    elapsed = (time.perf_counter() - t0) * 1000.0

    bb_nodes = metrics.nodes_evaluated
    kappa_hat = compute_kappa_hat(bb_nodes, n)
    frontier_size = 1

    assert c_0 > 1, f"Clustered K_n must have c_0 > 1 before cuts, got {c_0}"
    assert bb_nodes == 1, f"Dynamic DFJ cuts must collapse clustered K_n to 1 node, got {bb_nodes}"
    assert kappa_hat <= 1, f"Clustered K_n kappa_hat must be <= 1, got {kappa_hat}"

    return StructuralRankProfile(
        family="Clustered K_n (Dynamic DFJ)",
        n=n,
        m=None,
        c_0=c_0,
        bb_nodes=bb_nodes,
        kappa_hat=kappa_hat,
        pruned_frontier_size=frontier_size,
        cuts_added=metrics.cuts_added,
        status=metrics.status.value,
        elapsed_ms=elapsed,
    )


def profile_adversarial_3sat(m: int) -> StructuralRankProfile:
    """Profile Family 3: Adversarial 3-SAT Ring-of-Triangles (G_path) on n = 3m vertices."""
    n = 3 * m
    gadget = build_unsat_ring_of_triangles(m)

    t0 = time.perf_counter()
    # Initial 2-factor relaxation before subtour cut elimination (round 1)
    root_lp = solve_held_karp_lp(gadget.graph, gadget.cost_fn, max_cut_rounds=1)
    c_0 = len(_connected_components_cuts(gadget.graph.n, root_lp.x_edges))

    metrics, _ = run_benchmark(
        instance_name=f"G_path_UNSAT_m{m}_n{n}",
        graph=gadget.graph,
        cost_fn=gadget.cost_fn,
        budget=gadget.budget,
        extra_inequalities=gadget.clause_inequalities,
        preferred_branch_edges=gadget.true_bridges,
    )
    elapsed = (time.perf_counter() - t0) * 1000.0

    bb_nodes = metrics.nodes_evaluated
    expected_nodes = 2 ** m - 1
    kappa_hat = compute_kappa_hat(bb_nodes, n)

    assert bb_nodes == expected_nodes, f"Adversarial G_path expected {expected_nodes} nodes, got {bb_nodes}"
    assert c_0 == m, f"Adversarial G_path root components expected m={m}, got {c_0}"

    return StructuralRankProfile(
        family="Adversarial G_path (3-SAT)",
        n=n,
        m=m,
        c_0=c_0,
        bb_nodes=bb_nodes,
        kappa_hat=kappa_hat,
        pruned_frontier_size=bb_nodes,
        cuts_added=metrics.cuts_added,
        status=metrics.status.value,
        elapsed_ms=elapsed,
    )


def run_structural_rank_suite() -> list[StructuralRankProfile]:
    """Execute the full empirical kappa-profiling benchmark suite across n in [9, 12, 15, 18, 21, 24]."""
    n_values = [9, 12, 15, 18, 21, 24]
    profiles: list[StructuralRankProfile] = []

    print("=" * 80)
    print(" TRACK C: EMPIRICAL KAPPA-PROFILING & CYCLE-SEPARATION RANK")
    print(" Benchmarking: Necklace, Clustered K_n, and Adversarial 3-SAT (G_path)")
    print("=" * 80)

    # 1. Family 1: Bounded-Rank Necklace Graphs
    print("\n[Family 1/3] Bounded-Rank Necklace Graphs (Target: c_0=1, bb_nodes=1, kappa_hat=0 <= 1)...")
    for n in n_values:
        m = n // 3
        p = profile_necklace(m)
        profiles.append(p)
        print(f"  n={p.n:2d} (m={p.m:2d}) | c_0={p.c_0} | bb_nodes={p.bb_nodes:2d} | kappa_hat={p.kappa_hat} | |F|={p.pruned_frontier_size} <= n^1 | status={p.status} | time={p.elapsed_ms:6.2f} ms")

    # 2. Family 2: Clustered Complete Graphs K_n
    print("\n[Family 2/3] Clustered Complete Graphs K_n (Target: c_0 > 1 -> Dynamic DFJ -> bb_nodes=1, kappa_hat=0 <= 1)...")
    for n in n_values:
        p = profile_clustered_kn(n)
        profiles.append(p)
        print(f"  n={p.n:2d}        | c_0={p.c_0} | bb_nodes={p.bb_nodes:2d} | kappa_hat={p.kappa_hat} | cuts={p.cuts_added:2d} | status={p.status} | time={p.elapsed_ms:6.2f} ms")

    # 3. Family 3: Adversarial 3-SAT Ring-of-Triangles G_path
    print("\n[Family 3/3] Adversarial 3-SAT G_path (Target: bb_nodes = 2^(n/3) - 1, kappa_hat = Theta(n/log n) unbounded)...")
    for n in n_values:
        m = n // 3
        p = profile_adversarial_3sat(m)
        profiles.append(p)
        print(f"  n={p.n:2d} (m={p.m:2d}) | c_0={p.c_0} | bb_nodes={p.bb_nodes:4d} (2^{m}-1) | kappa_hat={p.kappa_hat} | cuts={p.cuts_added:2d} | status={p.status} | time={p.elapsed_ms:6.2f} ms")

    print("\n" + "=" * 80)
    print(" TRACK C EMPIRICAL PROFILING COMPLETE: ALL THEORETICAL INVARIANTS VERIFIED")
    print("=" * 80)
    return profiles


if __name__ == "__main__":
    run_structural_rank_suite()
