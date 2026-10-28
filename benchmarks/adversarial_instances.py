"""Adversarial Stress Test Suite & Benchmark Runner for Decision TSP.

Constructs and benchmarks the canonical counterexample families formalized in
`TSPComplexity.lean` and analyzed in `MONOGRAPH.md`:
  1. The 10-vertex **Petersen Graph** ($P_{10}$):
     - Demonstrates the fractional Held-Karp stall at $x_e = 2/3$ (and half-integral
       basic feasible stall after dynamic DFJ subtour separation) with no integer tour.
     - Demonstrates the hyperplane separation `petersenSepCost` on $K_{10}$ (LP cost $0.0$
       vs integral tour cost $1.0$).
  2. The **Ring-of-Triangles 3-SAT Gadget Graph** ($G_{\\text{path}}$):
     - Demonstrates how the initial 2-factor relaxation collapses into $m = |V|/3$
       disconnected 0-cost triangles $F^{(0)} = \\bigcup_{i=1}^m T_i$.
     - Demonstrates that after adding DFJ subtour cuts, the Held-Karp LP stalls at the
       half-integral point $x(e_{i,T}) = x(e_{i,F}) = 1/2$, where every 3-SAT clause
       inequality has slack ($1/2 + 1/2 + 1/2 = 1.5 \\le 2$).
     - Empirically proves the exponential branch-and-bound node explosion $\\Omega(2^{|V|/3})$.
  3. The **Bounded Cycle-Separation Rank ($\\kappa = 1$) Necklace Graph** & **Complete Graphs $K_n$**:
     - Control families validating `polynomial_termination_rank_one` and comparing
       Stoer-Wagner vs. Edmonds-Karp DFJ min-cut separation.
  4. The **Yannakakis DFJ Subtour Slack Matrix** ($S_{\\text{DFJ}}(n)$) & **Petersen Cut Slack Profile**:
     - Computes the exact $(2^n - 2) \\times ((n-1)!/2)$ subtour slack matrix (`IJM.TSP.dfjSlack`)
       for $n \\in \\{4, 5, 6, 7\\}$ and profiles all $2^{10} - 2 = 1022$ proper cuts of $P_{10}$.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Sequence

import numpy as np

from branch_and_cut import (
    BenchmarkMetrics,
    CostFunction,
    Edge,
    Graph,
    HeldKarpVerification,
    LinearInequality,
    LPRelaxationResult,
    SearchStatusKind,
    YannakakisSlackMatrixResult,
    canonical_edge,
    compute_yannakakis_dfj_slack_matrix,
    dfj_slack,
    enumerate_dfj_cuts,
    run_benchmark,
    separate_dfj_subtour_cuts,
    solve_held_karp_lp,
    verify_held_karp_point,
)


# ---------------------------------------------------------------------------
# 1. The 10-Vertex Petersen Graph (P_10)
# ---------------------------------------------------------------------------


def petersen_adj(u: int, v: int) -> bool:
    """Exact translation of `IJM.TSP.petersenAdj` in `TSPComplexity.lean` (lines 1285-1291).

    Vertices:
      - 0..4: Outer 5-cycle
      - 5..9: Inner 5-star
    """
    if u == v or not (0 <= u < 10 and 0 <= v < 10):
        return False
    outer_cycle = u < 5 and v < 5 and ((u + 1) % 5 == v or (v + 1) % 5 == u)
    inner_star = (
        u >= 5
        and v >= 5
        and (((u - 5) + 2) % 5 == (v - 5) or ((v - 5) + 2) % 5 == (u - 5))
    )
    spoke_uv = u < 5 and v >= 5 and v == u + 5
    spoke_vu = u >= 5 and v < 5 and u == v + 5
    return outer_cycle or inner_star or spoke_uv or spoke_vu


def build_petersen_graph() -> Graph:
    """Construct the 10-vertex, 15-edge Petersen graph $P_{10}$."""
    edges: list[Edge] = []
    for u in range(10):
        for v in range(u + 1, 10):
            if petersen_adj(u, v):
                edges.append((u, v))
    return Graph(n=10, edges=tuple(edges))


def build_petersen_fractional_matrix() -> np.ndarray:
    """Construct `IJM.TSP.petersenFractional` ($x_e = 2/3$ on $E(P_{10})$, $0$ elsewhere)."""
    mat = np.zeros((10, 10), dtype=float)
    for u in range(10):
        for v in range(10):
            if petersen_adj(u, v):
                mat[u, v] = 2.0 / 3.0
    return mat


def petersen_unit_cost(u: int, v: int) -> float:
    """Uniform edge cost $c_e = 1$ on $P_{10}$."""
    return 1.0 if petersen_adj(u, v) else 100.0


def petersen_sep_cost(u: int, v: int) -> float:
    """Exact translation of `IJM.TSP.petersenSepCost` in `TSPComplexity.lean` (line 1415).

    Assigns cost 0 to Petersen edges and cost 1 to non-Petersen edges in $K_{10}$.
    """
    if u == v:
        return 0.0
    return 0.0 if petersen_adj(u, v) else 1.0


@dataclass(frozen=True)
class PetersenAnalysisReport:
    """Detailed empirical report for the 10-vertex Petersen graph integrality gap."""

    hk_verification: HeldKarpVerification
    stoer_wagner_min_cut: float
    edmonds_karp_min_cut: float
    lp_two_thirds_stall: LPRelaxationResult
    lp_dynamic_cut_stall: LPRelaxationResult
    p10_branch_and_cut_metrics: BenchmarkMetrics
    k10_sep_budget_zero_metrics: BenchmarkMetrics
    k10_sep_budget_one_metrics: BenchmarkMetrics


def run_petersen_experiments() -> PetersenAnalysisReport:
    """Execute the full suite of Petersen graph polyhedral and branch-and-cut tests."""
    p10 = build_petersen_graph()
    x_mat = build_petersen_fractional_matrix()
    hk_ver = verify_held_karp_point(10, x_mat)

    x_edges_two_thirds = {e: 2.0 / 3.0 for e in p10.edges}
    sw_sep = separate_dfj_subtour_cuts(10, x_edges_two_thirds, method="stoer_wagner")
    ek_sep = separate_dfj_subtour_cuts(10, x_edges_two_thirds, method="edmonds_karp")

    # 1. Held-Karp LP with edge capacity 2/3: unique feasible/optimal point is x_e = 2/3 on all 15 edges
    lp_two_thirds = solve_held_karp_lp(
        graph=p10,
        cost_fn=petersen_unit_cost,
        edge_upper_bound=2.0 / 3.0,
        separation_method="stoer_wagner",
    )

    # 2. Held-Karp LP with standard [0, 1] bounds starting from 0 subtour cuts:
    #    Dynamically separates disconnected 5-cycle 2-factors and stalls at a half-integral vertex.
    lp_dynamic = solve_held_karp_lp(
        graph=p10,
        cost_fn=petersen_unit_cost,
        edge_upper_bound=1.0,
        separation_method="stoer_wagner",
    )

    # 3. Full Branch-and-Cut on P_10 (proves no Hamiltonian tour exists -> REJECTED)
    p10_metrics, _ = run_benchmark(
        instance_name="Petersen_P10_Hypohamiltonian",
        graph=p10,
        cost_fn=petersen_unit_cost,
        budget=10.0,
    )

    # 4. Hyperplane separation on K_10 with petersenSepCost (B = 0 -> REJECTED, B = 1 -> ACCEPTED)
    k10 = Graph.complete(10)
    k10_b0_metrics, _ = run_benchmark(
        instance_name="Petersen_K10_SepCost_B0",
        graph=k10,
        cost_fn=petersen_sep_cost,
        budget=0.0,
    )
    k10_b1_metrics, _ = run_benchmark(
        instance_name="Petersen_K10_SepCost_B1",
        graph=k10,
        cost_fn=petersen_sep_cost,
        budget=1.0,
    )

    return PetersenAnalysisReport(
        hk_verification=hk_ver,
        stoer_wagner_min_cut=sw_sep.min_cut_capacity,
        edmonds_karp_min_cut=ek_sep.min_cut_capacity,
        lp_two_thirds_stall=lp_two_thirds,
        lp_dynamic_cut_stall=lp_dynamic,
        p10_branch_and_cut_metrics=p10_metrics,
        k10_sep_budget_zero_metrics=k10_b0_metrics,
        k10_sep_budget_one_metrics=k10_b1_metrics,
    )


# ---------------------------------------------------------------------------
# 2. Ring-of-Triangles 3-SAT Gadget Graph (G_path)
# ---------------------------------------------------------------------------

Literal3SAT = tuple[int, bool]  # (variable_index in 0..m-1, polarity True/False)
Clause3SAT = tuple[Literal3SAT, Literal3SAT, Literal3SAT]


@dataclass(frozen=True)
class RingOfTrianglesGadget:
    r"""Ring-of-Triangles 3-SAT Reduction Graph $G_{\text{path}}(m, \Phi)$.

    Matches Section 3 of `MONOGRAPH.md` and `IJM.TSP.Reduction.TSPGadget` in `TSPComplexity.lean`:
      - $|V| = 3m$ vertices partitioned into $m$ disjoint triangles $T_i = \{3i, 3i+1, 3i+2\}$.
      - Internal triangle edges have weight $c(e) = 0$.
      - Between $T_i$ and $T_{(i+1) \bmod m}$, two symmetric bridge edges of weight $c(e) = 1$:
          * $e_{i, \text{True}}  = (3i+2, 3((i+1) \bmod m))$  (traversed when $T_i$ is oriented $3i \to 3i+1 \to 3i+2$)
          * $e_{i, \text{False}} = (3i+1, 3((i+1) \bmod m))$  (traversed when $T_i$ is oriented $3i \to 3i+2 \to 3i+1$)
      - Each 3-SAT clause $C_j = (\ell_{j,1} \lor \ell_{j,2} \lor \ell_{j,3})$ forbids selecting all three
        falsifying bridge edges simultaneously:
          $$x(\overline{e}_{j,1}) + x(\overline{e}_{j,2}) + x(\overline{e}_{j,3}) \le 2.$$
    """

    m: int
    n: int
    graph: Graph
    cost_fn: CostFunction
    budget: float
    true_bridges: tuple[Edge, ...]
    false_bridges: tuple[Edge, ...]
    clauses: tuple[Clause3SAT, ...]
    clause_inequalities: tuple[LinearInequality, ...]
    satisfiable: bool


def build_ring_of_triangles_gadget(
    m: int,
    clauses: Sequence[Clause3SAT],
    satisfiable: bool,
) -> RingOfTrianglesGadget:
    r"""Construct the Ring-of-Triangles 3-SAT gadget graph $G_{\text{path}}$ for $m \ge 3$ triangles."""
    if m < 3:
        raise ValueError("Ring-of-Triangles 3-SAT gadget requires m >= 3 triangles")

    n = 3 * m
    edges: list[Edge] = []
    edge_costs: dict[Edge, float] = {}
    true_bridges: list[Edge] = []
    false_bridges: list[Edge] = []

    for i in range(m):
        v0, v1, v2 = 3 * i, 3 * i + 1, 3 * i + 2
        # Zero-cost internal triangle edges
        for u, v in ((v0, v1), (v1, v2), (v0, v2)):
            e = canonical_edge(u, v)
            edges.append(e)
            edge_costs[e] = 0.0

        # Cost-1 variable choice bridges to the entry vertex of triangle (i + 1) % m
        next_entry = 3 * ((i + 1) % m)
        e_true = canonical_edge(v2, next_entry)
        e_false = canonical_edge(v1, next_entry)
        edges.append(e_true)
        edges.append(e_false)
        edge_costs[e_true] = 1.0
        edge_costs[e_false] = 1.0
        true_bridges.append(e_true)
        false_bridges.append(e_false)

    graph = Graph(n=n, edges=tuple(edges))

    def cost_fn(u: int, v: int) -> float:
        if u == v:
            return 0.0
        return edge_costs.get(canonical_edge(u, v), float(100 * m))

    inequalities: list[LinearInequality] = []
    for i in range(m):
        v0, v1, v2 = 3 * i, 3 * i + 1, 3 * i + 2
        # Flow coupling inside triangle T_i:
        # Exiting via e_{i,True} (v2) visits v0 -> v1 -> v2, so x(v0, v2) + x(e_{i,True}) <= 1
        inequalities.append(
            LinearInequality(
                coeffs={canonical_edge(v0, v2): 1.0, true_bridges[i]: 1.0},
                rhs=1.0,
                label=f"T_{i}_true_orientation",
            )
        )
        # Exiting via e_{i,False} (v1) visits v0 -> v2 -> v1, so x(v0, v1) + x(e_{i,False}) <= 1
        inequalities.append(
            LinearInequality(
                coeffs={canonical_edge(v0, v1): 1.0, false_bridges[i]: 1.0},
                rhs=1.0,
                label=f"T_{i}_false_orientation",
            )
        )

    for c_idx, clause in enumerate(clauses):
        coeffs: dict[Edge, float] = {}
        for var_idx, pol in clause:
            falsifying_bridge = false_bridges[var_idx] if pol else true_bridges[var_idx]
            coeffs[falsifying_bridge] = coeffs.get(falsifying_bridge, 0.0) + 1.0
        inequalities.append(
            LinearInequality(
                coeffs=coeffs,
                rhs=2.0,
                label=f"Clause_{c_idx}",
            )
        )

    return RingOfTrianglesGadget(
        m=m,
        n=n,
        graph=graph,
        cost_fn=cost_fn,
        budget=float(m),
        true_bridges=tuple(true_bridges),
        false_bridges=tuple(false_bridges),
        clauses=tuple(clauses),
        clause_inequalities=tuple(inequalities),
        satisfiable=satisfiable,
    )


def build_unsat_ring_of_triangles(m: int) -> RingOfTrianglesGadget:
    r"""Build an unsatisfiable Ring-of-Triangles 3-SAT instance on $m$ triangles ($|V| = 3m$).

    Couples every prefix variable $x_i$ ($0 \le i < m-3$) to the tail variables $(x_{m-2}, x_{m-1})$
    via XOR-3-SAT parity clauses $x_i \oplus x_{m-2} \oplus x_{m-1} = 0$, and places all 8 polarity
    clauses on $(x_{m-3}, x_{m-2}, x_{m-1})$.
    Because the continuous LP relaxation assigns $x(e_{j,T}) = x(e_{j,F}) = 0.5$ to unfixed tail
    triangles, every 3-SAT clause evaluates to $1.0 + 0.5 + 0.5 = 2.0 \le 2.0$ until depth $m - 1$.
    Thus, the Branch-and-Cut tree must evaluate exactly $2^m - 1 = 2^{|V|/3} - 1$ nodes!
    """
    a, b, c = m - 3, m - 2, m - 1
    clauses: list[Clause3SAT] = []
    # Couple all earlier variables i in 0 .. m-4 to (b, c) via 4 XOR-3-SAT clauses
    for i in range(m - 3):
        for p_i in (True, False):
            for p_b in (True, False):
                for p_c in (True, False):
                    if p_i ^ p_b ^ p_c:
                        clauses.append(((i, p_i), (b, p_b), (c, p_c)))

    # Complete 8-clause obstruction on the tail triple (a, b, c)
    for p_a in (True, False):
        for p_b in (True, False):
            for p_c in (True, False):
                clauses.append(((a, p_a), (b, p_b), (c, p_c)))

    return build_ring_of_triangles_gadget(m=m, clauses=clauses, satisfiable=False)


def build_unique_sat_ring_of_triangles(m: int) -> RingOfTrianglesGadget:
    r"""Build a uniquely satisfiable Ring-of-Triangles 3-SAT instance on $m$ triangles ($|V| = 3m$).

    The unique satisfying assignment is $x_0 = x_1 = \dots = x_{m-1} = \text{False}$
    (explored last when branching $x(e_{i,T}) = 1$ before $x(e_{i,T}) = 0$).
    Clauses on the tail variables $(x_{m-3}, x_{m-2}, x_{m-1})$ force the branch-and-cut
    tree to explore $\Omega(2^{|V|/3})$ nodes before discovering the unique valid tour.
    """
    a, b, c = m - 3, m - 2, m - 1
    clauses: list[Clause3SAT] = []
    # On the last 3 variables (a, b, c), forbid all 7 combinations except (False, False, False)
    for p_a in (True, False):
        for p_b in (True, False):
            for p_c in (True, False):
                if (p_a, p_b, p_c) == (False, False, False):
                    continue
                clauses.append(((a, not p_a), (b, not p_b), (c, not p_c)))

    # For earlier variables i in 0 .. m-4, forbid x_i = True when (x_{m-2}, x_{m-1}) = (False, False)
    for i in range(m - 3):
        clauses.append(((i, False), (b, True), (c, True)))

    return build_ring_of_triangles_gadget(m=m, clauses=clauses, satisfiable=True)


def build_rank_one_necklace(m: int) -> tuple[Graph, CostFunction, float, list[LinearInequality]]:
    r"""Build a Bounded Cycle-Separation Rank ($\kappa = 1$) necklace instance on $|V| = 3m$ vertices.

    Breaks the 3-SAT variable symmetry by giving $e_{i, \text{True}}$ cost $1.0$ and
    $e_{i, \text{False}}$ cost $2.0$. Dynamic DFJ subtour cuts at the root node immediately
    produce the unique integral tour of cost $m$ in **1 branch-and-bound node**, empirically
    confirming `polynomial_termination_rank_one` in `TSPComplexity.lean`.
    """
    gadget = build_ring_of_triangles_gadget(m=m, clauses=(), satisfiable=True)
    true_set = set(gadget.true_bridges)
    false_set = set(gadget.false_bridges)

    def asymmetric_cost(u: int, v: int) -> float:
        if u == v:
            return 0.0
        e = canonical_edge(u, v)
        if e in true_set:
            return 1.0
        if e in false_set:
            return 2.0
        if gadget.graph.has_edge(u, v):
            return 0.0
        return float(100 * m)

    return gadget.graph, asymmetric_cost, float(m), list(gadget.clause_inequalities)


def build_clustered_complete_graph(n: int) -> tuple[Graph, CostFunction, float]:
    """Construct a complete graph $K_n$ with two tight clusters to test DFJ subtour cut separation."""
    graph = Graph.complete(n)
    half = n // 2
    # Place vertices on two separated circles in 2D so initial degree-2 LP forms 2 disjoint subtours
    coords: list[tuple[float, float]] = []
    for i in range(half):
        angle = 2.0 * math.pi * i / half
        coords.append((math.cos(angle), math.sin(angle)))
    for i in range(n - half):
        angle = 2.0 * math.pi * i / (n - half)
        coords.append((10.0 + math.cos(angle), math.sin(angle)))

    dist_mat = np.zeros((n, n), dtype=float)
    for u in range(n):
        for v in range(u + 1, n):
            d = round(math.hypot(coords[u][0] - coords[v][0], coords[u][1] - coords[v][1]) * 10.0)
            dist_mat[u, v] = d
            dist_mat[v, u] = d

    def cost_fn(u: int, v: int) -> float:
        return float(dist_mat[u, v])

    return graph, cost_fn, 500.0


@dataclass(frozen=True)
class PetersenSlackProfile:
    r"""Complete DFJ cut slack profile of `petersenFractional` across all $2^{10} - 2 = 1022$ cuts.

    Corresponds directly to `petersen_dfjSlack_singleton_zero` and
    `petersen_dfjSlack_nontrivial_ge_two_thirds` in `TSPComplexity.lean`.
    """

    total_dfj_cuts: int
    singleton_cosingleton_cuts: int
    nontrivial_cuts: int
    min_slack_all: float
    max_slack_all: float
    singleton_all_zero: bool
    min_nontrivial_slack: float
    cut_edge_cardinality_histogram: dict[int, int]


def compute_petersen_dfj_slack_profile() -> PetersenSlackProfile:
    r"""Evaluate `dfjSlack petersenFractional S` across all $2^{10} - 2 = 1022$ proper cuts $S \in \text{DFJCut}(10)$."""
    x_mat = build_petersen_fractional_matrix()
    adj_mat = (x_mat > 0.5).astype(int)
    cuts = enumerate_dfj_cuts(10)

    singleton_slacks: list[float] = []
    nontrivial_slacks: list[float] = []
    edge_hist: dict[int, int] = {}

    for s in cuts:
        slack_val = dfj_slack(x_mat, s)
        s_idx = sorted(s)
        comp_idx = [v for v in range(10) if v not in s]
        num_edges = int(np.sum(adj_mat[np.ix_(s_idx, comp_idx)]))
        edge_hist[num_edges] = edge_hist.get(num_edges, 0) + 1

        if len(s) in (1, 9):
            singleton_slacks.append(slack_val)
        else:
            nontrivial_slacks.append(slack_val)

    all_slacks = singleton_slacks + nontrivial_slacks
    singleton_zero = all(abs(val) <= 1e-9 for val in singleton_slacks)

    return PetersenSlackProfile(
        total_dfj_cuts=len(cuts),
        singleton_cosingleton_cuts=len(singleton_slacks),
        nontrivial_cuts=len(nontrivial_slacks),
        min_slack_all=float(min(all_slacks)),
        max_slack_all=float(max(all_slacks)),
        singleton_all_zero=singleton_zero,
        min_nontrivial_slack=float(min(nontrivial_slacks)),
        cut_edge_cardinality_histogram=dict(sorted(edge_hist.items())),
    )


# ---------------------------------------------------------------------------
# 3. Full Benchmark Suite Execution
# ---------------------------------------------------------------------------


def run_all_benchmarks() -> dict[str, object]:
    """Run all Petersen, Ring-of-Triangles ($G_{\\text{path}}$), Rank-1, $K_n$, and Yannakakis Slack benchmarks."""
    print("=" * 88)
    print("PHASE 5 & 9 BENCHMARK SUITE: HELD-KARP LP, BRANCH-AND-CUT & YANNAKAKIS SLACK MATRICES")
    print("=" * 88)

    # Part 1: Petersen Graph Suite
    print("\n[1/4] Running 10-Vertex Petersen Graph (P_10) Integrality Gap Suite...")
    petersen_report = run_petersen_experiments()
    print(
        f"  - HeldKarpPoint Verification (x_e = 2/3): valid={petersen_report.hk_verification.is_valid}, "
        f"max_deg_err={petersen_report.hk_verification.max_degree_error:.2e}, "
        f"SW_min_cut={petersen_report.stoer_wagner_min_cut:.4f}, "
        f"EK_min_cut={petersen_report.edmonds_karp_min_cut:.4f}"
    )
    print(
        f"  - P_10 LP (x_e <= 2/3): obj={petersen_report.lp_two_thirds_stall.objective:.4f}, "
        f"min_cut={petersen_report.lp_two_thirds_stall.min_cut_capacity:.4f}, "
        f"frac_edges={len(petersen_report.lp_two_thirds_stall.fractional_edges)}"
    )
    print(
        f"  - P_10 LP (dynamic DFJ cuts): obj={petersen_report.lp_dynamic_cut_stall.objective:.4f}, "
        f"cuts_added={petersen_report.lp_dynamic_cut_stall.cuts_added}, "
        f"lp_rounds={petersen_report.lp_dynamic_cut_stall.lp_rounds}, "
        f"min_cut={petersen_report.lp_dynamic_cut_stall.min_cut_capacity:.4f}, "
        f"frac_edges={len(petersen_report.lp_dynamic_cut_stall.fractional_edges)}"
    )
    print(
        f"  - P_10 Branch-and-Cut: status={petersen_report.p10_branch_and_cut_metrics.status.value}, "
        f"nodes={petersen_report.p10_branch_and_cut_metrics.nodes_evaluated}, "
        f"cuts={petersen_report.p10_branch_and_cut_metrics.cuts_added}, "
        f"time={petersen_report.p10_branch_and_cut_metrics.elapsed_ms:.2f} ms"
    )
    print(
        f"  - K_10 petersenSepCost (B=0): status={petersen_report.k10_sep_budget_zero_metrics.status.value}, "
        f"root_LP={petersen_report.k10_sep_budget_zero_metrics.root_lp_bound:.4f}, "
        f"nodes={petersen_report.k10_sep_budget_zero_metrics.nodes_evaluated}, "
        f"cuts={petersen_report.k10_sep_budget_zero_metrics.cuts_added}, "
        f"time={petersen_report.k10_sep_budget_zero_metrics.elapsed_ms:.2f} ms"
    )
    print(
        f"  - K_10 petersenSepCost (B=1): status={petersen_report.k10_sep_budget_one_metrics.status.value}, "
        f"root_LP={petersen_report.k10_sep_budget_one_metrics.root_lp_bound:.4f}, "
        f"best_cost={petersen_report.k10_sep_budget_one_metrics.best_cost}, "
        f"nodes={petersen_report.k10_sep_budget_one_metrics.nodes_evaluated}, "
        f"cuts={petersen_report.k10_sep_budget_one_metrics.cuts_added}, "
        f"time={petersen_report.k10_sep_budget_one_metrics.elapsed_ms:.2f} ms"
    )

    # Part 2: Ring-of-Triangles 3-SAT Gadget Suite (UNSAT, UNIQUE-SAT, and Rank-1 Control)
    print("\n[2/4] Running Ring-of-Triangles 3-SAT Gadget Graph (G_path) Suite (m=3..9)...")
    unsat_results: list[BenchmarkMetrics] = []
    sat_results: list[BenchmarkMetrics] = []
    rank_one_results: list[BenchmarkMetrics] = []

    m_values = [3, 4, 5, 6, 7, 8, 9]
    for m in m_values:
        # 2a. UNSAT 3-SAT Gadget
        g_unsat = build_unsat_ring_of_triangles(m)
        m_unsat, _ = run_benchmark(
            instance_name=f"G_path_3SAT_UNSAT_m{m}_V{3*m}",
            graph=g_unsat.graph,
            cost_fn=g_unsat.cost_fn,
            budget=g_unsat.budget,
            extra_inequalities=g_unsat.clause_inequalities,
            preferred_branch_edges=g_unsat.true_bridges,
        )
        unsat_results.append(m_unsat)

        # 2b. UNIQUE-SAT 3-SAT Gadget
        g_sat = build_unique_sat_ring_of_triangles(m)
        m_sat, _ = run_benchmark(
            instance_name=f"G_path_3SAT_UNIQ_SAT_m{m}_V{3*m}",
            graph=g_sat.graph,
            cost_fn=g_sat.cost_fn,
            budget=g_sat.budget,
            extra_inequalities=g_sat.clause_inequalities,
            preferred_branch_edges=g_sat.true_bridges,
        )
        sat_results.append(m_sat)

        # 2c. Bounded Cycle-Separation Rank (kappa = 1) Control
        g_r1, c_r1, b_r1, ineq_r1 = build_rank_one_necklace(m)
        m_r1, _ = run_benchmark(
            instance_name=f"Necklace_Rank1_m{m}_V{3*m}",
            graph=g_r1,
            cost_fn=c_r1,
            budget=b_r1,
            extra_inequalities=ineq_r1,
            preferred_branch_edges=g_unsat.true_bridges,
        )
        rank_one_results.append(m_r1)

        print(
            f"  m={m} (|V|={3*m:2d}) | "
            f"UNSAT: nodes={m_unsat.nodes_evaluated:4d} (2^m-1={2**m-1:4d}), cuts={m_unsat.cuts_added:2d}, "
            f"LP_solves={m_unsat.lp_solves:4d}, status={m_unsat.status.value:8s}, time={m_unsat.elapsed_ms:7.2f} ms | "
            f"UNIQ-SAT: nodes={m_sat.nodes_evaluated:4d}, status={m_sat.status.value:8s}, time={m_sat.elapsed_ms:7.2f} ms | "
            f"Rank-1: nodes={m_r1.nodes_evaluated:2d}, cuts={m_r1.cuts_added:2d}, time={m_r1.elapsed_ms:6.2f} ms"
        )

    # Part 3: Clustered Complete Graphs K_n (Stoer-Wagner vs Edmonds-Karp DFJ Cut Separation)
    print("\n[3/4] Running Complete Graph K_n DFJ Separation Comparison (Stoer-Wagner vs Edmonds-Karp)...")
    kn_results: list[tuple[BenchmarkMetrics, BenchmarkMetrics]] = []
    for n_val in (6, 8, 10, 12):
        g_kn, c_kn, b_kn = build_clustered_complete_graph(n_val)
        sw_m, _ = run_benchmark(
            instance_name=f"Clustered_K{n_val}_StoerWagner",
            graph=g_kn,
            cost_fn=c_kn,
            budget=b_kn,
            separation_method="stoer_wagner",
        )
        ek_m, _ = run_benchmark(
            instance_name=f"Clustered_K{n_val}_EdmondsKarp",
            graph=g_kn,
            cost_fn=c_kn,
            budget=b_kn,
            separation_method="edmonds_karp",
        )
        kn_results.append((sw_m, ek_m))
        print(
            f"  K_{n_val:2d} (|E|={len(g_kn.edges):2d}) | "
            f"Stoer-Wagner: LP={sw_m.root_lp_bound:6.1f}, cuts={sw_m.cuts_added:2d}, "
            f"nodes={sw_m.nodes_evaluated:2d}, cost={sw_m.best_cost}, time={sw_m.elapsed_ms:6.2f} ms | "
            f"Edmonds-Karp: LP={ek_m.root_lp_bound:6.1f}, cuts={ek_m.cuts_added:2d}, "
            f"nodes={ek_m.nodes_evaluated:2d}, cost={ek_m.best_cost}, time={ek_m.elapsed_ms:6.2f} ms"
        )

    # Part 4: Yannakakis DFJ Subtour Slack Matrix & Petersen Slack Profile Suite
    print("\n[4/4] Running Yannakakis DFJ Subtour Slack Matrix & P_10 Cut Slack Profile Suite...")
    slack_results: list[YannakakisSlackMatrixResult] = []
    for n_val in (4, 5, 6, 7):
        s_res = compute_yannakakis_dfj_slack_matrix(n_val)
        slack_results.append(s_res)
        print(
            f"  K_{n_val} Slack Matrix S_DFJ({n_val}) | "
            f"shape=({s_res.num_dfj_cuts:3d} x {s_res.num_tour_vertices:3d}), "
            f"nontrivial_cuts={s_res.num_nontrivial_cuts:3d}, "
            f"min_slack={s_res.min_slack:.1f}, max_slack={s_res.max_slack:.1f}, "
            f"even_int={s_res.all_even_integers}, singletons_zero={s_res.singleton_cuts_all_zero}, "
            f"rank={s_res.linear_rank:2d}, zero_frac={s_res.zero_slack_fraction:.4f}, "
            f"time={s_res.elapsed_ms:.2f} ms"
        )

    p10_profile = compute_petersen_dfj_slack_profile()
    print(
        f"  P_10 DFJ Cut Slack Profile (1022 proper cuts) | "
        f"singletons_zero={p10_profile.singleton_all_zero} "
        f"({p10_profile.singleton_cosingleton_cuts} cuts at slack=0.0000), "
        f"nontrivial_cuts={p10_profile.nontrivial_cuts} "
        f"(min_nontrivial_slack={p10_profile.min_nontrivial_slack:.4f}, "
        f"max_slack={p10_profile.max_slack_all:.4f}), "
        f"cut_edge_hist={p10_profile.cut_edge_cardinality_histogram}"
    )

    return {
        "petersen": petersen_report,
        "unsat_results": unsat_results,
        "sat_results": sat_results,
        "rank_one_results": rank_one_results,
        "kn_results": kn_results,
        "slack_results": slack_results,
        "p10_slack_profile": p10_profile,
    }


if __name__ == "__main__":
    run_all_benchmarks()

