"""Executable Reference Engine for the Held-Karp LP Relaxation & Certified Branch-and-Cut State Machine.

Corresponds directly to the formal Lean 4 specifications in `OAI.TSP` (`TSPComplexity.lean`):
  - `Graph`, `CostFunction`, `cycleEdges`, `tourCost`, `IsTour`, `ValidTourBound`
  - `HeldKarpPoint`, `DegreeConservation`, `SubtourCutConstraint`, `cutCapacity`
  - `DFJCut`, `dfjSlack`, `HasAffineLift`
  - `SearchStatus`, `SolverState`, `step`, `run`
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from enum import Enum
import itertools
import math
import time
from typing import Callable, Iterable, Literal, Sequence

import networkx as nx
import numpy as np
from scipy.optimize import linprog

Edge = tuple[int, int]


def canonical_edge(u: int, v: int) -> Edge:
    """Return the canonical undirected edge representation (min(u, v), max(u, v))."""
    if u == v:
        raise ValueError(f"Self-loops are forbidden in simple undirected graphs: ({u}, {v})")
    return (u, v) if u < v else (v, u)


@dataclass(frozen=True)
class Graph:
    """Simple undirected loopless finite graph on vertex set `Fin n = {0, ..., n - 1}`.

    Matches `OAI.TSP.Graph n` in `TSPComplexity.lean`.
    """

    n: int
    edges: tuple[Edge, ...]
    adj: dict[int, frozenset[int]] = field(init=False, repr=False)
    edge_index: dict[Edge, int] = field(init=False, repr=False)

    def __post_init__(self) -> None:
        canonical_set: set[Edge] = set()
        adj_builder: dict[int, set[int]] = {v: set() for v in range(self.n)}
        for u, v in self.edges:
            if not (0 <= u < self.n and 0 <= v < self.n):
                raise ValueError(f"Edge ({u}, {v}) out of range for Fin({self.n})")
            if u == v:
                raise ValueError(f"Graph must be loopless, found self-loop at {u}")
            e = canonical_edge(u, v)
            canonical_set.add(e)
            adj_builder[u].add(v)
            adj_builder[v].add(u)
        sorted_edges = tuple(sorted(canonical_set))
        object.__setattr__(self, "edges", sorted_edges)
        object.__setattr__(
            self, "adj", {v: frozenset( sorted(adj_builder[v]) ) for v in range(self.n)}
        )
        object.__setattr__(
            self, "edge_index", {e: idx for idx, e in enumerate(sorted_edges)}
        )

    def has_edge(self, u: int, v: int) -> bool:
        """Check adjacency `G.adj u v`."""
        if u == v or not (0 <= u < self.n and 0 <= v < self.n):
            return False
        return v in self.adj[u]

    def incident_edges(self, v: int) -> list[Edge]:
        """Return all canonical edges incident to vertex `v`."""
        return [canonical_edge(v, u) for u in self.adj[v]]

    @staticmethod
    def complete(n: int) -> Graph:
        """Construct the complete graph K_n."""
        return Graph(
            n=n,
            edges=tuple((u, v) for u in range(n) for v in range(u + 1, n)),
        )


CostMatrix = np.ndarray
CostFunction = Callable[[int, int], float]


def cycle_edges(p: Sequence[int]) -> list[ tuple[int, int] ]:
    """Ordered sequence of cycle edges formed by adjacent elements in a circular list.

    Matches `OAI.TSP.cycleEdges` in `TSPComplexity.lean`.
    """
    if not p:
        return []
    m = len(p)
    return [(p[i], p[(i + 1) % m]) for i in range(m)]


def tour_cost(cost_fn: CostFunction, p: Sequence[int]) -> float:
    """Total traversal cost of the cycle edge sequence.

    Matches `OAI.TSP.tourCost` in `TSPComplexity.lean`.
    """
    return float(sum(cost_fn(u, v) for u, v in cycle_edges(p)))


def is_tour(graph: Graph, p: Sequence[int]) -> bool:
    """Verify whether `p` is a valid Hamiltonian tour on `graph`.

    Matches `OAI.TSP.IsTour` in `TSPComplexity.lean`:
      `p.length = n ∧ p.Nodup ∧ (∀ e ∈ cycleEdges p, G.adj e.1 e.2)`
    """
    if len(p) != graph.n:
        return False
    if len(set(p)) != graph.n:
        return False
    if any(not (0 <= v < graph.n) for v in p):
        return False
    return all(graph.has_edge(u, v) for u, v in cycle_edges(p))


def valid_tour_bound(
    graph: Graph, cost_fn: CostFunction, budget: float, p: Sequence[int], tol: float = 1e-6
) -> bool:
    """Decision TSP witness predicate: `IsTour G p ∧ tourCost c p ≤ B`."""
    return is_tour(graph, p) and tour_cost(cost_fn, p) <= budget + tol


# ---------------------------------------------------------------------------
# Min-Cut Separation Oracles for DFJ Subtour Elimination
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CutSeparationResult:
    """Result of running a minimum-cut separation oracle on fractional edge weights."""

    min_cut_capacity: float
    partition_s: frozenset[int]
    partition_complement: frozenset[int]
    violated_cuts: tuple[frozenset[int], ...]
    method: str


def _connected_components_cuts(
    n: int, x_edges: dict[Edge, float], eps: float = 1e-7
) -> list[frozenset[int]]:
    """Find connected components of the positive support graph `{e : x_e > eps}`."""
    adj: dict[int, list[int]] = {v: [] for v in range(n)}
    for (u, v), val in x_edges.items():
        if val > eps:
            adj[u].append(v)
            adj[v].append(u)

    visited: set[int] = set()
    components: list[frozenset[int]] = []
    for start in range(n):
        if start in visited:
            continue
        comp: set[int] = set()
        queue: deque[int] = deque([start])
        visited.add(start)
        while queue:
            curr = queue.popleft()
            comp.add(curr)
            for nxt in adj[curr]:
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        components.append(frozenset(comp))
    return components


def stoer_wagner_min_cut(
    n: int, x_edges: dict[Edge, float]
) -> tuple[float, frozenset[int], frozenset[int]]:
    r"""Global minimum cut using the deterministic Stoer-Wagner algorithm ($O(|V|^3)$).

    Finds a non-empty proper subset $S \subsetneq V$ minimizing $x(\delta(S))$.
    """
    if n < 2:
        raise ValueError("Stoer-Wagner requires at least 2 vertices")

    weights = np.zeros((n, n), dtype=float)
    for (u, v), val in x_edges.items():
        if val > 0.0:
            weights[u, v] += val
            weights[v, u] += val

    active = [True] * n
    merged_groups: list[set[int]] = [{i} for i in range(n)]
    best_cut_val = math.inf
    best_group: set[int] = {0}

    for phase in range(n - 1):
        in_a = [False] * n
        key = [0.0] * n
        prev_v = -1
        last_v = -1

        remaining_count = n - phase
        for _ in range(remaining_count):
            # Pick active vertex not in A with maximum key
            max_k = -1.0
            sel = -1
            for v in range(n):
                if active[v] and not in_a[v] and key[v] > max_k:
                    max_k = key[v]
                    sel = v
            in_a[sel] = True
            prev_v = last_v
            last_v = sel
            for v in range(n):
                if active[v] and not in_a[v]:
                    key[v] += weights[sel, v]

        # Cut of the phase separates `last_v` from the rest of the graph
        if key[last_v] < best_cut_val:
            best_cut_val = float(key[last_v])
            best_group = set(merged_groups[last_v])

        # Contract `last_v` into `prev_v`
        active[last_v] = False
        merged_groups[prev_v].update(merged_groups[last_v])
        for v in range(n):
            if active[v] and v != prev_v:
                weights[prev_v, v] += weights[last_v, v]
                weights[v, prev_v] = weights[prev_v, v]

    s_set = frozenset(best_group)
    comp_set = frozenset(set(range(n)) - best_group)
    return best_cut_val, s_set, comp_set


def edmonds_karp_min_st_cut(
    n: int, x_edges: dict[Edge, float], source: int, sink: int, eps: float = 1e-9
) -> tuple[float, frozenset[int]]:
    """Compute minimum $s$-$t$ cut using the Edmonds-Karp ($O(|V| |E|^2)$) max-flow algorithm."""
    capacity = np.zeros((n, n), dtype=float)
    adj: list[list[int]] = [[] for _ in range(n)]
    for (u, v), val in x_edges.items():
        if val > eps:
            capacity[u, v] += val
            capacity[v, u] += val
            adj[u].append(v)
            adj[v].append(u)

    flow = np.zeros((n, n), dtype=float)
    total_flow = 0.0

    while True:
        parent = [-1] * n
        parent[source] = source
        path_cap = [0.0] * n
        path_cap[source] = math.inf
        queue: deque[int] = deque([source])

        while queue and parent[sink] == -1:
            u = queue.popleft()
            for v in adj[u]:
                residual = capacity[u, v] - flow[u, v]
                if parent[v] == -1 and residual > eps:
                    parent[v] = u
                    path_cap[v] = min(path_cap[u], residual)
                    if v == sink:
                        break
                    queue.append(v)

        if parent[sink] == -1:
            break

        push = path_cap[sink]
        total_flow += push
        curr = sink
        while curr != source:
            prev = parent[curr]
            flow[prev, curr] += push
            flow[curr, prev] -= push
            curr = prev

    # Reachable vertices in residual graph form the source side S of the min s-t cut
    visited = {source}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in range(n):
            if v not in visited and (capacity[u, v] - flow[u, v]) > eps:
                visited.add(v)
                queue.append(v)

    return float(total_flow), frozenset(visited)


def separate_dfj_subtour_cuts(
    n: int,
    x_edges: dict[Edge, float],
    method: Literal["stoer_wagner", "edmonds_karp"] = "stoer_wagner",
    violation_tol: float = 1e-5,
) -> CutSeparationResult:
    r"""Dynamic separation oracle for Dantzig-Fulkerson-Johnson (DFJ) subtour constraints.

    Identifies non-empty proper subsets $S \subsetneq V$ violating:
        $$x(\delta(S)) = \sum_{u \in S, v \notin S} x_{uv} \ge 2.$$
    """
    all_vertices = frozenset(range(n))

    # Fast check: disconnected support components have cut capacity 0 < 2
    components = _connected_components_cuts(n, x_edges)
    if len(components) > 1:
        violated: list[frozenset[int]] = []
        seen: set[frozenset[int]] = set()
        for comp in components:
            canon = comp if len(comp) <= n // 2 else all_vertices - comp
            if 0 < len(canon) < n and canon not in seen:
                seen.add(canon)
                violated.append(canon)
        first = violated[0]
        return CutSeparationResult(
            min_cut_capacity=0.0,
            partition_s=first,
            partition_complement=all_vertices - first,
            violated_cuts=tuple(violated),
            method=f"{method}+components",
        )

    if method == "stoer_wagner":
        min_cap, s_set, comp_set = stoer_wagner_min_cut(n, x_edges)
        violated_list: list[frozenset[int]] = []
        if min_cap < 2.0 - violation_tol:
            canon = s_set if len(s_set) <= n // 2 else comp_set
            violated_list.append(canon)
            # Also collect additional violated cuts via s-t cuts to accelerate cutting planes
            seen_cuts = {canon, all_vertices - canon}
            for sink in range(1, n):
                cap_st, s_st = edmonds_karp_min_st_cut(n, x_edges, 0, sink)
                if cap_st < 2.0 - violation_tol:
                    c_st = s_st if len(s_st) <= n // 2 else all_vertices - s_st
                    if c_st not in seen_cuts and 1 < len(c_st) < n - 1:
                        seen_cuts.add(c_st)
                        seen_cuts.add(all_vertices - c_st)
                        violated_list.append(c_st)
        return CutSeparationResult(
            min_cut_capacity=min_cap,
            partition_s=s_set,
            partition_complement=comp_set,
            violated_cuts=tuple(violated_list),
            method="stoer_wagner",
        )

    # Edmonds-Karp separation from root vertex 0 to all sinks t in {1, ..., n - 1}
    min_cap = math.inf
    best_s = frozenset({0})
    violated_list = []
    seen_cuts: set[frozenset[int]] = set()

    for sink in range(1, n):
        cap_st, s_st = edmonds_karp_min_st_cut(n, x_edges, 0, sink)
        if cap_st < min_cap:
            min_cap = cap_st
            best_s = s_st
        if cap_st < 2.0 - violation_tol:
            canon = s_st if len(s_st) <= n // 2 else all_vertices - s_st
            if canon not in seen_cuts and 0 < len(canon) < n:
                seen_cuts.add(canon)
                seen_cuts.add(all_vertices - canon)
                violated_list.append(canon)

    return CutSeparationResult(
        min_cut_capacity=min_cap,
        partition_s=best_s,
        partition_complement=all_vertices - best_s,
        violated_cuts=tuple(violated_list),
        method="edmonds_karp",
    )


# ---------------------------------------------------------------------------
# Held-Karp Polyhedral Verification & Continuous LP Relaxation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HeldKarpVerification:
    """Verification report corresponding to `OAI.TSP.HeldKarpPoint n` in `TSPComplexity.lean`."""

    is_valid: bool
    symmetric: bool
    loopless: bool
    nonneg: bool
    unit_le: bool
    degree_conservation: bool
    subtour_cut_constraint: bool
    max_degree_error: float
    min_cut_capacity: float
    min_cut_subset: frozenset[int]


def verify_held_karp_point(
    n: int, x_matrix: np.ndarray, tol: float = 1e-6
) -> HeldKarpVerification:
    """Verify whether an $n \\times n$ matrix $x$ satisfies all axioms of `HeldKarpPoint n`."""
    sym_err = float(np.max(np.abs(x_matrix - x_matrix.T)))
    symmetric = sym_err <= tol
    diag_err = float(np.max(np.abs(np.diag(x_matrix))))
    loopless = diag_err <= tol
    nonneg = bool(np.all(x_matrix >= -tol))
    unit_le = bool(np.all(x_matrix <= 1.0 + tol))

    deg_sums = np.sum(x_matrix, axis=1) - np.diag(x_matrix)
    max_deg_err = float(np.max(np.abs(deg_sums - 2.0)))
    degree_conservation = max_deg_err <= tol

    x_edges: dict[Edge, float] = {}
    for u in range(n):
        for v in range(u + 1, n):
            x_edges[(u, v)] = float(0.5 * (x_matrix[u, v] + x_matrix[v, u]))

    sep = separate_dfj_subtour_cuts(n, x_edges, method="stoer_wagner", violation_tol=tol)
    subtour_ok = sep.min_cut_capacity >= 2.0 - tol

    is_valid = (
        symmetric
        and loopless
        and nonneg
        and unit_le
        and degree_conservation
        and subtour_ok
    )
    return HeldKarpVerification(
        is_valid=is_valid,
        symmetric=symmetric,
        loopless=loopless,
        nonneg=nonneg,
        unit_le=unit_le,
        degree_conservation=degree_conservation,
        subtour_cut_constraint=subtour_ok,
        max_degree_error=max_deg_err,
        min_cut_capacity=sep.min_cut_capacity,
        min_cut_subset=sep.partition_s,
    )


@dataclass(frozen=True)
class LinearInequality:
    """Additional linear inequality $\\sum_{e \\in \\text{edges}} w_e x_e \\le \\text{rhs}$."""

    coeffs: dict[Edge, float]
    rhs: float
    label: str = ""


@dataclass(frozen=True)
class LPRelaxationResult:
    """Result of solving the Held-Karp LP relaxation (with dynamic DFJ cut generation)."""

    feasible: bool
    objective: float
    x_edges: dict[Edge, float]
    min_cut_capacity: float
    cuts_added: int
    lp_rounds: int
    is_integral: bool
    extracted_tour: list[int] | None
    fractional_edges: tuple[ tuple[Edge, float], ... ]


def _extract_tour_from_integral_edges(
    n: int, x_edges: dict[Edge, float], tol: float = 1e-4
) -> list[int] | None:
    """If `x_edges` is an integral single Hamiltonian cycle, return the vertex order `[0, ...]`."""
    adj: dict[int, list[int]] = {v: [] for v in range(n)}
    for (u, v), val in x_edges.items():
        if abs(val - 1.0) <= tol:
            adj[u].append(v)
            adj[v].append(u)
        elif val > tol:
            return None

    if any(len(adj[v]) != 2 for v in range(n)):
        return None

    tour = [0]
    visited = {0}
    curr = 0
    prev = -1
    for _ in range(n - 1):
        u1, u2 = adj[curr]
        nxt = u1 if u1 != prev else u2
        if nxt in visited:
            return None
        visited.add(nxt)
        tour.append(nxt)
        prev, curr = curr, nxt

    # Check cycle closure back to 0
    if 0 not in adj[curr]:
        return None
    return tour


def solve_held_karp_lp(
    graph: Graph,
    cost_fn: CostFunction,
    cuts_pool: list[frozenset[int]] | None = None,
    fixed_ones: Iterable[Edge] = (),
    fixed_zeros: Iterable[Edge] = (),
    extra_inequalities: Sequence[LinearInequality] = (),
    edge_upper_bound: float = 1.0,
    separation_method: Literal["stoer_wagner", "edmonds_karp"] = "stoer_wagner",
    max_cut_rounds: int = 50,
    tol: float = 1e-5,
) -> LPRelaxationResult:
    """Solve the continuous Held-Karp LP relaxation using `scipy.optimize.linprog` and dynamic DFJ cuts.

    Formulation:
        min  sum_{e in E} c_e x_e
        s.t. sum_{e in delta(v)} x_e = 2          for all v in V
             sum_{e in delta(S)} x_e >= 2         for all dynamically separated S
             0 <= x_e <= edge_upper_bound         (with fixed_ones / fixed_zeros overrides)
    """
    n = graph.n
    edges = graph.edges
    num_edges = len(edges)
    edge_idx = graph.edge_index

    if num_edges < n:
        return LPRelaxationResult(
            feasible=False,
            objective=math.inf,
            x_edges={},
            min_cut_capacity=0.0,
            cuts_added=0,
            lp_rounds=0,
            is_integral=False,
            extracted_tour=None,
            fractional_edges=(),
        )

    c_vec = np.array([cost_fn(u, v) for u, v in edges], dtype=float)

    # Degree-2 equality constraints: A_eq @ x == 2
    a_eq = np.zeros((n, num_edges), dtype=float)
    for e_i, (u, v) in enumerate(edges):
        a_eq[u, e_i] = 1.0
        a_eq[v, e_i] = 1.0
    b_eq = np.full(n, 2.0, dtype=float)

    # Variable bounds
    ones_set = {canonical_edge(u, v) for u, v in fixed_ones}
    zeros_set = {canonical_edge(u, v) for u, v in fixed_zeros}
    if ones_set & zeros_set:
        return LPRelaxationResult(
            feasible=False,
            objective=math.inf,
            x_edges={},
            min_cut_capacity=0.0,
            cuts_added=0,
            lp_rounds=0,
            is_integral=False,
            extracted_tour=None,
            fractional_edges=(),
        )

    bounds: list[tuple[float, float]] = []
    for e in edges:
        if e in ones_set:
            bounds.append((1.0, 1.0))
        elif e in zeros_set:
            bounds.append((0.0, 0.0))
        else:
            bounds.append((0.0, float(edge_upper_bound)))

    active_cuts: list[frozenset[int]] = list(cuts_pool) if cuts_pool is not None else []
    known_cuts: set[frozenset[int]] = set(active_cuts)

    def _cut_row(subset_s: frozenset[int]) -> np.ndarray:
        row = np.zeros(num_edges, dtype=float)
        for e_i, (u, v) in enumerate(edges):
            if (u in subset_s) ^ (v in subset_s):
                row[e_i] = -1.0  # -sum_{e in delta(S)} x_e <= -2.0
        return row

    a_ub_rows: list[np.ndarray] = [_cut_row(s) for s in active_cuts]
    b_ub_vals: list[float] = [-2.0 for _ in active_cuts]

    for ineq in extra_inequalities:
        row = np.zeros(num_edges, dtype=float)
        for e_raw, coeff in ineq.coeffs.items():
            e = canonical_edge(*e_raw)
            if e in edge_idx:
                row[edge_idx[e]] = float(coeff)
        a_ub_rows.append(row)
        b_ub_vals.append(float(ineq.rhs))

    cuts_added = 0
    lp_rounds = 0
    last_x_edges: dict[Edge, float] = {}
    last_obj = math.inf
    last_min_cut = 0.0

    for _ in range(max_cut_rounds):
        lp_rounds += 1
        a_ub = np.vstack(a_ub_rows) if a_ub_rows else None
        b_ub = np.array(b_ub_vals, dtype=float) if b_ub_vals else None

        res = linprog(
            c=c_vec,
            A_ub=a_ub,
            b_ub=b_ub,
            A_eq=a_eq,
            b_eq=b_eq,
            bounds=bounds,
            method="highs",
        )

        if not res.success or res.x is None:
            return LPRelaxationResult(
                feasible=False,
                objective=math.inf,
                x_edges={},
                min_cut_capacity=0.0,
                cuts_added=cuts_added,
                lp_rounds=lp_rounds,
                is_integral=False,
                extracted_tour=None,
                fractional_edges=(),
            )

        x_sol = res.x
        last_obj = float(res.fun)
        last_x_edges = {edges[i]: float(x_sol[i]) for i in range(num_edges)}

        sep = separate_dfj_subtour_cuts(
            n=n,
            x_edges=last_x_edges,
            method=separation_method,
            violation_tol=tol,
        )
        last_min_cut = sep.min_cut_capacity

        new_cuts = [s for s in sep.violated_cuts if s not in known_cuts]
        if not new_cuts:
            break

        for s in new_cuts:
            known_cuts.add(s)
            active_cuts.append(s)
            if cuts_pool is not None:
                cuts_pool.append(s)
            a_ub_rows.append(_cut_row(s))
            b_ub_vals.append(-2.0)
            cuts_added += 1

    # Inspect integrality and fractional edges
    frac_list: list[tuple[Edge, float]] = []
    for e, val in last_x_edges.items():
        if tol < val < 1.0 - tol:
            frac_list.append((e, val))

    is_integral = len(frac_list) == 0 and last_min_cut >= 2.0 - tol
    extracted_tour = (
        _extract_tour_from_integral_edges(n, last_x_edges, tol=1e-3)
        if is_integral
        else None
    )
    if extracted_tour is not None:
        # Check extra inequalities on the integral solution
        for ineq in extra_inequalities:
            lhs = sum(
                coeff * last_x_edges.get(canonical_edge(*e_raw), 0.0)
                for e_raw, coeff in ineq.coeffs.items()
            )
            if lhs > ineq.rhs + tol:
                extracted_tour = None
                is_integral = False
                break

    return LPRelaxationResult(
        feasible=True,
        objective=last_obj,
        x_edges=last_x_edges,
        min_cut_capacity=last_min_cut,
        cuts_added=cuts_added,
        lp_rounds=lp_rounds,
        is_integral=extracted_tour is not None,
        extracted_tour=extracted_tour,
        fractional_edges=tuple(frac_list),
    )


# ---------------------------------------------------------------------------
# Certified Branch-and-Cut State Machine (`SolverState`, `step`, `run`)
# ---------------------------------------------------------------------------


class SearchStatusKind(str, Enum):
    """Matches `OAI.TSP.SearchStatus` constructors in `TSPComplexity.lean`."""

    SEARCHING = "searching"
    ACCEPTED = "accepted"
    REJECTED = "rejected"


@dataclass(frozen=True)
class SearchStatus:
    """Tagged status corresponding to `OAI.TSP.SearchStatus n`."""

    kind: SearchStatusKind
    witness: list[int] | None = None

    @staticmethod
    def searching() -> SearchStatus:
        return SearchStatus(SearchStatusKind.SEARCHING, None)

    @staticmethod
    def accepted(witness: Sequence[int]) -> SearchStatus:
        return SearchStatus(SearchStatusKind.ACCEPTED, list(witness))

    @staticmethod
    def rejected() -> SearchStatus:
        return SearchStatus(SearchStatusKind.REJECTED, None)


@dataclass(frozen=True)
class BranchNode:
    """A node in the branch-and-cut frontier queue."""

    fixed_ones: frozenset[Edge] = frozenset()
    fixed_zeros: frozenset[Edge] = frozenset()
    depth: int = 0
    lower_bound: float = 0.0
    candidate_tour: tuple[int, ...] | None = None


@dataclass
class SolverState:
    """Certified Branch-and-Cut state configuration.

    Directly mirrors `OAI.TSP.SolverState n` in `TSPComplexity.lean`:
      - `status : SearchStatus n`
      - `queue : List (BranchNode)`
      - `bestCost : Option float`
      - `bestTour : Option (List int)`
      - `steps : Nat`
    Along with instrumentation counters for empirical benchmarking.
    """

    n: int
    status: SearchStatus = field(default_factory=SearchStatus.searching)
    queue: list[BranchNode] = field(default_factory=list)
    best_cost: float | None = None
    best_tour: list[int] | None = None
    steps: int = 0
    cuts_pool: list[frozenset[int]] = field(default_factory=list)
    total_cuts_added: int = 0
    total_lp_solves: int = 0
    nodes_evaluated: int = 0
    pruned_by_bound: int = 0
    pruned_infeasible: int = 0
    root_lp_bound: float | None = None
    root_min_cut: float | None = None
    root_fractional_edges: tuple[tuple[Edge, float], ...] = ()

    @staticmethod
    def init(n: int) -> SolverState:
        """Initialize the solver state with the root branch node `[BranchNode()]`.

        Matches `OAI.TSP.SolverState.init` in `TSPComplexity.lean`.
        """
        return SolverState(
            n=n,
            status=SearchStatus.searching(),
            queue=[BranchNode()],
            best_cost=None,
            best_tour=None,
            steps=0,
        )


def _select_branching_edge(
    fractional_edges: Sequence[tuple[Edge, float]],
    preferred_edges: Sequence[Edge] = (),
    fixed_ones: frozenset[Edge] = frozenset(),
    fixed_zeros: frozenset[Edge] = frozenset(),
) -> Edge:
    """Select an undecided edge $e^*$ to branch on ($x_{e^*} = 1$ vs $x_{e^*} = 0$)."""
    decided = fixed_ones | fixed_zeros
    for pref in preferred_edges:
        e = canonical_edge(*pref)
        if e not in decided:
            return e
    frac_map = dict(fractional_edges)
    for e, _ in fractional_edges:
        if e not in decided:
            return min(
                (item for item in fractional_edges if item[0] not in decided),
                key=lambda item: (abs(item[1] - 0.5), item[0]),
            )[0]
    return fractional_edges[0][0]


def step(
    graph: Graph,
    cost_fn: CostFunction,
    budget: float,
    state: SolverState,
    extra_inequalities: Sequence[LinearInequality] = (),
    preferred_branch_edges: Sequence[Edge] = (),
    separation_method: Literal["stoer_wagner", "edmonds_karp"] = "stoer_wagner",
    max_cut_rounds_root: int = 50,
    max_cut_rounds_tree: int = 10,
    tol: float = 1e-5,
) -> SolverState:
    """Single transition step of the certified Branch-and-Cut solver.

    Directly mirrors `OAI.TSP.step` in `TSPComplexity.lean`:
      - Terminal states (`accepted`, `rejected`) are fixed points (`run_accepted_stable`, `run_rejected_stable`).
      - An empty queue (`queue = []`) transitions immediately to `accepted` (if `best_tour` exists)
        or `rejected` (`step_queue_nil_halts`).
      - A non-empty queue (`node :: rest`) pops `node` (`step_queue_pop`), evaluates the Held-Karp LP
        relaxation with dynamic DFJ cuts, and either accepts an integral tour within budget `B`
        (`step_accepted_soundness`), prunes the branch if infeasible / bound > B, or branches on a
        fractional edge.
    """
    if state.status.kind in (SearchStatusKind.ACCEPTED, SearchStatusKind.REJECTED):
        return state

    if not state.queue:
        if state.best_tour is not None:
            state.status = SearchStatus.accepted(state.best_tour)
        else:
            state.status = SearchStatus.rejected()
        state.steps += 1
        return state

    # Pop head node from the frontier queue (DFS/LIFO or FIFO; pop(0) matches `p :: ps` head pop)
    node = state.queue.pop(0)
    state.steps += 1
    state.nodes_evaluated += 1

    # Direct candidate tour check if provided explicitly
    if node.candidate_tour is not None:
        cand = list(node.candidate_tour)
        if valid_tour_bound(graph, cost_fn, budget, cand, tol=tol):
            c_val = tour_cost(cost_fn, cand)
            state.best_cost = c_val
            state.best_tour = cand
            state.status = SearchStatus.accepted(cand)
        return state

    # Prune if a vertex already has > 2 fixed incident edges
    deg_fixed: dict[int, int] = {v: 0 for v in range(graph.n)}
    for u, v in node.fixed_ones:
        deg_fixed[u] += 1
        deg_fixed[v] += 1
        if deg_fixed[u] > 2 or deg_fixed[v] > 2:
            state.pruned_infeasible += 1
            return state

    cut_rounds = max_cut_rounds_root if node.depth == 0 else max_cut_rounds_tree
    lp_res = solve_held_karp_lp(
        graph=graph,
        cost_fn=cost_fn,
        cuts_pool=state.cuts_pool,
        fixed_ones=node.fixed_ones,
        fixed_zeros=node.fixed_zeros,
        extra_inequalities=extra_inequalities,
        separation_method=separation_method,
        max_cut_rounds=cut_rounds,
        tol=tol,
    )
    state.total_cuts_added += lp_res.cuts_added
    state.total_lp_solves += lp_res.lp_rounds

    if node.depth == 0 and state.root_lp_bound is None:
        state.root_lp_bound = lp_res.objective
        state.root_min_cut = lp_res.min_cut_capacity
        state.root_fractional_edges = lp_res.fractional_edges

    if not lp_res.feasible:
        state.pruned_infeasible += 1
        return state

    if lp_res.objective > budget + tol:
        state.pruned_by_bound += 1
        return state

    if lp_res.is_integral and lp_res.extracted_tour is not None:
        tour = lp_res.extracted_tour
        if valid_tour_bound(graph, cost_fn, budget, tour, tol=tol):
            t_cost = tour_cost(cost_fn, tour)
            state.best_cost = t_cost
            state.best_tour = tour
            state.status = SearchStatus.accepted(tour)
            return state

    if not lp_res.fractional_edges:
        # Integral edge values on graph edges, but violates extra inequalities or subtours
        state.pruned_infeasible += 1
        return state

    # Branch on a fractional edge e*: child_1 sets x_{e*} = 1, child_0 sets x_{e*} = 0
    branch_edge = _select_branching_edge(
        lp_res.fractional_edges,
        preferred_branch_edges,
        node.fixed_ones,
        node.fixed_zeros,
    )
    child_one = BranchNode(
        fixed_ones=node.fixed_ones | {branch_edge},
        fixed_zeros=node.fixed_zeros,
        depth=node.depth + 1,
        lower_bound=lp_res.objective,
    )
    child_zero = BranchNode(
        fixed_ones=node.fixed_ones,
        fixed_zeros=node.fixed_zeros | {branch_edge},
        depth=node.depth + 1,
        lower_bound=lp_res.objective,
    )
    # Prepend children to head of queue for depth-first traversal while preserving head-pop semantics
    state.queue = [child_one, child_zero] + state.queue
    return state


def run(
    graph: Graph,
    cost_fn: CostFunction,
    budget: float,
    fuel: int,
    state: SolverState | None = None,
    extra_inequalities: Sequence[LinearInequality] = (),
    preferred_branch_edges: Sequence[Edge] = (),
    separation_method: Literal["stoer_wagner", "edmonds_karp"] = "stoer_wagner",
    max_cut_rounds_root: int = 50,
    max_cut_rounds_tree: int = 10,
    tol: float = 1e-5,
) -> SolverState:
    """Multi-step fuel-bounded execution of the Branch-and-Cut state machine.

    Directly mirrors `OAI.TSP.run` in `TSPComplexity.lean`:
      ```lean
      def run (G : Graph n) (c : CostFunction n) (B : ℕ) (fuel : ℕ) (s : SolverState n) : SolverState n
      ```
    """
    curr = state if state is not None else SolverState.init(graph.n)
    for _ in range(fuel):
        if curr.status.kind != SearchStatusKind.SEARCHING:
            break
        step(
            graph=graph,
            cost_fn=cost_fn,
            budget=budget,
            state=curr,
            extra_inequalities=extra_inequalities,
            preferred_branch_edges=preferred_branch_edges,
            separation_method=separation_method,
            max_cut_rounds_root=max_cut_rounds_root,
            max_cut_rounds_tree=max_cut_rounds_tree,
            tol=tol,
        )
    return curr


@dataclass(frozen=True)
class BenchmarkMetrics:
    """Structured telemetry record for a single Branch-and-Cut benchmark run."""

    instance_name: str
    vertices: int
    edges: int
    budget: float
    status: SearchStatusKind
    root_lp_bound: float
    root_min_cut: float
    cuts_added: int
    lp_solves: int
    nodes_evaluated: int
    steps: int
    pruned_by_bound: int
    pruned_infeasible: int
    best_cost: float | None
    elapsed_ms: float


def run_benchmark(
    instance_name: str,
    graph: Graph,
    cost_fn: CostFunction,
    budget: float,
    fuel: int = 100_000,
    extra_inequalities: Sequence[LinearInequality] = (),
    preferred_branch_edges: Sequence[Edge] = (),
    separation_method: Literal["stoer_wagner", "edmonds_karp"] = "stoer_wagner",
    max_cut_rounds_root: int = 50,
    max_cut_rounds_tree: int = 2,
) -> tuple[BenchmarkMetrics, SolverState]:
    """Execute `run` and collect timing, cut counts, and branch-and-bound node counts."""
    t0 = time.perf_counter()
    final_state = run(
        graph=graph,
        cost_fn=cost_fn,
        budget=budget,
        fuel=fuel,
        extra_inequalities=extra_inequalities,
        preferred_branch_edges=preferred_branch_edges,
        separation_method=separation_method,
        max_cut_rounds_root=max_cut_rounds_root,
        max_cut_rounds_tree=max_cut_rounds_tree,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    metrics = BenchmarkMetrics(
        instance_name=instance_name,
        vertices=graph.n,
        edges=len(graph.edges),
        budget=budget,
        status=final_state.status.kind,
        root_lp_bound=final_state.root_lp_bound if final_state.root_lp_bound is not None else math.nan,
        root_min_cut=final_state.root_min_cut if final_state.root_min_cut is not None else math.nan,
        cuts_added=final_state.total_cuts_added,
        lp_solves=final_state.total_lp_solves,
        nodes_evaluated=final_state.nodes_evaluated,
        steps=final_state.steps,
        pruned_by_bound=final_state.pruned_by_bound,
        pruned_infeasible=final_state.pruned_infeasible,
        best_cost=final_state.best_cost,
        elapsed_ms=elapsed_ms,
    )
    return metrics, final_state


# ---------------------------------------------------------------------------
# Yannakakis DFJ Subtour Slack Matrix & Extension Complexity Diagnostics
# ---------------------------------------------------------------------------


def enumerate_dfj_cuts(n: int) -> list[frozenset[int]]:
    r"""Enumerate all $2^n - 2$ proper non-empty cuts $S \in \text{DFJCut}(n)$ ($1 \le |S| \le n - 1$).

    Directly corresponds to `OAI.TSP.DFJCut n := {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ}`
    in `TSPComplexity.lean`.
    """
    cuts: list[frozenset[int]] = []
    vertices = list(range(n))
    for k in range(1, n):
        for comb in itertools.combinations(vertices, k):
            cuts.append(frozenset(comb))
    return cuts


def enumerate_canonical_tours(n: int) -> list[tuple[int, ...]]:
    r"""Enumerate all $(n-1)! / 2$ distinct undirected Hamiltonian tour cycles on $K_n$ ($n \ge 3$).

    Fixes `p[0] = 0` and breaks reversal symmetry via `p[1] < p[-1]`, producing a 1-to-1
    bijection with the extreme points `tourPoint p` of `OAI.TSP.TSPPolytope n`.
    """
    if n < 3:
        raise ValueError("Hamiltonian tour enumeration requires n >= 3")
    tours: list[tuple[int, ...]] = []
    for perm in itertools.permutations(range(1, n)):
        if perm[0] < perm[-1]:
            tours.append((0, *perm))
    return tours


def tour_point_matrix(n: int, p: Sequence[int]) -> np.ndarray:
    """Construct the symmetric $n \\times n$ incidence matrix `OAI.TSP.tourPoint p`."""
    mat = np.zeros((n, n), dtype=float)
    for u, v in cycle_edges(p):
        mat[u, v] = 1.0
        mat[v, u] = 1.0
    return mat


def cut_capacity(x_matrix: np.ndarray, cut_s: frozenset[int]) -> float:
    r"""Compute `OAI.TSP.cutCapacity x S` $= \sum_{u \in S} \sum_{v \in V \setminus S} x_{uv}$."""
    n = x_matrix.shape[0]
    s_idx = sorted(cut_s)
    comp_idx = [v for v in range(n) if v not in cut_s]
    if not s_idx or not comp_idx:
        return 0.0
    return float(np.sum(x_matrix[np.ix_(s_idx, comp_idx)]))


def dfj_slack(x_matrix: np.ndarray, cut_s: frozenset[int]) -> float:
    """Compute `OAI.TSP.dfjSlack x S := cutCapacity x S.1 - 2`."""
    return cut_capacity(x_matrix, cut_s) - 2.0


@dataclass(frozen=True)
class YannakakisSlackMatrixResult:
    r"""Empirical diagnostics for the Yannakakis DFJ subtour slack matrix $S_{\text{DFJ}}(n)$.

    Rows are indexed by `DFJCut n` ($2^n - 2$ proper non-empty subsets $S \subsetneq V$)
    and columns are indexed by the $(n-1)! / 2$ distinct extreme points `tourPoint p` of
    `TSPPolytope n`, with entries:
        $$S_{\text{DFJ}}[S, p] = \text{dfjSlack}(\text{tourPoint}(p), S) = |\delta(S) \cap E(p)| - 2.$$
    """

    n: int
    num_dfj_cuts: int
    num_nontrivial_cuts: int
    num_tour_vertices: int
    num_permutations: int
    slack_matrix: np.ndarray
    min_slack: float
    max_slack: float
    all_nonneg: bool
    all_even_integers: bool
    singleton_cuts_all_zero: bool
    linear_rank: int
    frobenius_norm: float
    zero_slack_fraction: float
    elapsed_ms: float


def compute_yannakakis_dfj_slack_matrix(n: int) -> YannakakisSlackMatrixResult:
    r"""Construct and analyze the exact Yannakakis DFJ subtour slack matrix $S_{\text{DFJ}}(n)$."""
    if n < 3:
        raise ValueError("Yannakakis DFJ slack matrix requires n >= 3")

    t0 = time.perf_counter()
    cuts = enumerate_dfj_cuts(n)
    tours = enumerate_canonical_tours(n)

    num_cuts = len(cuts)
    num_tours = len(tours)

    # Vectorized construction via boolean indicator masks B (num_cuts x n)
    cut_masks = np.zeros((num_cuts, n), dtype=bool)
    cut_sizes = np.zeros(num_cuts, dtype=int)
    for c_i, s in enumerate(cuts):
        for u in s:
            cut_masks[c_i, u] = True
        cut_sizes[c_i] = len(s)

    slack_mat = np.zeros((num_cuts, num_tours), dtype=float)
    for t_j, p in enumerate(tours):
        p_arr = np.array(p, dtype=int)
        p_next = np.roll(p_arr, -1)
        # Indicator sequence b(i) = (p[i] in S) across all cuts simultaneously
        in_s_curr = cut_masks[:, p_arr]
        in_s_next = cut_masks[:, p_next]
        crossings = np.sum(in_s_curr ^ in_s_next, axis=1).astype(float)
        slack_mat[:, t_j] = crossings - 2.0

    min_slack = float(np.min(slack_mat))
    max_slack = float(np.max(slack_mat))
    all_nonneg = bool(min_slack >= -1e-9)

    rounded = np.rint(slack_mat)
    is_int = bool(np.max(np.abs(slack_mat - rounded)) <= 1e-9)
    is_even = bool(np.all((rounded.astype(int) % 2) == 0))
    all_even_integers = is_int and is_even

    singleton_mask = (cut_sizes == 1) | (cut_sizes == (n - 1))
    singleton_cuts_all_zero = bool(np.max(np.abs(slack_mat[singleton_mask, :])) <= 1e-9)
    num_nontrivial = int(np.sum(~singleton_mask))

    lin_rank = int(np.linalg.matrix_rank(slack_mat))
    frob_norm = float(np.linalg.norm(slack_mat, ord="fro"))
    zero_frac = float(np.mean(np.abs(slack_mat) <= 1e-9))
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    return YannakakisSlackMatrixResult(
        n=n,
        num_dfj_cuts=num_cuts,
        num_nontrivial_cuts=num_nontrivial,
        num_tour_vertices=num_tours,
        num_permutations=math.factorial(n),
        slack_matrix=slack_mat,
        min_slack=min_slack,
        max_slack=max_slack,
        all_nonneg=all_nonneg,
        all_even_integers=all_even_integers,
        singleton_cuts_all_zero=singleton_cuts_all_zero,
        linear_rank=lin_rank,
        frobenius_norm=frob_norm,
        zero_slack_fraction=zero_frac,
        elapsed_ms=elapsed_ms,
    )
