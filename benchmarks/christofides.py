"""
Christofides-Serdyukov Algorithm Benchmark & Verification Engine.
Module: tsp_research.benchmarks.christofides
Topic: Minimum Spanning Trees, Hamiltonian Path Relaxations, and Empirical MST Lower Bound Verification.
Track D: Phase 2 Reference Scaffolding.
"""

from typing import List, Tuple, Set, Dict, Optional
import math
import random
import itertools
import heapq


class UnionFind:
    """Disjoint Set Union (DSU) with path compression and union by rank."""

    def __init__(self, n: int):
        self.parent = list(range(n))
        self.rank = [0] * n

    def find(self, i: int) -> int:
        if self.parent[i] != i:
            self.parent[i] = self.find(self.parent[i])
        return self.parent[i]

    def union(self, i: int, j: int) -> bool:
        root_i = self.find(i)
        root_j = self.find(j)
        if root_i == root_j:
            return False
        if self.rank[root_i] < self.rank[root_j]:
            self.parent[root_i] = root_j
        elif self.rank[root_i] > self.rank[root_j]:
            self.parent[root_j] = root_i
        else:
            self.parent[root_j] = root_i
            self.rank[root_i] += 1
        return True


def kruskal_mst(n: int, dist_matrix: List[List[int]]) -> Tuple[int, List[Tuple[int, int, int]]]:
    """
    Computes the Minimum Spanning Tree using Kruskal's algorithm.
    Returns (mst_cost, list of (u, v, weight) edges in the MST).
    """
    edges: List[Tuple[int, int, int]] = []
    for u in range(n):
        for v in range(u + 1, n):
            edges.append((dist_matrix[u][v], u, v))
    edges.sort()

    dsu = UnionFind(n)
    mst_edges: List[Tuple[int, int, int]] = []
    mst_cost = 0

    for weight, u, v in edges:
        if dsu.union(u, v):
            mst_edges.append((u, v, weight))
            mst_cost += weight
            if len(mst_edges) == n - 1:
                break

    return mst_cost, mst_edges


def prim_mst(n: int, dist_matrix: List[List[int]]) -> Tuple[int, List[Tuple[int, int, int]]]:
    """
    Computes the Minimum Spanning Tree using Prim's algorithm.
    Returns (mst_cost, list of (u, v, weight) edges in the MST).
    """
    if n <= 1:
        return 0, []

    visited = [False] * n
    visited[0] = True
    heap: List[Tuple[int, int, int]] = []
    for v in range(1, n):
        heapq.heappush(heap, (dist_matrix[0][v], 0, v))

    mst_edges: List[Tuple[int, int, int]] = []
    mst_cost = 0

    while heap and len(mst_edges) < n - 1:
        weight, u, v = heapq.heappop(heap)
        if visited[v]:
            continue
        visited[v] = True
        mst_edges.append((u, v, weight))
        mst_cost += weight
        for next_v in range(n):
            if not visited[next_v]:
                heapq.heappush(heap, (dist_matrix[v][next_v], v, next_v))

    return mst_cost, mst_edges


def solve_tsp_exact(n: int, dist_matrix: List[List[int]]) -> Tuple[int, List[int]]:
    """
    Computes the exact optimal Traveling Salesperson tour (OPT) using
    the Held-Karp dynamic programming algorithm (O(n^2 2^n)).
    Returns (opt_cost, optimal_tour_as_list_of_vertices).
    """
    if n < 3:
        raise ValueError("Metric TSP requires n >= 3.")

    # memo[(mask, last)] = (min_cost, prev_vertex)
    memo: Dict[Tuple[int, int], Tuple[int, int]] = {}

    for i in range(1, n):
        memo[(1 << i, i)] = (dist_matrix[0][i], 0)

    for subset_size in range(2, n):
        for subset in itertools.combinations(range(1, n), subset_size):
            mask = 0
            for v in subset:
                mask |= 1 << v
            for v in subset:
                prev_mask = mask & ~(1 << v)
                best_cost = float("inf")
                best_prev = -1
                for u in subset:
                    if u == v:
                        continue
                    cost = memo[(prev_mask, u)][0] + dist_matrix[u][v]
                    if cost < best_cost:
                        best_cost = cost
                        best_prev = u
                memo[(mask, v)] = (best_cost, best_prev)

    full_mask = ((1 << n) - 1) & ~1
    best_cost = float("inf")
    last_vertex = -1
    for v in range(1, n):
        cost = memo[(full_mask, v)][0] + dist_matrix[v][0]
        if cost < best_cost:
            best_cost = cost
            last_vertex = v

    # Reconstruct optimal tour
    tour = [0]
    curr_mask = full_mask
    curr_v = last_vertex
    path = []
    while curr_v != 0:
        path.append(curr_v)
        prev_v = memo[(curr_mask, curr_v)][1]
        curr_mask &= ~(1 << curr_v)
        curr_v = prev_v
    path.reverse()
    tour.extend(path)

    return int(best_cost), tour


def tour_to_spanning_path_cost(n: int, dist_matrix: List[List[int]], tour: List[int]) -> int:
    """
    Computes the cost of dropping the wrap-around cycle edge from a Hamiltonian tour,
    yielding a Hamiltonian spanning path.
    """
    assert len(tour) == n
    path_cost = 0
    for i in range(n - 1):
        path_cost += dist_matrix[tour[i]][tour[i + 1]]
    return path_cost


def generate_random_euclidean_metric(n: int, scale: int = 1000, seed: Optional[int] = None) -> List[List[int]]:
    """
    Generates an integer Euclidean metric space on n 2D points.
    Preserves symmetry, zero diagonal, and triangle inequality.
    """
    if seed is not None:
        random.seed(seed)
    pts = [(random.randint(0, scale), random.randint(0, scale)) for _ in range(n)]
    dist = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                dx = pts[i][0] - pts[j][0]
                dy = pts[i][1] - pts[j][1]
                # Integer ceiling distance satisfies triangle inequality
                dist[i][j] = math.ceil(math.hypot(dx, dy))
    return dist


def generate_ring_metric(n: int, step_cost: int = 10) -> List[List[int]]:
    """
    Generates shortest-path metric on a ring of n vertices.
    """
    dist = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            diff = abs(i - j)
            shortest_steps = min(diff, n - diff)
            dist[i][j] = shortest_steps * step_cost
    return dist


def run_mst_lower_bound_benchmarks() -> bool:
    """
    Executes empirical verification of the MST lower bound (MSTCost <= OPT)
    across diverse metric graph families.
    """
    print("=" * 80)
    print("Track D (Phase 2): Minimum Spanning Tree Lower Bound Verification Suite")
    print("Verifying Landmark Theorem: MSTCost(T_mst) <= SpanningPathCost(p*) <= OPT")
    print("=" * 80)

    test_cases = [
        ("Ring Metric n=4", 4, generate_ring_metric(4, 15)),
        ("Ring Metric n=6", 6, generate_ring_metric(6, 10)),
        ("Ring Metric n=8", 8, generate_ring_metric(8, 20)),
        ("Euclidean 2D n=4 (seed 42)", 4, generate_random_euclidean_metric(4, 1000, 42)),
        ("Euclidean 2D n=6 (seed 101)", 6, generate_random_euclidean_metric(6, 1000, 101)),
        ("Euclidean 2D n=8 (seed 202)", 8, generate_random_euclidean_metric(8, 1000, 202)),
        ("Euclidean 2D n=10 (seed 303)", 10, generate_random_euclidean_metric(10, 1000, 303)),
        ("Euclidean 2D n=11 (seed 404)", 11, generate_random_euclidean_metric(11, 1000, 404)),
        ("Euclidean 2D n=12 (seed 505)", 12, generate_random_euclidean_metric(12, 1000, 505)),
    ]

    all_passed = True

    print(f"{'Instance':<30} | {'n':<3} | {'MST (Kruskal)':<13} | {'MST (Prim)':<10} | {'Path(p*)':<10} | {'OPT':<10} | {'MST/OPT':<8} | {'Status'}")
    print("-" * 105)

    for name, n, dist_mat in test_cases:
        kruskal_cost, _ = kruskal_mst(n, dist_mat)
        prim_cost, _ = prim_mst(n, dist_mat)

        assert kruskal_cost == prim_cost, f"MST cost mismatch for {name}: Kruskal={kruskal_cost}, Prim={prim_cost}"

        opt_cost, opt_tour = solve_tsp_exact(n, dist_mat)
        path_cost = tour_to_spanning_path_cost(n, dist_mat, opt_tour)

        ratio = kruskal_cost / opt_cost if opt_cost > 0 else 1.0

        # Invariant checks:
        # 1. MSTCost <= SpanningPathCost
        # 2. SpanningPathCost <= OPT
        # 3. MSTCost <= OPT
        passed = (kruskal_cost <= path_cost <= opt_cost)
        if not passed:
            all_passed = False

        status = "PASSED [OK]" if passed else "FAILED [VIOLATION]"
        print(f"{name:<30} | {n:<3} | {kruskal_cost:<13} | {prim_cost:<10} | {path_cost:<10} | {opt_cost:<10} | {ratio:.4f}  | {status}")

    print("=" * 105)
    if all_passed:
        print("[SUCCESS] All 9 test suites confirmed the invariant: MSTCost <= SpanningPathCost <= OPT (100% compliance).")
    else:
        print("[FAILURE] Invariant violation detected!")

    return all_passed


def extract_odd_degree_vertices(n: int, mst_edges: List[Tuple[int, int, int]]) -> List[int]:
    """
    Computes vertex degrees from an undirected edge set and extracts the
    subset O of vertices having odd degree.
    By Euler's Handshaking Lemma, |O| must be strictly even.
    Returns a sorted list of odd-degree vertex indices.
    """
    degrees = [0] * n
    for edge in mst_edges:
        u, v = edge[0], edge[1]
        degrees[u] += 1
        degrees[v] += 1
    return [v for v in range(n) if degrees[v] % 2 == 1]


def compute_vertex_degrees(n: int, edges: List[Tuple[int, int, int]]) -> List[int]:
    """Computes vertex degree for every vertex in Fin n."""
    degrees = [0] * n
    for edge in edges:
        u, v = edge[0], edge[1]
        degrees[u] += 1
        degrees[v] += 1
    return degrees


def run_handshaking_parity_benchmarks() -> bool:
    """
    Executes empirical verification of Euler's Handshaking Lemma:
      1. sum(deg(v)) == 2 * |E|
      2. |oddDegreeVertices(E)| is strictly even.
    """
    print("=" * 85)
    print("Track D (Phase 3): Euler's Handshaking Lemma & Degree Parity Verification Suite")
    print("Verifying Invariants: sum(deg(v)) = 2*|E| and |O| is Even (len(O) % 2 == 0)")
    print("=" * 85)

    test_cases = [
        ("Ring Metric n=4", 4, generate_ring_metric(4, 15)),
        ("Ring Metric n=6", 6, generate_ring_metric(6, 10)),
        ("Ring Metric n=8", 8, generate_ring_metric(8, 20)),
        ("Euclidean 2D n=4 (seed 42)", 4, generate_random_euclidean_metric(4, 1000, 42)),
        ("Euclidean 2D n=6 (seed 101)", 6, generate_random_euclidean_metric(6, 1000, 101)),
        ("Euclidean 2D n=8 (seed 202)", 8, generate_random_euclidean_metric(8, 1000, 202)),
        ("Euclidean 2D n=10 (seed 303)", 10, generate_random_euclidean_metric(10, 1000, 303)),
        ("Euclidean 2D n=11 (seed 404)", 11, generate_random_euclidean_metric(11, 1000, 404)),
        ("Euclidean 2D n=12 (seed 505)", 12, generate_random_euclidean_metric(12, 1000, 505)),
    ]

    all_passed = True

    print(f"{'Instance':<30} | {'n':<3} | {'|E|':<4} | {'sum(deg)':<8} | {'2*|E|':<6} | {'|O|':<4} | {'Odd Vertices O':<22} | {'Status'}")
    print("-" * 105)

    for name, n, dist_mat in test_cases:
        _, mst_edges = kruskal_mst(n, dist_mat)
        degrees = compute_vertex_degrees(n, mst_edges)
        sum_deg = sum(degrees)
        two_card = 2 * len(mst_edges)
        odd_vertices = extract_odd_degree_vertices(n, mst_edges)
        card_o = len(odd_vertices)

        # Invariant checks:
        # 1. Handshaking Lemma: sum(deg(v)) == 2 * |E|
        # 2. Spanning Tree edge count: |E| == n - 1
        # 3. Parity Conservation: |O| % 2 == 0
        h_handshaking = (sum_deg == two_card)
        h_edges = (len(mst_edges) == n - 1)
        h_even = (card_o % 2 == 0)

        passed = h_handshaking and h_edges and h_even
        if not passed:
            all_passed = False

        status = "PASSED [OK]" if passed else "FAILED [VIOLATION]"
        odd_str = str(odd_vertices)
        if len(odd_str) > 20:
            odd_str = odd_str[:17] + "..."
        print(f"{name:<30} | {n:<3} | {len(mst_edges):<4} | {sum_deg:<8} | {two_card:<6} | {card_o:<4} | {odd_str:<22} | {status}")

    print("=" * 105)
    if all_passed:
        print("[SUCCESS] All test suites confirmed Euler's Handshaking Lemma & Parity Invariant (100% compliance).")
    else:
        print("[FAILURE] Parity invariant or Handshaking Lemma violation detected!")

    return all_passed


def min_weight_perfect_matching(
    odd_vertices: List[int], dist_matrix: List[List[int]]
) -> Tuple[int, List[Tuple[int, int]]]:
    """
    Computes a minimum-weight perfect matching on the induced metric subgraph of odd-degree vertices.
    Uses NetworkX blossom algorithm (min_weight_matching) with exact recursive branch-and-bound fallback.
    Returns (matching_cost, list of (u, v) matching edges).
    """
    k = len(odd_vertices)
    if k == 0:
        return 0, []
    assert k % 2 == 0, f"Odd degree vertex set must have even cardinality, got {k}"

    try:
        import networkx as nx
        G = nx.Graph()
        for i in range(k):
            u = odd_vertices[i]
            for j in range(i + 1, k):
                v = odd_vertices[j]
                G.add_edge(u, v, weight=dist_matrix[u][v])
        matching = nx.min_weight_matching(G)
        edges = [(u, v) for u, v in matching]
        cost = sum(dist_matrix[u][v] for u, v in edges)
        return cost, edges
    except (ImportError, AttributeError):
        pass

    # Exact branch-and-bound recursive fallback
    def solve(remaining: List[int]) -> Tuple[int, List[Tuple[int, int]]]:
        if not remaining:
            return 0, []
        first = remaining[0]
        best_cost = float("inf")
        best_edges: List[Tuple[int, int]] = []
        for i in range(1, len(remaining)):
            partner = remaining[i]
            rest = [x for j, x in enumerate(remaining) if j != 0 and j != i]
            sub_cost, sub_edges = solve(rest)
            total = dist_matrix[first][partner] + sub_cost
            if total < best_cost:
                best_cost = total
                best_edges = [(first, partner)] + sub_edges
        return int(best_cost), best_edges

    return solve(odd_vertices)


def run_perfect_matching_benchmarks() -> bool:
    """
    Executes empirical verification of Track D Phase 4:
      1. 2 * cost(M) <= OPT (Master Matching Upper Bound)
      2. cost(T) + cost(M) <= 1.5 * OPT (Christofides 3/2-OPT Intermediate Guarantee)
    """
    print("=" * 115)
    print("Track D (Phase 4): Perfect Matchings on Odd Vertices & 1/2-OPT Upper Bound Verification Suite")
    print("Verifying Landmark Invariants: 2 * cost(M) <= OPT and cost(T) + cost(M) <= 1.5 * OPT")
    print("=" * 115)

    test_cases = [
        ("Ring Metric n=4", 4, generate_ring_metric(4, 15)),
        ("Ring Metric n=6", 6, generate_ring_metric(6, 10)),
        ("Ring Metric n=8", 8, generate_ring_metric(8, 20)),
        ("Euclidean 2D n=4 (seed 42)", 4, generate_random_euclidean_metric(4, 1000, 42)),
        ("Euclidean 2D n=6 (seed 101)", 6, generate_random_euclidean_metric(6, 1000, 101)),
        ("Euclidean 2D n=8 (seed 202)", 8, generate_random_euclidean_metric(8, 1000, 202)),
        ("Euclidean 2D n=10 (seed 303)", 10, generate_random_euclidean_metric(10, 1000, 303)),
        ("Euclidean 2D n=11 (seed 404)", 11, generate_random_euclidean_metric(11, 1000, 404)),
        ("Euclidean 2D n=12 (seed 505)", 12, generate_random_euclidean_metric(12, 1000, 505)),
    ]

    all_passed = True

    print(f"{'Instance':<30} | {'n':<3} | {'|O|':<3} | {'c(T)':<6} | {'c(M)':<6} | {'OPT':<6} | {'2*c(M) <= OPT':<15} | {'c(T)+c(M) <= 1.5*OPT':<20} | {'Status'}")
    print("-" * 115)

    for name, n, dist_mat in test_cases:
        mst_cost, mst_edges = kruskal_mst(n, dist_mat)
        odd_vertices = extract_odd_degree_vertices(n, mst_edges)
        matching_cost, matching_edges = min_weight_perfect_matching(odd_vertices, dist_mat)
        opt_cost, _ = solve_tsp_exact(n, dist_mat)

        two_matching = 2 * matching_cost
        tree_plus_matching = mst_cost + matching_cost
        three_half_opt = 1.5 * opt_cost

        # Invariant checks:
        # 1. Matching cardinality: |M| == |O| / 2
        # 2. 2 * cost(M) <= OPT
        # 3. 2 * (cost(T) + cost(M)) <= 3 * OPT
        h_card = (len(matching_edges) == len(odd_vertices) // 2)
        h_matching_half_opt = (two_matching <= opt_cost)
        h_christofides_bound = (2 * tree_plus_matching <= 3 * opt_cost)

        passed = h_card and h_matching_half_opt and h_christofides_bound
        if not passed:
            all_passed = False

        status = "PASSED [OK]" if passed else "FAILED [VIOLATION]"
        m_cond_str = f"{two_matching} <= {opt_cost}"
        c_cond_str = f"{tree_plus_matching} <= {three_half_opt:.1f}"

        print(f"{name:<30} | {n:<3} | {len(odd_vertices):<3} | {mst_cost:<6} | {matching_cost:<6} | {opt_cost:<6} | {m_cond_str:<15} | {c_cond_str:<20} | {status}")

    print("=" * 115)
    if all_passed:
        print("[SUCCESS] All 9 test suites confirmed 2*cost(M) <= OPT and cost(T) + cost(M) <= 1.5*OPT (100% compliance).")
    else:
        print("[FAILURE] Matching upper bound or approximation invariant violation detected!")

    return all_passed


def hierholzer_eulerian_circuit(n: int, edges: List[Tuple[int, int]]) -> List[int]:
    """
    Constructs an Eulerian circuit on the multigraph defined by `edges`
    using Hierholzer's algorithm.
    Every vertex degree must be even and the multigraph connected.
    Returns a closed walk list of vertices starting and ending at the same vertex.
    """
    if not edges:
        return [0]

    # Multigraph adjacency representation: u -> dict of {v: multiplicity}
    adj: Dict[int, Dict[int, int]] = {i: {} for i in range(n)}
    for u, v in edges:
        adj[u][v] = adj[u].get(v, 0) + 1
        adj[v][u] = adj[v].get(u, 0) + 1

    start_node = edges[0][0]
    curr_path = [start_node]
    circuit: List[int] = []

    while curr_path:
        curr_v = curr_path[-1]
        # Look for an unused edge
        next_v = None
        for neighbor in list(adj[curr_v].keys()):
            if adj[curr_v][neighbor] > 0:
                next_v = neighbor
                break

        if next_v is not None:
            adj[curr_v][next_v] -= 1
            adj[next_v][curr_v] -= 1
            curr_path.append(next_v)
        else:
            circuit.append(curr_path.pop())

    circuit.reverse()
    return circuit


def shortcut_circuit(circuit: List[int]) -> List[int]:
    """
    Canonical first-visit metric shortcutting operator.
    Removes duplicate vertex visits from circuit[:-1], preserving first occurrences.
    """
    seen: Set[int] = set()
    tour: List[int] = []
    for v in circuit[:-1]:
        if v not in seen:
            seen.add(v)
            tour.append(v)
    return tour


def compute_walk_cost(dist_matrix: List[List[int]], walk: List[int]) -> int:
    """Computes total traversal cost of a vertex walk."""
    if len(walk) <= 1:
        return 0
    return sum(dist_matrix[walk[i]][walk[i + 1]] for i in range(len(walk) - 1))


def compute_tour_cost(dist_matrix: List[List[int]], tour: List[int]) -> int:
    """Computes the total cyclic cost of a Hamiltonian tour."""
    n = len(tour)
    if n <= 1:
        return 0
    return sum(dist_matrix[tour[i]][tour[(i + 1) % n]] for i in range(n))


def christofides_tsp(n: int, dist_matrix: List[List[int]]) -> Tuple[int, List[int], int, List[int]]:
    """
    End-to-end Christofides-Serdyukov 3/2-approximation algorithm:
      1. T = MST(G)
      2. O = odd-degree vertices of T
      3. M = min-weight perfect matching on O
      4. W = Eulerian circuit on T ∪ M
      5. π = shortcut(W)
    Returns (tour_cost, tour, circuit_cost, circuit).
    """
    mst_cost, mst_edges_weighted = kruskal_mst(n, dist_matrix)
    mst_edges = [(u, v) for u, v, _ in mst_edges_weighted]
    odd_vertices = extract_odd_degree_vertices(n, mst_edges_weighted)
    matching_cost, matching_edges = min_weight_perfect_matching(odd_vertices, dist_matrix)

    # Multigraph union H = T ∪ M
    multigraph_edges = mst_edges + matching_edges
    circuit = hierholzer_eulerian_circuit(n, multigraph_edges)
    circuit_cost = compute_walk_cost(dist_matrix, circuit)

    # Metric shortcutting
    tour = shortcut_circuit(circuit)
    tour_cost = compute_tour_cost(dist_matrix, tour)

    return tour_cost, tour, circuit_cost, circuit


def run_christofides_full_benchmarks() -> bool:
    """
    Executes empirical verification of Track D Phases 5 & 6:
      1. multigraph traversal cost == cost(T) + cost(M)
      2. shortcut tour cost <= circuit walk cost (shortcutting contraction)
      3. shortcut tour cost <= 1.5 * OPT (Master 3/2-Approximation Guarantee)
    """
    print("=" * 125)
    print("Track D (Phases 5 & 6): Eulerian Multigraph Shortcutting & Master 3/2-OPT Approximation Verification Suite")
    print("Verifying Invariants: cost(W) == c(T) + c(M), cost(pi) <= cost(W), and cost(pi) <= 1.5 * OPT")
    print("=" * 125)

    test_cases = [
        ("Ring Metric n=4", 4, generate_ring_metric(4, 15)),
        ("Ring Metric n=6", 6, generate_ring_metric(6, 10)),
        ("Ring Metric n=8", 8, generate_ring_metric(8, 20)),
        ("Euclidean 2D n=4 (seed 42)", 4, generate_random_euclidean_metric(4, 1000, 42)),
        ("Euclidean 2D n=6 (seed 101)", 6, generate_random_euclidean_metric(6, 1000, 101)),
        ("Euclidean 2D n=8 (seed 202)", 8, generate_random_euclidean_metric(8, 1000, 202)),
        ("Euclidean 2D n=10 (seed 303)", 10, generate_random_euclidean_metric(10, 1000, 303)),
        ("Euclidean 2D n=11 (seed 404)", 11, generate_random_euclidean_metric(11, 1000, 404)),
        ("Euclidean 2D n=12 (seed 505)", 12, generate_random_euclidean_metric(12, 1000, 505)),
    ]

    all_passed = True

    print(f"{'Instance':<30} | {'n':<3} | {'c(T)+c(M)':<9} | {'cost(W)':<8} | {'cost(pi)':<8} | {'OPT':<6} | {'Ratio':<6} | {'cost(pi) <= 1.5*OPT':<20} | {'Status'}")
    print("-" * 125)

    for name, n, dist_mat in test_cases:
        mst_cost, mst_edges_weighted = kruskal_mst(n, dist_mat)
        odd_vertices = extract_odd_degree_vertices(n, mst_edges_weighted)
        matching_cost, _ = min_weight_perfect_matching(odd_vertices, dist_mat)
        tree_plus_matching = mst_cost + matching_cost

        tour_cost, tour, circuit_cost, circuit = christofides_tsp(n, dist_mat)
        opt_cost, _ = solve_tsp_exact(n, dist_mat)

        ratio = tour_cost / opt_cost if opt_cost > 0 else 1.0

        # Invariant checks:
        # 1. Eulerian circuit cost identity: circuit_cost == c(T) + c(M)
        # 2. Shortcutting inequality: tour_cost <= circuit_cost
        # 3. Master 3/2-OPT approximation bound: 2 * tour_cost <= 3 * opt_cost
        # 4. Tour validity: len(tour) == n and len(set(tour)) == n
        h_circuit_cost = (circuit_cost == tree_plus_matching)
        h_shortcut_le = (tour_cost <= circuit_cost)
        h_ratio = (2 * tour_cost <= 3 * opt_cost)
        h_valid_tour = (len(tour) == n and len(set(tour)) == n)

        passed = h_circuit_cost and h_shortcut_le and h_ratio and h_valid_tour
        if not passed:
            all_passed = False

        status = "PASSED [OK]" if passed else "FAILED [VIOLATION]"
        bound_str = f"{tour_cost} <= {1.5 * opt_cost:.1f}"

        print(f"{name:<30} | {n:<3} | {tree_plus_matching:<9} | {circuit_cost:<8} | {tour_cost:<8} | {opt_cost:<6} | {ratio:.4f} | {bound_str:<20} | {status}")

    print("=" * 125)
    if all_passed:
        print("[SUCCESS] All 9 test suites confirmed Master 3/2-OPT Approximation Theorem & Shortcutting Invariant (100% compliance).")
    else:
        print("[FAILURE] Invariant violation detected in Christofides benchmarks!")

    return all_passed


if __name__ == "__main__":
    p2_success = run_mst_lower_bound_benchmarks()
    p3_success = run_handshaking_parity_benchmarks()
    p4_success = run_perfect_matching_benchmarks()
    p56_success = run_christofides_full_benchmarks()
    exit(0 if (p2_success and p3_success and p4_success and p56_success) else 1)


