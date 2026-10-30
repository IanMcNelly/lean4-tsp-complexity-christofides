-- Lean 4 Palomar Challenge Module for the Christofides-Serdyukov 3/2-Approximation Algorithm
-- Matches solution module: Christofides

module

public import Mathlib

@[expose] public section

namespace IJM

namespace TSP

/-!
# Advertised Statement: Christofides–Serdyukov 3/2-Approximation for Metric TSP

This Challenge module states the formal specification and main theorems for the
Christofides–Serdyukov $3/2$-approximation algorithm for the Metric Traveling Salesperson
Problem (Metric TSP) on finite complete undirected graphs over `Fin n` ($n \ge 3$).

Every definition is given transparently below, and all theorem statements are proved
without `sorry` or custom axioms in `Christofides.lean`.
-/

/-- Simple undirected finite graph on vertex set `Fin n`. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ u, ¬ adj u u

/-- Non-negative edge weight function. -/
def CostFunction (n : ℕ) := Fin n → Fin n → ℕ

/-- Ordered sequence of cycle edges formed by adjacent elements in a circular list. -/
def cycleEdges {n : ℕ} (p : List (Fin n)) : List (Fin n × Fin n) :=
  match p with
  | [] => []
  | x :: xs => p.zip (xs ++ [x])

/-- Total traversal cost of the cycle edge sequence. -/
def tourCost {n : ℕ} (c : CostFunction n) (p : List (Fin n)) : ℕ :=
  ((cycleEdges p).map (fun e => c e.1 e.2)).sum

/-- A valid Hamiltonian tour visits every vertex in `Fin n` bijectively along graph edges. -/
def IsTour {n : ℕ} (G : Graph n) (p : List (Fin n)) : Prop :=
  p.length = n ∧ p.Nodup ∧ (∀ e ∈ cycleEdges p, G.adj e.1 e.2)

/-- Complete undirected graph on `Fin n` with loopless edges. -/
def completeGraph (n : ℕ) : Graph n where
  adj := fun u v => u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- Metric cost function satisfying symmetry, zero diagonal, and triangle inequality. -/
structure IsMetricCost {n : ℕ} (c : CostFunction n) : Prop where
  symm : ∀ u v, c u v = c v u
  zero_diag : ∀ u, c u u = 0
  triangle : ∀ u v w, c u w ≤ c u v + c v w

/-- Total traversal cost of an arbitrary directed walk. -/
def walkCost {n : ℕ} (c : CostFunction n) : List (Fin n) → ℕ
  | [] => 0
  | [_] => 0
  | u :: v :: vs => c u v + walkCost c (v :: vs)

/-- Frontier of all possible Hamiltonian vertex permutations on `Fin n`. -/
def allTours (n : ℕ) : List (List (Fin n)) :=
  (List.finRange n).permutations

/-- Constructive optimal tour cost over all vertex permutations of `Fin n`. -/
def optTourCost {n : ℕ} (c : CostFunction n) : ℕ :=
  match allTours n with
  | [] => 0
  | t :: ts => (ts.map (tourCost c)).foldl min (tourCost c t)

/-- Symmetric undirected edge weight on `Sym2 (Fin n)` via `Sym2.lift`. -/
def undirectedEdgeCost {n : ℕ} (c : CostFunction n) (e : Sym2 (Fin n)) : ℕ :=
  Sym2.lift ⟨fun u v => min (c u v) (c v u), fun u v => min_comm (c u v) (c v u)⟩ e

/-- Total weight of a finite set of undirected edges. -/
def edgeSetCost {n : ℕ} (c : CostFunction n) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ e ∈ E, undirectedEdgeCost c e

/-- Reflexive-transitive reachability relation in an undirected edge set `E`. -/
inductive ConnectedInEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : Fin n → Fin n → Prop where
  | refl (u : Fin n) : ConnectedInEdges E u u
  | step {u v w : Fin n} : s(u, v) ∈ E → ConnectedInEdges E v w → ConnectedInEdges E u w

/-- Predicate asserting that an edge finset contains no self-loops. -/
def IsLooplessEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : Prop :=
  ∀ e ∈ E, ∃ u v, e = s(u, v) ∧ u ≠ v

/-- Undirected `Sym2` edges traversed by an open vertex walk. -/
def pathEdges {α : Type*} : List α → List (Sym2 α)
  | [] => []
  | [_] => []
  | u :: v :: vs => s(u, v) :: pathEdges (v :: vs)

/-- A spanning tree on `Fin n` is a connected, loopless edge set of cardinality `n - 1`. -/
structure SpanningTree (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  card_edges : edges.card = n - 1
  connected : ∀ u v : Fin n, ConnectedInEdges edges u v
  loopless : IsLooplessEdges edges

/-- Minimum Spanning Tree (MST) optimality predicate. -/
def IsMST {n : ℕ} (c : CostFunction n) (T : SpanningTree n) : Prop :=
  ∀ T' : SpanningTree n, edgeSetCost c T.edges ≤ edgeSetCost c T'.edges

/-- Degree of vertex `v` in an undirected edge finset `E`. -/
def vertexDegree {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- Subset of vertices having odd degree in `E`. -/
def oddDegreeVertices {n : ℕ} (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.filter (fun v => vertexDegree E v % 2 = 1) Finset.univ

/-- A perfect matching on a vertex subset `S ⊆ Fin n`. -/
structure PerfectMatching {n : ℕ} (S : Finset (Fin n)) where
  edges : Finset (Sym2 (Fin n))
  endpoints_in : ∀ e ∈ edges, ∀ v ∈ e, v ∈ S
  incident_once : ∀ v ∈ S, (edges.filter (fun e => v ∈ e)).card = 1
  loopless : IsLooplessEdges edges

/-- Minimum-weight perfect matching optimality predicate on `S`. -/
def IsMinWeightMatching {n : ℕ} (c : CostFunction n) (S : Finset (Fin n)) (M : PerfectMatching S) : Prop :=
  ∀ M' : PerfectMatching S, edgeSetCost c M.edges ≤ edgeSetCost c M'.edges

/-- Multigraph edge multiset over `Sym2 (Fin n)`. -/
abbrev MultigraphEdges (n : ℕ) := Multiset (Sym2 (Fin n))

/-- Multigraph union (multiset sum) preserving parallel edges between `E1` and `E2`. -/
def multigraphUnion {n : ℕ} (E1 E2 : Finset (Sym2 (Fin n))) : MultigraphEdges n :=
  E1.val + E2.val

/-- Vertex degree in a multigraph edge multiset. -/
def multigraphDegree {n : ℕ} (E : MultigraphEdges n) (v : Fin n) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- A closed Eulerian circuit traversing every edge of `E` and visiting all vertices. -/
structure EulerianCircuit {n : ℕ} (E : MultigraphEdges n) where
  walk : List (Fin n)
  is_closed : walk.head? = walk.getLast?
  edge_multiset_eq : (pathEdges walk : Multiset (Sym2 (Fin n))) = E
  visits_all : ∀ v : Fin n, v ∈ walk

/-- Metric shortcutting operator removing duplicate vertices from a closed walk. -/
def shortcutCircuit {n : ℕ} (w : List (Fin n)) : List (Fin n) :=
  (w.dropLast).eraseDups

/-- Bundled certificate for the Christofides-Serdyukov algorithm on `(n, c)`. -/
structure ChristofidesCertificate (n : ℕ) (c : CostFunction n) where
  tree : SpanningTree n
  tree_mst : IsMST c tree
  matching : PerfectMatching (oddDegreeVertices tree.edges)
  matching_min : IsMinWeightMatching c (oddDegreeVertices tree.edges) matching
  eulerian : EulerianCircuit (multigraphUnion tree.edges matching.edges)

/-- The Hamiltonian tour produced by shortcutting the Eulerian circuit in a `ChristofidesCertificate`. -/
def christofidesTour {n : ℕ} {c : CostFunction n}
    (cert : ChristofidesCertificate n c) : List (Fin n) :=
  shortcutCircuit cert.eulerian.walk

/-!
## Main Theorems
-/

/-- Master MST Lower Bound: the weight of a Minimum Spanning Tree is at most `optTourCost c`. -/
theorem MSTCost_le_OPT {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (T_mst : SpanningTree n) (hMST : IsMST c T_mst) :
    edgeSetCost c T_mst.edges ≤ optTourCost c := by
  sorry

/-- Euler's Handshaking Parity Invariant: any loopless undirected graph has an even number of odd-degree vertices. -/
theorem even_card_oddDegreeVertices {n : ℕ} (E : Finset (Sym2 (Fin n)))
    (h_loopless : IsLooplessEdges E) :
    Even (oddDegreeVertices E).card := by
  sorry

/-- Every perfect matching `M` on `S` satisfies `2 * |M| = |S|`. -/
lemma perfectMatching_card_two_mul {n : ℕ} {S : Finset (Fin n)} (M : PerfectMatching S) :
    2 * M.edges.card = S.card := by
  sorry

/-- Master Matching Upper Bound: a minimum-weight perfect matching on the odd-degree vertices of `T`
has weight at most `(1/2) * optTourCost c` (stated in exact integer scaling `2 * cost(M) ≤ OPT`). -/
theorem matchingCost_le_half_OPT {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M) :
    2 * edgeSetCost c M.edges ≤ optTourCost c := by
  sorry

/-- Every vertex in the multigraph union `T ∪ M` has even degree. -/
lemma multigraph_degree_even {n : ℕ} (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges)) (v : Fin n) :
    Even (multigraphDegree (multigraphUnion T.edges M.edges) v) := by
  sorry

/-- Traversal cost of an Eulerian circuit of `T ∪ M` equals `cost(T) + cost(M)`. -/
lemma circuitCost_eq_treeCost_add_matchingCost {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    walkCost c W.walk = edgeSetCost c T.edges + edgeSetCost c M.edges := by
  sorry

/-- Shortcutting any Eulerian circuit on `n ≥ 3` vertices yields a valid Hamiltonian tour of `K_n`. -/
lemma shortcutCircuit_isTour {n : ℕ} (hn : 3 ≤ n) (E : MultigraphEdges n)
    (W : EulerianCircuit E) :
    IsTour (completeGraph n) (shortcutCircuit W.walk) := by
  sorry

/-- Metric Shortcutting Contraction: shortcutting an Eulerian circuit does not increase traversal cost. -/
theorem shortcut_tourCost_le_circuitCost {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (E : MultigraphEdges n) (W : EulerianCircuit E) :
    tourCost c (shortcutCircuit W.walk) ≤ walkCost c W.walk := by
  sorry

/-- Master Circuit 3/2-Approximation Theorem (Integer Scaling): `2 * cost(shortcut(W)) ≤ 3 * OPT`. -/
theorem christofides_circuit_approx_ratio_nat {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n) (hMST : IsMST c T)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M)
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    2 * tourCost c (shortcutCircuit W.walk) ≤ 3 * optTourCost c := by
  sorry

/-- Master Circuit 3/2-Approximation Theorem (Real Arithmetic): `cost(shortcut(W)) ≤ (3/2) * OPT`. -/
theorem christofides_circuit_approx_ratio {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n) (hMST : IsMST c T)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M)
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    (tourCost c (shortcutCircuit W.walk) : ℝ) ≤ (3 / 2) * (optTourCost c : ℝ) := by
  sorry

/-- Master Certificate 3/2-Approximation Theorem (Integer Scaling). -/
theorem christofides_approx_ratio_nat {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (cert : ChristofidesCertificate n c) :
    2 * tourCost c (christofidesTour cert) ≤ 3 * optTourCost c := by
  sorry

/-- Master Certificate 3/2-Approximation Theorem (Real Arithmetic). -/
theorem christofides_approx_ratio {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (cert : ChristofidesCertificate n c) :
    (tourCost c (christofidesTour cert) : ℝ) ≤ (3 / 2) * (optTourCost c : ℝ) := by
  sorry

/-- Constructive Existence of a Complete `ChristofidesCertificate` for any `n ≥ 3` and `c`. -/
theorem exists_christofidesCertificate {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :
    ∃ _cert : ChristofidesCertificate n c, True := by
  sorry

/-- Unconditional Christofides Certificate & 3/2-Approximation Theorem (Integer Scaling). -/
theorem christofides_certificate_approx_ratio_nat_unconditional {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) :
    ∃ cert : ChristofidesCertificate n c,
      IsTour (completeGraph n) (christofidesTour cert) ∧
      2 * tourCost c (christofidesTour cert) ≤ 3 * optTourCost c := by
  sorry

/-- Unconditional Christofides Certificate & 3/2-Approximation Theorem (Real Arithmetic). -/
theorem christofides_certificate_approx_ratio_unconditional {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) :
    ∃ cert : ChristofidesCertificate n c,
      IsTour (completeGraph n) (christofidesTour cert) ∧
      (tourCost c (christofidesTour cert) : ℝ) ≤ (3 / 2 : ℝ) * (optTourCost c : ℝ) := by
  sorry

end TSP

end IJM
