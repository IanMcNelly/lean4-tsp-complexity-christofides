-- Lean 4 formalization matching openai/math repository idioms
-- Module: IJM.TSP.Christofides
-- Topic: Metric Foundations, Walk Contraction, Spanning Trees, Handshaking Lemma, Degree Parity, Perfect Matchings, Eulerian Multigraphs, Shortcutting, and Master 3/2-Approximation Bound
-- Track D: Complete Formal Verification (Phases 1-6)

import Mathlib

namespace IJM

namespace TSP

/-!
# Track D: Christofides-Serdyukov 3/2-Approximation Algorithm Formal Verification (Phases 1-6)

This module formalizes the complete, end-to-end formal verification of the celebrated
Christofides-Serdyukov 3/2-approximation algorithm for the metric Traveling Salesperson Problem
(Metric TSP) in Lean 4 with ZERO `sorry`s and ZERO `admit`s.

Key components established across all 6 phases:
1. Discrete graph and tour foundations matching `TSPComplexity.lean` (`Graph`, `CostFunction`,
   `cycleEdges`, `tourCost`, `IsTour`).
2. Complete metric graphs (`completeGraph`) and basic properties.
3. Metric cost spaces (`IsMetricCost`) with symmetry, zero diagonal, and triangle inequality.
4. Walk traversal costs (`walkCost`) and the iterated/telescoping triangle inequality (`pathCost_le_walkCost`).
5. Constructive optimal tour specification (`allTours`, `optTourCost`) and proofs of:
   - Metric lower bound: `optTourCost_le_tourCost` (every valid tour has cost at least `optTourCost`).
   - Constructive existence: `exists_optTour` (for $n \ge 3$, an optimal tour exists in $K_n$).
6. Undirected edge weights & finset aggregation (`undirectedEdgeCost`, `edgeSetCost`).
7. Spanning tree and Minimum Spanning Tree specification (`ConnectedInEdges`, `SpanningTree`, `IsMST`).
8. Hamiltonian path spanning tree witness (`tourToSpanningPath`, `tourToSpanningPath_cost_le_tourCost`).
9. Master MST Lower Bound theorem: `MSTCost_le_OPT` ($c(T_{\text{mst}}) \le \text{OPT}$).
10. Undirected edge looplessness and endpoint counting (`IsLooplessEdges`, `card_filter_mem_edge`, `tourToSpanningPath_edges_loopless`).
11. Vertex incidence and degrees in undirected edge finsets (`vertexDegree`).
12. Euler's Handshaking Lemma via double counting / sum swapping (`sum_vertexDegree_eq_two_card`).
13. Odd-degree vertex extraction (`oddDegreeVertices`).
14. Mod-2 degree parity decomposition and Parity Conservation Theorem (`sum_mod_two_partition`, `even_card_oddDegreeVertices`, `tree_even_card_oddDegreeVertices`).
15. Perfect matching specification on arbitrary vertex subsets (`PerfectMatching S`) and cardinality invariant (`perfectMatching_card_two_mul`).
16. Minimum-weight perfect matching optimality predicate (`IsMinWeightMatching`).
17. Metric tour projection operator (`shortcutToSubset`) and cycle shortcutting bound (`shortcutToSubset_cost_le_opt`).
18. Alternating matching decomposition of even cycles (`evenCycleMatchingOne`, `evenCycleMatchingTwo`, `cycle_matchings_cost_sum`).
19. Master Matching Upper Bound Theorem: `matchingCost_le_half_OPT` ($2 \cdot c(M) \le \text{OPT}$).
20. Eulerian multigraph edge multisets and parity conservation: `multigraphUnion`, `multigraphDegree`, `multigraph_degree_even`.
21. Eulerian circuit specification and traversal cost conservation: `EulerianCircuit`, `circuitCost_eq_treeCost_add_matchingCost`.
22. Metric shortcutting operator and tour certification: `shortcutCircuit`, `shortcutCircuit_isTour`.
23. Master Shortcutting Lemma via subwalk contraction: `walkCost_sublist_le`, `shortcut_tourCost_le_circuitCost`.
24. Master Approximation Theorems:
    - Integer Scaling: `christofides_circuit_approx_ratio_nat`, `christofides_approx_ratio_nat` ($2 \cdot \text{cost} \le 3 \cdot \text{OPT}$).
    - Real Arithmetic: `christofides_circuit_approx_ratio`, `christofides_approx_ratio` ($\text{cost} \le \frac{3}{2}\text{OPT}$).
-/

/-!
## 1. Discrete Problem Formulation & Foundational Types
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

/-- Complete undirected graph on Fin n with loopless edges. -/
def completeGraph (n : ℕ) : Graph n where
  adj := fun u v => u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

lemma completeGraph_adj (n : ℕ) (u v : Fin n) :
    (completeGraph n).adj u v ↔ u ≠ v :=
  Iff.rfl

lemma completeGraph_symm (n : ℕ) (u v : Fin n) (h : (completeGraph n).adj u v) :
    (completeGraph n).adj v u :=
  h.symm

lemma completeGraph_loopless (n : ℕ) (u : Fin n) :
    ¬ (completeGraph n).adj u u :=
  fun h => h rfl

lemma cycleEdges_nil {n : ℕ} : cycleEdges ([] : List (Fin n)) = [] := rfl

lemma cycleEdges_length {n : ℕ} (p : List (Fin n)) (h : p ≠ []) :
    (cycleEdges p).length = p.length := by
  cases p with
  | nil => contradiction
  | cons x xs =>
    dsimp [cycleEdges]
    rw [List.length_zip, List.length_append]
    simp

/-!
## 2. Metric Cost Spaces & Walk Contraction
-/

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

@[simp] lemma walkCost_nil {n : ℕ} (c : CostFunction n) :
    walkCost c ([] : List (Fin n)) = 0 := rfl

@[simp] lemma walkCost_singleton {n : ℕ} (c : CostFunction n) (u : Fin n) :
    walkCost c [u] = 0 := rfl

@[simp] lemma walkCost_cons_cons {n : ℕ} (c : CostFunction n) (u v : Fin n) (vs : List (Fin n)) :
    walkCost c (u :: v :: vs) = c u v + walkCost c (v :: vs) := rfl

/-- Stepwise triangle inequality extension for walks. -/
lemma walkCost_triangle_step {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (u v w : Fin n) :
    c u w ≤ c u v + c v w :=
  hMetric.triangle u v w

/-- Inductive helper for the telescoping triangle inequality on non-empty tails. -/
lemma pathCost_le_walkCost_cons {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c) :
    ∀ (u v : Fin n) (vs : List (Fin n)),
    c u ((v :: vs).getLast (by simp)) ≤ walkCost c (u :: v :: vs) := by
  intro u v vs
  induction vs generalizing u v with
  | nil =>
    dsimp [walkCost]
    exact Nat.le_refl _
  | cons w ws ih =>
    rw [walkCost_cons_cons]
    have hlast : (v :: w :: ws).getLast (by simp) = (w :: ws).getLast (by simp) := rfl
    rw [hlast]
    have h_tri : c u ((w :: ws).getLast (by simp)) ≤ c u v + c v ((w :: ws).getLast (by simp)) :=
      hMetric.triangle u v ((w :: ws).getLast (by simp))
    have h_ih := ih v w
    exact h_tri.trans (Nat.add_le_add_left h_ih (c u v))

lemma ne_nil_of_length_ge_two {α : Type*} {w : List α} (h : 2 ≤ w.length) : w ≠ [] := by
  rintro rfl
  simp at h

/-- Telescoping triangle inequality: direct distance is bounded by intermediate walk cost. -/
lemma pathCost_le_walkCost {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    {w : List (Fin n)} (h : 2 ≤ w.length) :
    c (w.head (ne_nil_of_length_ge_two h)) (w.getLast (ne_nil_of_length_ge_two h)) ≤ walkCost c w := by
  cases w with
  | nil => simp at h
  | cons u ws =>
    cases ws with
    | nil => simp at h
    | cons v vs =>
      have hhead : (u :: v :: vs).head (ne_nil_of_length_ge_two h) = u := rfl
      have hlast : (u :: v :: vs).getLast (ne_nil_of_length_ge_two h) = (v :: vs).getLast (by simp) := rfl
      rw [hhead, hlast]
      exact pathCost_le_walkCost_cons c hMetric u v vs

/-!
## 3. Constructive Optimal Tour Specification
-/

/-- Frontier of all possible Hamiltonian vertex permutations. -/
def allTours (n : ℕ) : List (List (Fin n)) :=
  (List.finRange n).permutations

lemma tour_mem_allTours {n : ℕ} {G : Graph n} {p : List (Fin n)} (hTour : IsTour G p) :
    p ∈ allTours n := by
  have hlen : p.length = n := hTour.1
  have hnodup : p.Nodup := hTour.2.1
  have h_univ : p.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnodup, hlen, Fintype.card_fin]
  dsimp [allTours]
  rw [List.mem_permutations]
  rw [List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)]
  intro v
  refine ⟨fun _ => List.mem_finRange v, fun _ => ?_⟩
  have hv : v ∈ p.toFinset := by
    rw [h_univ]
    exact Finset.mem_univ v
  exact List.mem_toFinset.mp hv

/-- Exact optimal tour cost over all permutations on the complete graph. -/
def optTourCost {n : ℕ} (c : CostFunction n) : ℕ :=
  match allTours n with
  | [] => 0
  | t :: ts => (ts.map (tourCost c)).foldl min (tourCost c t)

lemma foldl_min_le_init (xs : List ℕ) (init : ℕ) :
    xs.foldl min init ≤ init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    dsimp [List.foldl]
    exact (ih (min init x)).trans (min_le_left init x)

lemma foldl_min_le_mem {x : ℕ} {xs : List ℕ} (init : ℕ) (hx : x ∈ xs) :
    xs.foldl min init ≤ x := by
  induction xs generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    dsimp [List.foldl]
    cases hx with
    | head =>
      exact (foldl_min_le_init ys (min init x)).trans (min_le_right init x)
    | tail _ hmem =>
      exact ih (min init y) hmem

/-- Any valid Hamiltonian tour has cost at least optTourCost. -/
lemma optTourCost_le_tourCost {n : ℕ} (c : CostFunction n) (p : List (Fin n))
    (hp : IsTour (completeGraph n) p) :
    optTourCost c ≤ tourCost c p := by
  have hmem : p ∈ allTours n := tour_mem_allTours hp
  dsimp [optTourCost]
  cases heq : allTours n with
  | nil =>
    rw [heq] at hmem
    contradiction
  | cons t ts =>
    rw [heq] at hmem
    cases hmem with
    | head =>
      exact foldl_min_le_init (ts.map (tourCost c)) (tourCost c p)
    | tail _ hmem_ts =>
      have hmap : tourCost c p ∈ ts.map (tourCost c) := List.mem_map.mpr ⟨p, hmem_ts, rfl⟩
      exact foldl_min_le_mem (tourCost c t) hmap

lemma exists_mem_foldl_min {α : Type*} (ts : List α) (t : α) (f : α → ℕ) :
    ∃ p ∈ t :: ts, f p = (ts.map f).foldl min (f t) := by
  induction ts generalizing t with
  | nil =>
    refine ⟨t, List.Mem.head _, rfl⟩
  | cons y ys ih =>
    dsimp [List.map, List.foldl]
    by_cases hle : f t ≤ f y
    · rw [min_eq_left hle]
      rcases ih t with ⟨p, hp_mem, hp_eq⟩
      refine ⟨p, ?_, hp_eq⟩
      cases hp_mem with
      | head => exact List.Mem.head _
      | tail _ hmem => exact List.Mem.tail _ (List.Mem.tail _ hmem)
    · have hle' : f y ≤ f t := by omega
      rw [min_eq_right hle']
      rcases ih y with ⟨p, hp_mem, hp_eq⟩
      refine ⟨p, ?_, hp_eq⟩
      cases hp_mem with
      | head => exact List.Mem.tail _ (List.Mem.head _)
      | tail _ hmem => exact List.Mem.tail _ (List.Mem.tail _ hmem)

/-- Any permutation of Fin n for n ≥ 3 forms a valid Hamiltonian tour in completeGraph n. -/
lemma isTour_completeGraph_of_mem_allTours {n : ℕ} (hn : 3 ≤ n) {p : List (Fin n)}
    (hp : p ∈ allTours n) : IsTour (completeGraph n) p := by
  have hperm : p.Perm (List.finRange n) := List.mem_permutations.mp hp
  have hlen : p.length = n := by
    rw [hperm.length_eq, List.length_finRange]
  have hnodup : p.Nodup := by
    rw [hperm.nodup_iff]
    exact List.nodup_finRange n
  refine ⟨hlen, hnodup, ?_⟩
  intro e he
  rw [completeGraph_adj]
  cases hp_cons : p with
  | nil =>
    have : p.length = 0 := by rw [hp_cons]; rfl
    omega
  | cons x xs =>
    have h_cyc : cycleEdges p = (x :: xs).zip (xs ++ [x]) := by
      dsimp [cycleEdges]
      rw [hp_cons]
    rw [h_cyc] at he
    rw [List.mem_iff_getElem] at he
    rcases he with ⟨i, hi, rfl⟩
    have h_zip_len : ((x :: xs).zip (xs ++ [x])).length = xs.length + 1 := by
      rw [List.length_zip, List.length_append, List.length_singleton]
      change min (xs.length + 1) (xs.length + 1) = xs.length + 1
      exact min_self _
    have hi_lt : i < xs.length + 1 := by rw [h_zip_len] at hi; exact hi
    have hi_p : i < (x :: xs).length := hi_lt
    have hi_app : i < (xs ++ [x]).length := by
      rw [List.length_append, List.length_singleton]
      exact hi_lt
    have hfst : ((x :: xs).zip (xs ++ [x]))[i].1 = (x :: xs)[i]'hi_p := by
      exact congrArg Prod.fst List.getElem_zip
    have hsnd : ((x :: xs).zip (xs ++ [x]))[i].2 = (xs ++ [x])[i]'hi_app := by
      exact congrArg Prod.snd List.getElem_zip
    intro heq
    rw [hfst, hsnd] at heq
    have h_nodup_cons : (x :: xs).Nodup := by rw [← hp_cons]; exact hnodup
    by_cases hi_xs : i < xs.length
    · have h_app : (xs ++ [x])[i]'hi_app = xs[i] := by
        exact List.getElem_append_left hi_xs
      rw [h_app] at heq
      have hi_succ : i + 1 < (x :: xs).length := by
        change i + 1 < xs.length + 1
        omega
      have h_xs_succ : xs[i] = (x :: xs)[i + 1]'hi_succ := rfl
      rw [h_xs_succ] at heq
      have h_inj := (h_nodup_cons.getElem_inj_iff (hi := hi_p) (hj := hi_succ)).mp heq
      omega
    · have hi_eq : i = xs.length := by omega
      have h_app : (xs ++ [x])[i]'hi_app = x := by
        subst hi_eq
        simp
      rw [h_app] at heq
      have h0 : 0 < (x :: xs).length := by
        change 0 < xs.length + 1
        omega
      have h_x0 : x = (x :: xs)[0]'h0 := rfl
      rw [h_x0] at heq
      have h_inj := (h_nodup_cons.getElem_inj_iff (hi := hi_p) (hj := h0)).mp heq
      have : xs.length = 0 := by
        subst hi_eq
        exact h_inj
      have : p.length = 1 := by
        rw [hp_cons]
        change xs.length + 1 = 1
        omega
      omega

/-- For n ≥ 3, there exists an optimal tour achieving optTourCost. -/
lemma exists_optTour {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :
    ∃ p : List (Fin n), IsTour (completeGraph n) p ∧ tourCost c p = optTourCost c := by
  have h_perm_self : List.finRange n ∈ allTours n := by
    dsimp [allTours]
    exact List.mem_permutations.mpr (List.Perm.refl _)
  cases heq : allTours n with
  | nil =>
    rw [heq] at h_perm_self
    contradiction
  | cons t ts =>
    have h_opt : optTourCost c = (ts.map (tourCost c)).foldl min (tourCost c t) := by
      dsimp [optTourCost]
      rw [heq]
    rcases exists_mem_foldl_min ts t (tourCost c) with ⟨p, hp_mem, hp_cost⟩
    have hp_all : p ∈ allTours n := by
      rw [heq]
      exact hp_mem
    refine ⟨p, isTour_completeGraph_of_mem_allTours hn hp_all, ?_⟩
    rw [h_opt]
    exact hp_cost

lemma isTour_ne_nil {n : ℕ} (hn : 1 ≤ n) {G : Graph n} {p : List (Fin n)} (hp : IsTour G p) :
    p ≠ [] := by
  rintro rfl
  have hlen := hp.1
  simp at hlen
  omega

/-!
## 4. Undirected Edge Weight & Finset Aggregation (Phase 2)
-/

/-- Canonical undirected edge cost lifted from a directed cost function.
For symmetric/metric cost functions, this coincides exactly with `c u v`. -/
def undirectedEdgeCost {n : ℕ} (c : CostFunction n) (e : Sym2 (Fin n)) : ℕ :=
  Sym2.lift ⟨fun u v => min (c u v) (c v u), fun u v => min_comm (c u v) (c v u)⟩ e

lemma undirectedEdgeCost_mk {n : ℕ} (c : CostFunction n) (u v : Fin n) :
    undirectedEdgeCost c s(u, v) = min (c u v) (c v u) := rfl

lemma undirectedEdgeCost_of_symm {n : ℕ} (c : CostFunction n) (h : ∀ u v, c u v = c v u) (u v : Fin n) :
    undirectedEdgeCost c s(u, v) = c u v := by
  dsimp [undirectedEdgeCost]
  rw [h u v, min_self]

lemma undirectedEdgeCost_metric {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c) (u v : Fin n) :
    undirectedEdgeCost c s(u, v) = c u v :=
  undirectedEdgeCost_of_symm c hMetric.symm u v

/-- Total weight of an undirected edge finset under cost function `c`. -/
def edgeSetCost {n : ℕ} (c : CostFunction n) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ e ∈ E, undirectedEdgeCost c e

@[simp] lemma edgeSetCost_empty {n : ℕ} (c : CostFunction n) :
    edgeSetCost c ∅ = 0 := Finset.sum_empty

lemma edgeSetCost_subset {n : ℕ} (c : CostFunction n) {E1 E2 : Finset (Sym2 (Fin n))}
    (h : E1 ⊆ E2) : edgeSetCost c E1 ≤ edgeSetCost c E2 :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

lemma edgeSetCost_union_of_disjoint {n : ℕ} (c : CostFunction n) {E1 E2 : Finset (Sym2 (Fin n))}
    (h : Disjoint E1 E2) : edgeSetCost c (E1 ∪ E2) = edgeSetCost c E1 + edgeSetCost c E2 :=
  Finset.sum_union h

/-!
## 5. Spanning Tree & Minimum Spanning Tree (MST) Specification
-/

/-- Connectivity predicate in an undirected edge finset `E`:
there is a sequence of edges in `E` connecting `u` to `v`. -/
inductive ConnectedInEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : Fin n → Fin n → Prop where
  | refl (u : Fin n) : ConnectedInEdges E u u
  | step {u v w : Fin n} : s(u, v) ∈ E → ConnectedInEdges E v w → ConnectedInEdges E u w

lemma ConnectedInEdges.trans {n : ℕ} {E : Finset (Sym2 (Fin n))} {u v w : Fin n}
    (h1 : ConnectedInEdges E u v) (h2 : ConnectedInEdges E v w) :
    ConnectedInEdges E u w := by
  induction h1 with
  | refl _ => exact h2
  | step h_edge _ ih => exact ConnectedInEdges.step h_edge (ih h2)

lemma ConnectedInEdges.single {n : ℕ} {E : Finset (Sym2 (Fin n))} {u v : Fin n}
    (h : s(u, v) ∈ E) : ConnectedInEdges E u v :=
  ConnectedInEdges.step h (ConnectedInEdges.refl v)

lemma ConnectedInEdges.symm {n : ℕ} {E : Finset (Sym2 (Fin n))} {u v : Fin n}
    (h : ConnectedInEdges E u v) : ConnectedInEdges E v u := by
  induction h with
  | refl _ => exact ConnectedInEdges.refl _
  | @step a b c h_edge _ ih =>
    have h_ba : s(b, a) ∈ E := by
      rw [Sym2.eq_swap]
      exact h_edge
    exact ConnectedInEdges.trans ih (ConnectedInEdges.single h_ba)

lemma ConnectedInEdges_mono {n : ℕ} {E1 E2 : Finset (Sym2 (Fin n))} (hsub : E1 ⊆ E2)
    {u v : Fin n} (h : ConnectedInEdges E1 u v) : ConnectedInEdges E2 u v := by
  induction h with
  | refl _ => exact ConnectedInEdges.refl _
  | step h_edge _ ih => exact ConnectedInEdges.step (hsub h_edge) ih

/-- A set of undirected edges is loopless if every edge connects two distinct vertices. -/
def IsLooplessEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : Prop :=
  ∀ e ∈ E, ∃ u v, e = s(u, v) ∧ u ≠ v

/-- Undirected consecutive edge sequence along a vertex walk. -/
def pathEdges {α : Type*} : List α → List (Sym2 α)
  | [] => []
  | [_] => []
  | u :: v :: vs => s(u, v) :: pathEdges (v :: vs)

/-- Any path of distinct vertices produces loopless undirected edges. -/
lemma pathEdges_loopless {α : Type*} {p : List α} (hp : p.Nodup) :
    ∀ e ∈ pathEdges p, ∃ u v, e = s(u, v) ∧ u ≠ v := by
  induction p with
  | nil =>
    intro e he
    contradiction
  | cons u ws ih =>
    cases ws with
    | nil =>
      intro e he
      contradiction
    | cons v vs =>
      intro e he
      dsimp [pathEdges] at he
      cases he with
      | head =>
        refine ⟨u, v, rfl, ?_⟩
        intro h_eq
        subst h_eq
        have hu_in : u ∈ u :: vs := List.Mem.head _
        have hu_not : u ∉ u :: vs := (List.nodup_cons.mp hp).1
        exact hu_not hu_in
      | tail _ he_tail =>
        have hp_tail : (v :: vs).Nodup := hp.of_cons
        exact ih hp_tail e he_tail

/-- Spanning tree on `Fin n`: exactly `n - 1` undirected edges connecting all vertices. -/
structure SpanningTree (n : ℕ) where
  edges : Finset (Sym2 (Fin n))
  card_edges : edges.card = n - 1
  connected : ∀ u v : Fin n, ConnectedInEdges edges u v
  loopless : IsLooplessEdges edges

/-- Minimum Spanning Tree optimality predicate: `T` achieves minimal edgeSetCost. -/
def IsMST {n : ℕ} (c : CostFunction n) (T : SpanningTree n) : Prop :=
  ∀ T' : SpanningTree n, edgeSetCost c T.edges ≤ edgeSetCost c T'.edges

/-!
## 6. Hamiltonian Path Spanning Tree Witness
-/

/-- Directed consecutive edge pairs along a vertex walk. -/
def directedPathEdges {α : Type*} : List α → List (α × α)
  | [] => []
  | [_] => []
  | u :: v :: vs => (u, v) :: directedPathEdges (v :: vs)

lemma pathEdges_eq_map {α : Type*} (w : List α) :
    pathEdges w = (directedPathEdges w).map (fun e => s(e.1, e.2)) := by
  induction w with
  | nil => rfl
  | cons u ws ih =>
    cases ws with
    | nil => rfl
    | cons v vs =>
      dsimp [pathEdges, directedPathEdges]
      rw [ih]
      rfl

lemma mem_pathEdges_mem {α : Type*} {w : List α} {e : Sym2 α} (he : e ∈ pathEdges w) :
    ∀ x ∈ e, x ∈ w := by
  induction w with
  | nil => contradiction
  | cons u ws ih =>
    cases ws with
    | nil => contradiction
    | cons v vs =>
      dsimp [pathEdges] at he
      cases he with
      | head =>
        intro x hx
        simp only [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact List.Mem.head _
        · exact List.Mem.tail _ (List.Mem.head _)
      | tail _ he_tail =>
        intro x hx
        exact List.Mem.tail _ (ih he_tail x hx)

lemma pathEdges_nodup {α : Type*} {w : List α} (hw : w.Nodup) : (pathEdges w).Nodup := by
  induction w with
  | nil => exact List.nodup_nil
  | cons u ws ih =>
    cases ws with
    | nil => exact List.nodup_nil
    | cons v vs =>
      dsimp [pathEdges]
      have h_nodup_tail : (v :: vs).Nodup := hw.of_cons
      have ih_res := ih h_nodup_tail
      refine List.Nodup.cons ?_ ih_res
      intro h_mem
      have hu_in_edge : u ∈ s(u, v) := by simp
      have hu_in_tail := mem_pathEdges_mem h_mem u hu_in_edge
      have hu_not_in : u ∉ v :: vs := (List.nodup_cons.mp hw).1
      exact hu_not_in hu_in_tail

lemma pathEdges_length {α : Type*} (w : List α) (hw : w ≠ []) :
    (pathEdges w).length = w.length - 1 := by
  induction w with
  | nil => contradiction
  | cons u ws ih =>
    cases ws with
    | nil => rfl
    | cons v vs =>
      dsimp [pathEdges]
      rw [ih (by simp)]
      simp

lemma connected_head_of_mem {n : ℕ} :
    ∀ (w : List (Fin n)) (h_ne : w ≠ []) (x : Fin n) (_hx : x ∈ w),
    ConnectedInEdges (pathEdges w).toFinset (w.head h_ne) x := by
  intro w
  induction w with
  | nil => intro h_ne; contradiction
  | cons u ws ih =>
    intro h_ne x hx
    cases ws with
    | nil =>
      cases hx with
      | head => exact ConnectedInEdges.refl _
      | tail _ h => contradiction
    | cons v vs =>
      cases hx with
      | head => exact ConnectedInEdges.refl _
      | tail _ hx_ws =>
        have h_edge : s(u, v) ∈ (pathEdges (u :: v :: vs)).toFinset := by
          rw [List.mem_toFinset]
          exact List.Mem.head _
        have h_step : ConnectedInEdges (pathEdges (u :: v :: vs)).toFinset u v :=
          ConnectedInEdges.single h_edge
        have h_sub : (pathEdges (v :: vs)).toFinset ⊆ (pathEdges (u :: v :: vs)).toFinset := by
          intro e he
          rw [List.mem_toFinset] at he ⊢
          exact List.Mem.tail _ he
        have h_tail := ConnectedInEdges_mono h_sub (ih (by simp) x hx_ws)
        have h_u : (u :: v :: vs).head h_ne = u := rfl
        rw [h_u]
        exact ConnectedInEdges.trans h_step h_tail

/-- Dropping the wrap-around cycle edge from any Hamiltonian tour on `Fin n` ($n \ge 3$)
yields a certified spanning tree `tourToSpanningPath`. -/
def tourToSpanningPath {n : ℕ} (hn : 3 ≤ n) (p : List (Fin n))
    (hp : IsTour (completeGraph n) p) : SpanningTree n where
  edges := (pathEdges p).toFinset
  card_edges := by
    have hnodup_p : p.Nodup := hp.2.1
    have hnodup_edges : (pathEdges p).Nodup := pathEdges_nodup hnodup_p
    rw [List.toFinset_card_of_nodup hnodup_edges]
    have hp_ne : p ≠ [] := isTour_ne_nil (by omega) hp
    rw [pathEdges_length p hp_ne]
    rw [hp.1]
  connected := by
    intro u v
    have hp_ne : p ≠ [] := isTour_ne_nil (by omega) hp
    have hu_mem : u ∈ p := by
      have h_univ : p.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup hp.2.1, hp.1, Fintype.card_fin]
      have : u ∈ p.toFinset := by rw [h_univ]; exact Finset.mem_univ u
      exact List.mem_toFinset.mp this
    have hv_mem : v ∈ p := by
      have h_univ : p.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup hp.2.1, hp.1, Fintype.card_fin]
      have : v ∈ p.toFinset := by rw [h_univ]; exact Finset.mem_univ v
      exact List.mem_toFinset.mp this
    have h1 := connected_head_of_mem p hp_ne u hu_mem
    have h2 := connected_head_of_mem p hp_ne v hv_mem
    exact ConnectedInEdges.trans (ConnectedInEdges.symm h1) h2
  loopless := by
    intro e he
    rw [List.mem_toFinset] at he
    exact pathEdges_loopless hp.2.1 e he

lemma zip_append_singleton {α β : Type*} (x : α) (xs : List α) (y : β) (ys : List β)
    (hlen : xs.length = ys.length) :
    (x :: xs).zip (ys ++ [y]) = ((x :: xs).zip ys) ++ [((x :: xs).getLast (by simp), y)] := by
  induction xs generalizing x ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y0 ys => simp at hlen
  | cons x1 xs1 ih =>
    cases ys with
    | nil => simp at hlen
    | cons y0 ys1 =>
      have hlen1 : xs1.length = ys1.length := by simpa using hlen
      change (x, y0) :: (x1 :: xs1).zip (ys1 ++ [y]) =
        (x, y0) :: ((x1 :: xs1).zip ys1 ++ [((x1 :: xs1).getLast (by simp), y)])
      rw [ih x1 ys1 hlen1]

lemma directedPathEdges_eq_zip {α : Type*} (x : α) (xs : List α) :
    directedPathEdges (x :: xs) = (x :: xs).zip xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    dsimp [directedPathEdges]
    rw [ih y]

lemma cycleEdges_cons {n : ℕ} (x : Fin n) (xs : List (Fin n)) :
    cycleEdges (x :: xs) = directedPathEdges (x :: xs) ++ [((x :: xs).getLast (by simp), x)] := by
  dsimp [cycleEdges]
  rw [zip_append_singleton x xs x xs rfl, directedPathEdges_eq_zip]

lemma sum_map_le_sum_map {α : Type*} (L : List α) (f g : α → ℕ) (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    dsimp [List.map, List.sum]
    have h_head := h a (List.Mem.head _)
    have h_tail := ih (fun x hx => h x (List.Mem.tail _ hx))
    exact Nat.add_le_add h_head h_tail

lemma pathEdges_cost_le_tourCost {n : ℕ} (c : CostFunction n) (p : List (Fin n)) :
    ((pathEdges p).map (undirectedEdgeCost c)).sum ≤ tourCost c p := by
  cases p with
  | nil =>
    dsimp [pathEdges, tourCost, cycleEdges]
    exact Nat.le_refl _
  | cons x xs =>
    dsimp [tourCost]
    rw [cycleEdges_cons x xs]
    rw [List.map_append, List.sum_append]
    rw [pathEdges_eq_map (x :: xs)]
    rw [List.map_map]
    have h_le : (((directedPathEdges (x :: xs)).map (fun e => undirectedEdgeCost c s(e.1, e.2)))).sum ≤
        (((directedPathEdges (x :: xs)).map (fun e => c e.1 e.2))).sum := by
      apply sum_map_le_sum_map
      intro e _
      exact min_le_left (c e.1 e.2) (c e.2 e.1)
    have : ((directedPathEdges (x :: xs)).map (fun e => c e.1 e.2)).sum ≤
        ((directedPathEdges (x :: xs)).map (fun e => c e.1 e.2)).sum +
          ([c ((x :: xs).getLast (by simp)) x]).sum := Nat.le_add_right _ _
    exact h_le.trans this

/-- Cost of the spanning path is bounded by the original tour cost. -/
lemma tourToSpanningPath_cost_le_tourCost {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (p : List (Fin n)) (hp : IsTour (completeGraph n) p) :
    edgeSetCost c (tourToSpanningPath hn p hp).edges ≤ tourCost c p := by
  dsimp [tourToSpanningPath, edgeSetCost]
  have hnodup_edges : (pathEdges p).Nodup := pathEdges_nodup hp.2.1
  rw [List.sum_toFinset _ hnodup_edges]
  exact pathEdges_cost_le_tourCost c p

/-!
## 7. Master MST Lower Bound Theorem
-/

/-- Master MST Lower Bound: Minimum Spanning Tree cost never exceeds the optimal tour cost (OPT). -/
theorem MSTCost_le_OPT {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (T_mst : SpanningTree n) (hMST : IsMST c T_mst) :
    edgeSetCost c T_mst.edges ≤ optTourCost c := by
  rcases exists_optTour hn c with ⟨p_opt, hp_opt, hcost_opt⟩
  have h_mst_le := hMST (tourToSpanningPath hn p_opt hp_opt)
  have h_path_le := tourToSpanningPath_cost_le_tourCost hn c p_opt hp_opt
  rw [← hcost_opt]
  exact h_mst_le.trans h_path_le

/-!
## 8. Undirected Edge Looplessness & Endpoint Counting
-/

/-- The edges of a spanning path derived from a Hamiltonian tour are strictly loopless. -/
lemma tourToSpanningPath_edges_loopless {n : ℕ} (hn : 3 ≤ n) (p : List (Fin n))
    (hp : IsTour (completeGraph n) p) :
    IsLooplessEdges (tourToSpanningPath hn p hp).edges :=
  (tourToSpanningPath hn p hp).loopless

/-- For any pair of distinct vertices, exactly two vertices in `Fin n` belong to the edge `s(u, v)`. -/
lemma card_filter_mem_edge_of_ne {n : ℕ} {u v : Fin n} (hne : u ≠ v) :
    (Finset.univ.filter (fun x => x ∈ (s(u, v) : Sym2 (Fin n)))).card = 2 := by
  have h_set : (Finset.univ.filter (fun x => x ∈ (s(u, v) : Sym2 (Fin n)))) = {u, v} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
      Finset.mem_insert, Finset.mem_singleton]
  rw [h_set]
  exact Finset.card_pair hne

/-- Any loopless undirected edge has exactly two incident endpoints in `Fin n`. -/
lemma card_filter_mem_edge {n : ℕ} (e : Sym2 (Fin n)) (h : ∃ u v, e = s(u, v) ∧ u ≠ v) :
    (Finset.univ.filter (fun x => x ∈ e)).card = 2 := by
  rcases h with ⟨u, v, rfl, hne⟩
  exact card_filter_mem_edge_of_ne hne

/-!
## 9. Vertex Degree & Euler's Handshaking Lemma
-/

/-- Vertex degree in an undirected edge finset `E`: count of incident edges. -/
def vertexDegree {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- Degree expressed as an indicator sum over edges. -/
lemma vertexDegree_eq_sum_ite {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) :
    vertexDegree E v = ∑ e ∈ E, if v ∈ e then 1 else 0 := by
  dsimp [vertexDegree]
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_filter (fun e => v ∈ e) (fun _ => 1)

/-- Euler's Handshaking Lemma: the sum of vertex degrees in any loopless undirected
graph equals twice the number of edges. Proved by incidence matrix double counting. -/
lemma sum_vertexDegree_eq_two_card {n : ℕ} (E : Finset (Sym2 (Fin n)))
    (h_loopless : IsLooplessEdges E) :
    (∑ v : Fin n, vertexDegree E v) = 2 * E.card := by
  have h_step1 : (∑ v : Fin n, vertexDegree E v) =
      ∑ v : Fin n, ∑ e ∈ E, (if v ∈ e then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v _
    exact vertexDegree_eq_sum_ite E v
  rw [h_step1]
  rw [Finset.sum_comm]
  have h_step2 : (∑ e ∈ E, ∑ v : Fin n, (if v ∈ e then 1 else 0)) =
      ∑ e ∈ E, 2 := by
    apply Finset.sum_congr rfl
    intro e he
    have h_card := card_filter_mem_edge e (h_loopless e he)
    rw [Finset.card_eq_sum_ones] at h_card
    rw [← Finset.sum_filter]
    exact h_card
  rw [h_step2]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact Nat.mul_comm _ 2

/-!
## 10. Odd-Degree Vertices & Parity Conservation Invariant
-/

/-- Subset of vertices having odd degree in edge finset `E`. -/
def oddDegreeVertices {n : ℕ} (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.filter (fun v => vertexDegree E v % 2 = 1) Finset.univ

/-- Canonical mod-2 natural cast identity: natural numbers cast into `ZMod 2` coincide with their parity. -/
lemma nat_cast_zmod_two (m : ℕ) :
    ((m : ℕ) : ZMod 2) = if m % 2 = 1 then (1 : ZMod 2) else 0 := by
  have h_mod : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h_cast : ((m : ℕ) : ZMod 2) = (((m % 2) + 2 * (m / 2) : ℕ) : ZMod 2) :=
    congrArg Nat.cast (Nat.mod_add_div m 2).symm
  rw [h_cast, Nat.cast_add, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
  rw [h2, zero_mul, add_zero]
  rcases h_mod with h0 | h1
  · rw [h0]
    rfl
  · rw [h1]
    rfl

/-- Mod-2 sum decomposition: the mod-2 sum of vertex degrees equals the cardinality of
the odd-degree vertex set modulo 2. -/
lemma sum_mod_two_partition {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    ((∑ v : Fin n, vertexDegree E v : ℕ) : ZMod 2) = ((oddDegreeVertices E).card : ZMod 2) := by
  rw [Nat.cast_sum]
  have h_term : ∀ v : Fin n, ((vertexDegree E v : ℕ) : ZMod 2) =
      if vertexDegree E v % 2 = 1 then (1 : ZMod 2) else 0 := fun v => nat_cast_zmod_two (vertexDegree E v)
  have h_sum : (∑ v : Fin n, ((vertexDegree E v : ℕ) : ZMod 2)) =
      ∑ v : Fin n, if vertexDegree E v % 2 = 1 then (1 : ZMod 2) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    exact h_term v
  rw [h_sum]
  rw [← Finset.sum_filter]
  have h_ones : (∑ x ∈ Finset.filter (fun v => vertexDegree E v % 2 = 1) Finset.univ, (1 : ZMod 2)) =
      ((oddDegreeVertices E).card : ZMod 2) := by
    dsimp [oddDegreeVertices]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact h_ones

/-- Parity Conservation Theorem: in any loopless undirected graph, the number of
vertices with odd degree is strictly even. -/
theorem even_card_oddDegreeVertices {n : ℕ} (E : Finset (Sym2 (Fin n)))
    (h_loopless : IsLooplessEdges E) :
    Even (oddDegreeVertices E).card := by
  have h_hand := sum_vertexDegree_eq_two_card E h_loopless
  have h_mod := sum_mod_two_partition E
  have h_two : ((∑ v : Fin n, vertexDegree E v : ℕ) : ZMod 2) =
      ((2 * E.card : ℕ) : ZMod 2) := by rw [h_hand]
  have h_zero : ((2 * E.card : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
    rw [h2, zero_mul]
  rw [h_two, h_zero] at h_mod
  have h_val := congr_arg ZMod.val h_mod.symm
  rw [ZMod.val_zero, ZMod.val_natCast] at h_val
  exact Nat.even_iff.mpr h_val

/-- Specialization to spanning trees: the odd-degree vertex set of any loopless
spanning tree has strictly even cardinality. -/
theorem tree_even_card_oddDegreeVertices {n : ℕ} (T : SpanningTree n) :
    Even (oddDegreeVertices T.edges).card :=
  even_card_oddDegreeVertices T.edges T.loopless

/-!
## 11. Perfect Matchings & Matching Cardinality Invariant
-/

/-- Perfect matching on an arbitrary subset S of Fin n.
An undirected edge finset where every edge has endpoints in S, every vertex in S
is incident to exactly one edge, and all edges are loopless. -/
structure PerfectMatching {n : ℕ} (S : Finset (Fin n)) where
  edges : Finset (Sym2 (Fin n))
  endpoints_in : ∀ e ∈ edges, ∀ v ∈ e, v ∈ S
  incident_once : ∀ v ∈ S, (edges.filter (fun e => v ∈ e)).card = 1
  loopless : IsLooplessEdges edges

/-- Any perfect matching on S satisfies 2 * |M| = |S|. Proved by incidence matrix double counting. -/
lemma perfectMatching_card_two_mul {n : ℕ} {S : Finset (Fin n)} (M : PerfectMatching S) :
    2 * M.edges.card = S.card := by
  have h_sum : (∑ v ∈ S, (M.edges.filter (fun e => v ∈ e)).card) = ∑ v ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro v hv
    exact M.incident_once v hv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h_sum
  have h_double : (∑ v ∈ S, (M.edges.filter (fun e => v ∈ e)).card) =
      ∑ v ∈ S, ∑ e ∈ M.edges, (if v ∈ e then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter (fun e => v ∈ e) (fun _ => 1)
  rw [h_double] at h_sum
  rw [Finset.sum_comm] at h_sum
  have h_inner : ∀ e ∈ M.edges, (∑ v ∈ S, (if v ∈ e then 1 else 0)) = 2 := by
    intro e he
    have h_card := card_filter_mem_edge e (M.loopless e he)
    have h_eq : (S.filter (fun x => x ∈ e)) = (Finset.univ.filter (fun x => x ∈ e)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.2
      · intro hx; refine ⟨M.endpoints_in e he x hx, hx⟩
    rw [← h_eq] at h_card
    rw [Finset.card_eq_sum_ones] at h_card
    rw [← Finset.sum_filter]
    exact h_card
  have h_two : (∑ e ∈ M.edges, ∑ v ∈ S, (if v ∈ e then 1 else 0)) = ∑ e ∈ M.edges, 2 := by
    apply Finset.sum_congr rfl
    intro e he
    exact h_inner e he
  rw [h_two] at h_sum
  rw [Finset.sum_const, nsmul_eq_mul] at h_sum
  rw [mul_comm] at h_sum
  exact h_sum

/-- Minimum-weight perfect matching optimality predicate. -/
def IsMinWeightMatching {n : ℕ} (c : CostFunction n) (S : Finset (Fin n)) (M : PerfectMatching S) : Prop :=
  ∀ M' : PerfectMatching S, edgeSetCost c M.edges ≤ edgeSetCost c M'.edges

/-!
## 12. Tour Projection & Metric Cycle Shortcutting
-/

/-- Cycle projection operator filtering a tour to subset S. -/
def shortcutToSubset {n : ℕ} (p : List (Fin n)) (S : Finset (Fin n)) : List (Fin n) :=
  p.filter (fun v => v ∈ S)

lemma shortcutToSubset_nodup {n : ℕ} (p : List (Fin n)) (S : Finset (Fin n)) (hp : p.Nodup) :
    (shortcutToSubset p S).Nodup :=
  hp.filter (fun v => v ∈ S)

lemma mem_shortcutToSubset_iff {n : ℕ} (p : List (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    v ∈ shortcutToSubset p S ↔ v ∈ p ∧ v ∈ S := by
  dsimp [shortcutToSubset]
  simp

lemma mem_of_isTour {n : ℕ} (p : List (Fin n)) (hp : IsTour (completeGraph n) p) (v : Fin n) :
    v ∈ p := by
  have h_univ : p.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hp.2.1, hp.1, Fintype.card_fin]
  have : v ∈ p.toFinset := by rw [h_univ]; exact Finset.mem_univ v
  exact List.mem_toFinset.mp this

lemma mem_shortcutToSubset_of_isTour {n : ℕ} (p : List (Fin n)) (hp : IsTour (completeGraph n) p)
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) :
    v ∈ shortcutToSubset p S := by
  rw [mem_shortcutToSubset_iff]
  exact ⟨mem_of_isTour p hp v, hv⟩

lemma shortcutToSubset_length_eq {n : ℕ} (p : List (Fin n)) (hp : IsTour (completeGraph n) p)
    (S : Finset (Fin n)) :
    (shortcutToSubset p S).length = S.card := by
  have h_nodup : (shortcutToSubset p S).Nodup := shortcutToSubset_nodup p S hp.2.1
  rw [← List.toFinset_card_of_nodup h_nodup]
  have h_set : (shortcutToSubset p S).toFinset = S := by
    ext v
    simp only [List.mem_toFinset, mem_shortcutToSubset_iff]
    constructor
    · intro h; exact h.2
    · intro hv; exact ⟨mem_of_isTour p hp v, hv⟩
  rw [h_set]

lemma walkCost_append_singleton {n : ℕ} (c : CostFunction n) :
    ∀ (w : List (Fin n)) (x : Fin n) (h : w ≠ []),
    walkCost c (w ++ [x]) = walkCost c w + c (w.getLast h) x
  | [], x, h => by contradiction
  | [u], x, _ => by
    dsimp [walkCost]
    omega
  | u :: v :: vs, x, _ => by
    have h_ne : v :: vs ≠ [] := by simp
    have ih := walkCost_append_singleton c (v :: vs) x h_ne
    have h_step : (u :: v :: vs) ++ [x] = u :: v :: (vs ++ [x]) := rfl
    have h_step2 : v :: vs ++ [x] = v :: (vs ++ [x]) := rfl
    rw [h_step2] at ih
    rw [h_step, walkCost_cons_cons, ih, walkCost_cons_cons]
    have h_last : (u :: v :: vs).getLast (by simp) = (v :: vs).getLast h_ne := rfl
    rw [h_last]
    omega

lemma directedPathEdges_cost_eq_walkCost {n : ℕ} (c : CostFunction n) :
    ∀ (w : List (Fin n)), ((directedPathEdges w).map (fun e => c e.1 e.2)).sum = walkCost c w
  | [] => rfl
  | [_] => rfl
  | u :: v :: vs => by
    simp only [directedPathEdges, List.map_cons, List.sum_cons, walkCost_cons_cons]
    rw [directedPathEdges_cost_eq_walkCost c (v :: vs)]

lemma tourCost_eq_walkCost_append_head {n : ℕ} (c : CostFunction n) (x : Fin n) (xs : List (Fin n)) :
    tourCost c (x :: xs) = walkCost c (x :: xs ++ [x]) := by
  dsimp [tourCost]
  rw [cycleEdges_cons x xs]
  rw [List.map_append, List.sum_append]
  rw [directedPathEdges_cost_eq_walkCost]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have h_ne : x :: xs ≠ [] := by simp
  have h_app := walkCost_append_singleton c (x :: xs) x h_ne
  rw [← h_app]
  rfl

lemma walkCost_cons_le_cons {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (u v w : Fin n) (ws : List (Fin n)) :
    walkCost c (u :: w :: ws) ≤ walkCost c (u :: v :: w :: ws) := by
  rw [walkCost_cons_cons, walkCost_cons_cons, walkCost_cons_cons]
  have h_tri := hMetric.triangle u v w
  omega


lemma walkCost_filter_subwalk_le {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (S : Finset (Fin n)) (v : Fin n) :
    ∀ (ws : List (Fin n)) (u : Fin n),
    walkCost c (u :: (ws.filter (fun x => x ∈ S)) ++ [v]) ≤
    walkCost c (u :: ws ++ [v])
  | [], u => by
    dsimp [walkCost, List.filter]
    exact Nat.le_refl _
  | w :: rest, u => by
    by_cases hw : w ∈ S
    · have h_flt : (w :: rest).filter (fun x => x ∈ S) = w :: rest.filter (fun x => x ∈ S) := by
        apply List.filter_cons_of_pos
        simpa using hw
      rw [h_flt]
      have h1 : u :: (w :: rest.filter (fun x => x ∈ S)) ++ [v] =
          u :: w :: (rest.filter (fun x => x ∈ S) ++ [v]) := rfl
      have h2 : u :: (w :: rest) ++ [v] = u :: w :: (rest ++ [v]) := rfl
      rw [h1, h2, walkCost_cons_cons, walkCost_cons_cons]
      have ih := walkCost_filter_subwalk_le c hMetric S v rest w
      have h_app1 : w :: rest.filter (fun x => x ∈ S) ++ [v] =
          w :: (rest.filter (fun x => x ∈ S) ++ [v]) := rfl
      have h_app2 : w :: rest ++ [v] = w :: (rest ++ [v]) := rfl
      rw [h_app1, h_app2] at ih
      omega
    · have h_flt : (w :: rest).filter (fun x => x ∈ S) = rest.filter (fun x => x ∈ S) := by
        apply List.filter_cons_of_neg
        simpa using hw
      rw [h_flt]
      have ih := walkCost_filter_subwalk_le c hMetric S v rest u
      have h2 : u :: (w :: rest) ++ [v] = u :: w :: (rest ++ [v]) := rfl
      rw [h2, walkCost_cons_cons]
      cases rest with
      | nil =>
        dsimp [walkCost]
        have h_tri := hMetric.triangle u w v
        omega
      | cons w2 rest' =>
        have h_w_step : w :: (w2 :: rest' ++ [v]) = w :: w2 :: (rest' ++ [v]) := rfl
        rw [h_w_step, walkCost_cons_cons]
        have h_def : u :: (w2 :: rest') ++ [v] = u :: w2 :: (rest' ++ [v]) := rfl
        rw [h_def, walkCost_cons_cons] at ih
        have h_tri := hMetric.triangle u w w2
        omega

lemma tourCost_delete_head_step {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (px y : Fin n) (rest : List (Fin n))
    (h_tour_y : tourCost c (y :: rest) = walkCost c (y :: rest ++ [y]))
    (h_tour_pxy : tourCost c (px :: y :: rest) = walkCost c (px :: y :: rest ++ [px])) :
    tourCost c (y :: rest) ≤ tourCost c (px :: y :: rest) := by
  rw [h_tour_y, h_tour_pxy]
  have h_pxy_step : (px :: y :: rest) ++ [px] = px :: y :: (rest ++ [px]) := rfl
  have h_y_step : (y :: rest) ++ [px] = y :: (rest ++ [px]) := rfl
  have h_ne : y :: rest ≠ [] := by simp
  have h_app1 := walkCost_append_singleton c (y :: rest) y h_ne
  have h_app2 := walkCost_append_singleton c (y :: rest) px h_ne
  rw [h_pxy_step, walkCost_cons_cons, ← h_y_step, h_app2]
  have h_step_app1 : y :: rest ++ [y] = (y :: rest) ++ [y] := rfl
  rw [h_step_app1, h_app1]
  have h_tri := hMetric.triangle ((y :: rest).getLast h_ne) px y
  omega

/-- General metric cycle shortcutting: projecting any cycle to a subset never increases tour cost. -/
lemma shortcutToSubset_cost_le {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (S : Finset (Fin n)) :
    ∀ (p : List (Fin n)), tourCost c (shortcutToSubset p S) ≤ tourCost c p
  | [] => by
    dsimp [shortcutToSubset]
    exact Nat.le_refl _
  | [u] => by
    dsimp [shortcutToSubset]
    by_cases hu : u ∈ S
    · have : [u].filter (fun v => v ∈ S) = [u] := by
        simp [hu]
      rw [this]
    · have : [u].filter (fun v => v ∈ S) = [] := by
        simp [hu]
      rw [this]
      dsimp [tourCost, cycleEdges]
      exact Nat.zero_le _
  | px :: pxs => by
    by_cases hpx : px ∈ S
    · have h_flt : shortcutToSubset (px :: pxs) S = px :: (pxs.filter (fun x => x ∈ S)) := by
        dsimp [shortcutToSubset]
        exact List.filter_cons_of_pos (by simpa using hpx)
      rw [h_flt]
      rw [tourCost_eq_walkCost_append_head c px (pxs.filter (fun x => x ∈ S))]
      rw [tourCost_eq_walkCost_append_head c px pxs]
      exact walkCost_filter_subwalk_le c hMetric S px pxs px
    · have h_flt : shortcutToSubset (px :: pxs) S = shortcutToSubset pxs S := by
        dsimp [shortcutToSubset]
        exact List.filter_cons_of_neg (by simpa using hpx)
      rw [h_flt]
      cases h_pxs : pxs with
      | nil =>
        dsimp [shortcutToSubset]
        exact Nat.zero_le _
      | cons y rest =>
        have ih := shortcutToSubset_cost_le c hMetric S (y :: rest)
        have h_del := tourCost_delete_head_step c hMetric px y rest
          (tourCost_eq_walkCost_append_head c y rest)
          (tourCost_eq_walkCost_append_head c px (y :: rest))
        exact ih.trans h_del

/-- Metric shortcutting lemma on cycles: projecting any Hamiltonian tour to a subset S
never increases tour cost under metric triangle inequality. -/
lemma shortcutToSubset_cost_le_opt {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (p : List (Fin n)) (_hp : IsTour (completeGraph n) p) (S : Finset (Fin n)) :
    tourCost c (shortcutToSubset p S) ≤ tourCost c p :=
  shortcutToSubset_cost_le c hMetric S p



/-!
## 13. Alternating Matching Decomposition of Even Cycles
-/

/-- Extract alternating edge pairs starting at even indices. -/
def cyclePairs {α : Type*} : List α → List (Sym2 α)
  | [] => []
  | [_] => []
  | u :: v :: rest => s(u, v) :: cyclePairs rest

lemma cyclePairs_nil {α : Type*} : cyclePairs ([] : List α) = [] := rfl

lemma cyclePairs_singleton {α : Type*} (u : α) : cyclePairs [u] = [] := rfl

lemma cyclePairs_cons_cons {α : Type*} (u v : α) (rest : List α) :
    cyclePairs (u :: v :: rest) = s(u, v) :: cyclePairs rest := rfl

lemma cyclePairs_length {α : Type*} : ∀ (L : List α),
    2 * (cyclePairs L).length ≤ L.length
  | [] => by dsimp [cyclePairs]; omega
  | [u] => by dsimp [cyclePairs]; omega
  | u :: v :: rest => by
    dsimp [cyclePairs]
    have ih := cyclePairs_length rest
    omega

lemma cyclePairs_length_of_even {α : Type*} : ∀ {L : List α}, Even L.length →
    2 * (cyclePairs L).length = L.length
  | [], _ => rfl
  | [u], h => by
    exfalso
    simp at h
  | u :: v :: rest, h => by
    dsimp [cyclePairs]
    have h_even_rest : Even rest.length := by
      rcases h with ⟨k, hk⟩
      have hlen : (u :: v :: rest).length = rest.length + 2 := rfl
      rw [hlen] at hk
      cases k with
      | zero => omega
      | succ k' =>
        refine ⟨k', by omega⟩
    have ih := cyclePairs_length_of_even h_even_rest
    omega

lemma mem_cyclePairs_endpoints {α : Type*} : ∀ {L : List α} {e : Sym2 α},
    e ∈ cyclePairs L → ∀ x ∈ e, x ∈ L
  | [], e, he => by contradiction
  | [u], e, he => by contradiction
  | u :: v :: rest, e, he => by
    dsimp [cyclePairs] at he
    cases he with
    | head =>
      intro x hx
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.head _)
    | tail _ htail =>
      intro x hx
      have ih := mem_cyclePairs_endpoints htail x hx
      exact List.Mem.tail _ (List.Mem.tail _ ih)

lemma cyclePairs_loopless {n : ℕ} : ∀ {L : List (Fin n)}, L.Nodup →
    IsLooplessEdges (cyclePairs L).toFinset
  | [], _ => by
    intro e he
    rw [List.mem_toFinset] at he
    contradiction
  | [u], _ => by
    intro e he
    rw [cyclePairs, List.mem_toFinset] at he
    contradiction
  | u :: v :: rest, hnodup => by
    intro e he
    rw [List.mem_toFinset, cyclePairs_cons_cons] at he
    cases he with
    | head =>
      have hu_not_v : u ≠ v := by
        have hu_not_in := (List.nodup_cons.mp hnodup).1
        intro heq
        subst heq
        exact hu_not_in (List.Mem.head _)
      exact ⟨u, v, rfl, hu_not_v⟩
    | tail _ htail =>
      have hnodup_rest : rest.Nodup := by
        have h1 := (List.nodup_cons.mp hnodup).2
        exact (List.nodup_cons.mp h1).2
      have ih := cyclePairs_loopless hnodup_rest e (List.mem_toFinset.mpr htail)
      exact ih

lemma cyclePairs_incident_once {n : ℕ} : ∀ {L : List (Fin n)}, L.Nodup → Even L.length →
    ∀ x ∈ L.toFinset, (((cyclePairs L).toFinset).filter (fun e => x ∈ e)).card = 1
  | [], _, _, x, hx => by
    simp at hx
  | [u], _, h_even, _, _ => by
    exfalso
    simp at h_even
  | u :: v :: rest, hnodup, h_even, x, hx => by
    rw [List.mem_toFinset] at hx
    have hu_not_in : u ∉ v :: rest := (List.nodup_cons.mp hnodup).1
    have hv_not_in : v ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
    have hnodup_rest : rest.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).2
    have h_even_rest : Even rest.length := by
      rcases h_even with ⟨k, hk⟩
      have hlen : (u :: v :: rest).length = rest.length + 2 := rfl
      rw [hlen] at hk
      cases k with
      | zero => omega
      | succ k' =>
        refine ⟨k', by omega⟩
    dsimp [cyclePairs]
    cases hx with
    | head =>
      have h_in_uv : u ∈ (s(u, v) : Sym2 (Fin n)) := by simp
      have h_not_in_rest : ∀ e ∈ cyclePairs rest, u ∉ e := by
        intro e he hu_in_e
        have hu_in_rest := mem_cyclePairs_endpoints he u hu_in_e
        have hu_not_rest : u ∉ rest := fun h => hu_not_in (List.mem_cons_of_mem v h)
        exact hu_not_rest hu_in_rest
      have h_set : (((s(u, v) :: cyclePairs rest).toFinset).filter (fun e => u ∈ e)) = {s(u, v)} := by
        ext e
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | he, hu⟩
          · rfl
          · exfalso; exact h_not_in_rest e he hu
        · rintro rfl
          refine ⟨Or.inl rfl, h_in_uv⟩
      rw [h_set]
      exact Finset.card_singleton _
    | tail _ hx_tail =>
      cases hx_tail with
      | head =>
        have hv_in_uv : v ∈ (s(u, v) : Sym2 (Fin n)) := by simp
        have hv_not_in_rest : ∀ e ∈ cyclePairs rest, v ∉ e := by
          intro e he hv_in_e
          have hv_in_rest := mem_cyclePairs_endpoints he v hv_in_e
          exact hv_not_in hv_in_rest
        have h_set : (((s(u, v) :: cyclePairs rest).toFinset).filter (fun e => v ∈ e)) = {s(u, v)} := by
          ext e
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | he, hv⟩
            · rfl
            · exfalso; exact hv_not_in_rest e he hv
          · rintro rfl
            refine ⟨Or.inl rfl, hv_in_uv⟩
        rw [h_set]
        exact Finset.card_singleton _
      | tail _ hx_rest =>
        have hx_not_uv : x ∉ (s(u, v) : Sym2 (Fin n)) := by
          simp only [Sym2.mem_iff, not_or]
          constructor
          · intro hxu
            have hu_not_rest : u ∉ rest := fun h => hu_not_in (List.mem_cons_of_mem v h)
            have : u ∈ rest := by rwa [hxu] at hx_rest
            exact hu_not_rest this
          · intro hxv
            have hv_not_rest : v ∉ rest := hv_not_in
            have : v ∈ rest := by rwa [hxv] at hx_rest
            exact hv_not_rest this
        have ih := cyclePairs_incident_once hnodup_rest h_even_rest x (List.mem_toFinset.mpr hx_rest)
        have h_filter_eq : (((s(u, v) :: cyclePairs rest).toFinset).filter (fun e => x ∈ e)) =
            ((cyclePairs rest).toFinset.filter (fun e => x ∈ e)) := by
          ext e
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons]
          constructor
          · rintro ⟨rfl | he, hx_e⟩
            · exfalso; exact hx_not_uv hx_e
            · exact ⟨he, hx_e⟩
          · rintro ⟨he, hx_e⟩
            exact ⟨Or.inr he, hx_e⟩
        rw [h_filter_eq]
        exact ih

/-- First alternating matching of an even cycle covering subset S. -/
def evenCycleMatchingOne {n : ℕ} (cycle : List (Fin n)) (hEven : Even cycle.length)
    (hNodup : cycle.Nodup) (_hLen : 2 ≤ cycle.length) :
    PerfectMatching cycle.toFinset where
  edges := (cyclePairs cycle).toFinset
  endpoints_in := by
    intro e he v hv
    rw [List.mem_toFinset] at he
    have hv_in := mem_cyclePairs_endpoints he v hv
    exact List.mem_toFinset.mpr hv_in
  incident_once := by
    intro v hv
    exact cyclePairs_incident_once hNodup hEven v hv
  loopless := cyclePairs_loopless hNodup

/-- Cyclic rotation by shifting head to tail. -/
def cycleRotated {α : Type*} : List α → List α
  | [] => []
  | u :: rest => rest ++ [u]

lemma cycleRotated_length {α : Type*} : ∀ (L : List α), (cycleRotated L).length = L.length
  | [] => rfl
  | u :: rest => by
    dsimp [cycleRotated]
    rw [List.length_append, List.length_singleton]

lemma cycleRotated_nodup {α : Type*} : ∀ {L : List α}, L.Nodup → (cycleRotated L).Nodup
  | [], h => h
  | u :: rest, h => by
    dsimp [cycleRotated]
    have hu_not := (List.nodup_cons.mp h).1
    have hrest := (List.nodup_cons.mp h).2
    rw [List.nodup_append_comm]
    dsimp
    exact List.nodup_cons.mpr ⟨fun h => hu_not (by simpa using h), hrest⟩

lemma cycleRotated_toFinset {α : Type*} [DecidableEq α] : ∀ (L : List α), (cycleRotated L).toFinset = L.toFinset
  | [] => rfl
  | u :: rest => by
    dsimp [cycleRotated]
    ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons]
    tauto

/-- Second alternating matching of an even cycle covering subset S. -/
def evenCycleMatchingTwo {n : ℕ} (cycle : List (Fin n)) (hEven : Even cycle.length)
    (hNodup : cycle.Nodup) (_hLen : 2 ≤ cycle.length) :
    PerfectMatching cycle.toFinset where
  edges := (cyclePairs (cycleRotated cycle)).toFinset
  endpoints_in := by
    intro e he v hv
    rw [List.mem_toFinset] at he
    have hv_in := mem_cyclePairs_endpoints he v hv
    have h_in_rot : v ∈ (cycleRotated cycle).toFinset := List.mem_toFinset.mpr hv_in
    rwa [cycleRotated_toFinset] at h_in_rot
  incident_once := by
    intro v hv
    have h_rot_even : Even (cycleRotated cycle).length := by
      rw [cycleRotated_length]
      exact hEven
    have h_rot_nodup : (cycleRotated cycle).Nodup := cycleRotated_nodup hNodup
    have hv_rot : v ∈ (cycleRotated cycle).toFinset := by
      rwa [cycleRotated_toFinset]
    exact cyclePairs_incident_once h_rot_nodup h_rot_even v hv_rot
  loopless := by
    have h_rot_nodup : (cycleRotated cycle).Nodup := cycleRotated_nodup hNodup
    exact cyclePairs_loopless h_rot_nodup

lemma toFinset_sum_of_nodup {α : Type*} [DecidableEq α] {L : List α} (h : L.Nodup) (f : α → ℕ) :
    ∑ x ∈ L.toFinset, f x = (L.map f).sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp h).1
    have hxs : xs.Nodup := (List.nodup_cons.mp h).2
    rw [List.toFinset_cons, Finset.sum_insert, ih hxs, List.map_cons, List.sum_cons]
    rwa [List.mem_toFinset]

lemma cyclePairs_nodup {n : ℕ} : ∀ {L : List (Fin n)}, L.Nodup → (cyclePairs L).Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_nil
  | u :: v :: rest, h => by
    dsimp [cyclePairs]
    rw [List.nodup_cons]
    have hu_not_in : u ∉ v :: rest := (List.nodup_cons.mp h).1
    have hu_not_rest : u ∉ rest := fun hmem => hu_not_in (List.mem_cons_of_mem v hmem)
    have hnodup_rest : rest.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp h).2).2
    refine ⟨?_, cyclePairs_nodup hnodup_rest⟩
    intro he_in
    have hu_in_e : u ∈ (s(u, v) : Sym2 (Fin n)) := by simp
    have hu_in_rest := mem_cyclePairs_endpoints he_in u hu_in_e
    exact hu_not_rest hu_in_rest

/-- Helper: undirected cost of alternating pairs in a walk. -/
def pairsCost {n : ℕ} (c : CostFunction n) (L : List (Fin n)) : ℕ :=
  ((cyclePairs L).map (undirectedEdgeCost c)).sum

lemma pairsCost_nil {n : ℕ} (c : CostFunction n) : pairsCost c ([] : List (Fin n)) = 0 := rfl

lemma pairsCost_cons_cons {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (u v : Fin n) (rest : List (Fin n)) :
    pairsCost c (u :: v :: rest) = c u v + pairsCost c rest := by
  dsimp [pairsCost, cyclePairs, List.map, List.sum]
  rw [undirectedEdgeCost_metric c hMetric u v]

lemma walk_alternating_pairs_cost {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c) :
    ∀ (rest : List (Fin n)) (v u : Fin n),
    Even rest.length →
    pairsCost c rest + pairsCost c (v :: rest ++ [u]) = walkCost c (v :: rest ++ [u])
  | [], v, u, _ => by
    rw [pairsCost_nil, zero_add]
    have h_vu : v :: [] ++ [u] = [v, u] := rfl
    rw [h_vu]
    dsimp [pairsCost, cyclePairs, walkCost, List.map, List.sum]
    rw [undirectedEdgeCost_metric c hMetric v u]
  | [x], _, _, h => by
    exfalso
    simp at h
  | w :: z :: rest', v, u, h => by
    have h_even_rest' : Even rest'.length := by
      rcases h with ⟨k, hk⟩
      have : (w :: z :: rest').length = rest'.length + 2 := rfl
      rw [this] at hk
      cases k with
      | zero => omega
      | succ k' => refine ⟨k', by omega⟩
    have ih := walk_alternating_pairs_cost c hMetric rest' z u h_even_rest'
    rw [pairsCost_cons_cons c hMetric w z rest']
    have h_app : v :: (w :: z :: rest') ++ [u] = v :: w :: (z :: rest' ++ [u]) := rfl
    have h_app2 : z :: rest' ++ [u] = z :: (rest' ++ [u]) := rfl
    rw [h_app]
    have h_pairs : pairsCost c (v :: w :: (z :: rest' ++ [u])) =
        c v w + pairsCost c (z :: rest' ++ [u]) :=
      pairsCost_cons_cons c hMetric v w (z :: rest' ++ [u])
    rw [h_pairs]
    have h_walk : walkCost c (v :: w :: (z :: rest' ++ [u])) =
        c v w + (c w z + walkCost c (z :: rest' ++ [u])) := by
      rw [walkCost_cons_cons, h_app2, walkCost_cons_cons]
    rw [h_walk]
    omega

lemma pairsCost_sum_eq_tourCost {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (u v : Fin n) (rest : List (Fin n)) (hEven : Even (u :: v :: rest).length) :
    pairsCost c (u :: v :: rest) + pairsCost c (cycleRotated (u :: v :: rest)) =
    tourCost c (u :: v :: rest) := by
  have h_even_rest : Even rest.length := by
    rcases hEven with ⟨k, hk⟩
    have : (u :: v :: rest).length = rest.length + 2 := rfl
    rw [this] at hk
    cases k with
    | zero => omega
    | succ k' => refine ⟨k', by omega⟩
  have h_alt := walk_alternating_pairs_cost c hMetric rest v u h_even_rest
  rw [pairsCost_cons_cons c hMetric u v rest]
  dsimp [cycleRotated]
  rw [tourCost_eq_walkCost_append_head c u (v :: rest)]
  have h_walk : walkCost c (u :: v :: rest ++ [u]) = c u v + walkCost c (v :: rest ++ [u]) := by
    have h_app : u :: v :: rest ++ [u] = u :: v :: (rest ++ [u]) := rfl
    have h_v_app : v :: rest ++ [u] = v :: (rest ++ [u]) := rfl
    rw [h_app, h_v_app, walkCost_cons_cons]
  rw [h_walk]
  have h_rot_eq : v :: (rest ++ [u]) = v :: rest ++ [u] := rfl
  rw [h_rot_eq]
  omega

/-- Alternating matchings cost conservation identity: the sum of the costs of the two
alternating matchings M1 and M2 equals the tour cost of the even cycle. -/
lemma cycle_matchings_cost_sum {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (cycle : List (Fin n)) (hEven : Even cycle.length)
    (hNodup : cycle.Nodup) (hLen : 2 ≤ cycle.length) :
    edgeSetCost c (evenCycleMatchingOne cycle hEven hNodup hLen).edges +
    edgeSetCost c (evenCycleMatchingTwo cycle hEven hNodup hLen).edges = tourCost c cycle := by
  cases cycle with
  | nil => simp at hLen
  | cons u rest_u =>
    cases rest_u with
    | nil => simp at hLen
    | cons v rest =>
      dsimp [evenCycleMatchingOne, evenCycleMatchingTwo, edgeSetCost]
      have hnodup1 : (cyclePairs (u :: v :: rest)).Nodup := cyclePairs_nodup hNodup
      have hnodup2 : (cyclePairs (cycleRotated (u :: v :: rest))).Nodup :=
        cyclePairs_nodup (cycleRotated_nodup hNodup)
      rw [toFinset_sum_of_nodup hnodup1 (undirectedEdgeCost c)]
      rw [toFinset_sum_of_nodup hnodup2 (undirectedEdgeCost c)]
      change pairsCost c (u :: v :: rest) + pairsCost c (cycleRotated (u :: v :: rest)) =
        tourCost c (u :: v :: rest)
      exact pairsCost_sum_eq_tourCost c hMetric u v rest hEven

/-!
## 14. Master Matching Upper Bound Theorem (1/2-OPT Upper Bound)
-/

/-- Landmark 1/2-OPT Matching Bound: The cost of any minimum-weight perfect matching
on the odd-degree vertices of a spanning tree is bounded by half the optimal TSP tour cost.
In exact integer arithmetic: 2 * cost(M) ≤ OPT. -/
theorem matchingCost_le_half_OPT {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M) :
    2 * edgeSetCost c M.edges ≤ optTourCost c := by
  rcases exists_optTour hn c with ⟨p_opt, hp_opt, h_opt_cost⟩
  let O := oddDegreeVertices T.edges
  have h_card_two : 2 * M.edges.card = O.card := by
    change 2 * M.edges.card = (oddDegreeVertices T.edges).card
    exact perfectMatching_card_two_mul M
  rw [two_mul] at h_card_two
  by_cases hO_zero : O.card = 0
  · have h_M_zero : M.edges.card = 0 := by
      rw [hO_zero] at h_card_two
      omega
    have h_M_empty : M.edges = ∅ := Finset.card_eq_zero.mp h_M_zero
    rw [h_M_empty, edgeSetCost_empty]
    exact Nat.zero_le _
  · have h_M_ne_zero : M.edges.card ≠ 0 := by
      intro heq
      have : O.card = 0 := by
        rw [heq, add_zero] at h_card_two
        exact h_card_two.symm
      exact hO_zero this
    have hO_even : Even O.card := ⟨M.edges.card, h_card_two.symm⟩
    have hO_ge_two : 2 ≤ O.card := by
      have : 1 ≤ M.edges.card := Nat.one_le_iff_ne_zero.mpr h_M_ne_zero
      omega
    have hC_len : (shortcutToSubset p_opt O).length = O.card :=
      shortcutToSubset_length_eq p_opt hp_opt O
    have hC_nodup : (shortcutToSubset p_opt O).Nodup :=
      shortcutToSubset_nodup p_opt O hp_opt.2.1
    have hC_even : Even (shortcutToSubset p_opt O).length := by
      rw [hC_len]
      exact hO_even
    have hC_ge_two : 2 ≤ (shortcutToSubset p_opt O).length := by
      rw [hC_len]
      exact hO_ge_two
    have hC_set : (shortcutToSubset p_opt O).toFinset = O := by
      ext v
      simp only [List.mem_toFinset, mem_shortcutToSubset_iff]
      constructor
      · intro h; exact h.2
      · intro hv; exact ⟨mem_of_isTour p_opt hp_opt v, hv⟩
    let M1 := evenCycleMatchingOne (shortcutToSubset p_opt O) hC_even hC_nodup hC_ge_two
    let M2 := evenCycleMatchingTwo (shortcutToSubset p_opt O) hC_even hC_nodup hC_ge_two
    let M1_O : PerfectMatching O := {
      edges := M1.edges
      endpoints_in := by
        intro e he v hv
        have := M1.endpoints_in e he v hv
        rwa [hC_set] at this
      incident_once := by
        intro v hv
        have hv' : v ∈ (shortcutToSubset p_opt O).toFinset := by rwa [hC_set]
        exact M1.incident_once v hv'
      loopless := M1.loopless
    }
    let M2_O : PerfectMatching O := {
      edges := M2.edges
      endpoints_in := by
        intro e he v hv
        have := M2.endpoints_in e he v hv
        rwa [hC_set] at this
      incident_once := by
        intro v hv
        have hv' : v ∈ (shortcutToSubset p_opt O).toFinset := by rwa [hC_set]
        exact M2.incident_once v hv'
      loopless := M2.loopless
    }
    have h_min1 := hMin M1_O
    have h_min2 := hMin M2_O
    have h_sum_matchings : 2 * edgeSetCost c M.edges ≤
        edgeSetCost c M1_O.edges + edgeSetCost c M2_O.edges := by omega
    have h_cost_partition : edgeSetCost c M1_O.edges + edgeSetCost c M2_O.edges =
        tourCost c (shortcutToSubset p_opt O) :=
      cycle_matchings_cost_sum c hMetric (shortcutToSubset p_opt O) hC_even hC_nodup hC_ge_two
    have h_shortcut : tourCost c (shortcutToSubset p_opt O) ≤ tourCost c p_opt :=
      shortcutToSubset_cost_le_opt c hMetric p_opt hp_opt O
    rw [h_opt_cost] at h_shortcut
    rw [h_cost_partition] at h_sum_matchings
    exact h_sum_matchings.trans h_shortcut

/-- For any type `α` and function `f : α → ℕ`, if `α` is inhabited by `x₀`,
there exists an element `x : α` that minimizes `f`. -/
lemma exists_min_nat {α : Type*} (f : α → ℕ) (x₀ : α) :
    ∃ x : α, ∀ y : α, f x ≤ f y := by
  classical
  have h_ex : ∃ k : ℕ, ∃ x : α, f x = k := ⟨f x₀, x₀, rfl⟩
  rcases Nat.find_spec h_ex with ⟨x, hx⟩
  refine ⟨x, fun y => ?_⟩
  rw [hx]
  exact Nat.find_min' h_ex ⟨y, rfl⟩

/-- Constructive existence of a Minimum Spanning Tree for any graph with n ≥ 3. -/
theorem exists_mst {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :
    ∃ T : SpanningTree n, IsMST c T := by
  rcases exists_optTour hn c with ⟨p, hp, _⟩
  let T0 := tourToSpanningPath hn p hp
  exact exists_min_nat (fun T => edgeSetCost c T.edges) T0

/-- Constructive existence of a Minimum-Weight Perfect Matching on the odd-degree
vertices of any spanning tree for n ≥ 3. -/
theorem exists_minWeightMatching {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) (T : SpanningTree n) :
    ∃ M : PerfectMatching (oddDegreeVertices T.edges),
      IsMinWeightMatching c (oddDegreeVertices T.edges) M := by
  rcases exists_optTour hn c with ⟨p, hp, _⟩
  let O := oddDegreeVertices T.edges
  have h_witness : ∃ M0 : PerfectMatching O, True := by
    by_cases hO_zero : O.card = 0
    · have hO_empty : O = ∅ := Finset.card_eq_zero.mp hO_zero
      refine ⟨{
        edges := ∅
        endpoints_in := by
          intro e he v hv
          exact (Finset.notMem_empty e he).elim
        incident_once := by
          intro v hv
          rw [hO_empty] at hv
          exact (Finset.notMem_empty v hv).elim
        loopless := by
          intro e he
          exact (Finset.notMem_empty e he).elim
      }, trivial⟩
    · have hO_even : Even O.card := tree_even_card_oddDegreeVertices T
      have hO_ge_two : 2 ≤ O.card := by
        rcases hO_even with ⟨k, hk⟩
        omega
      have hC_len : (shortcutToSubset p O).length = O.card :=
        shortcutToSubset_length_eq p hp O
      have hC_nodup : (shortcutToSubset p O).Nodup :=
        shortcutToSubset_nodup p O hp.2.1
      have hC_even : Even (shortcutToSubset p O).length := by
        rw [hC_len]
        exact hO_even
      have hC_ge_two : 2 ≤ (shortcutToSubset p O).length := by
        rw [hC_len]
        exact hO_ge_two
      have hC_set : (shortcutToSubset p O).toFinset = O := by
        ext v
        simp only [List.mem_toFinset, mem_shortcutToSubset_iff]
        constructor
        · intro h; exact h.2
        · intro hv; exact ⟨mem_of_isTour p hp v, hv⟩
      let M1 := evenCycleMatchingOne (shortcutToSubset p O) hC_even hC_nodup hC_ge_two
      let M1_O : PerfectMatching O := {
        edges := M1.edges
        endpoints_in := by
          intro e he v hv
          have := M1.endpoints_in e he v hv
          rwa [hC_set] at this
        incident_once := by
          intro v hv
          have hv' : v ∈ (shortcutToSubset p O).toFinset := by rwa [hC_set]
          exact M1.incident_once v hv'
        loopless := M1.loopless
      }
      exact ⟨M1_O, trivial⟩
  rcases h_witness with ⟨M0, _⟩
  exact exists_min_nat (fun M => edgeSetCost c M.edges) M0

/-!
## 15. Eulerian Multigraphs & Degree Parity (Phase 5)

This section establishes multigraph edge multisets, the multigraph union of spanning tree
edges and odd-vertex matching edges $H = T \cup M$, and proves that every vertex degree
in $H$ is strictly even.
-/

/-- Multigraph represented as a multiset of undirected edges on `Fin n`. -/
abbrev MultigraphEdges (n : ℕ) := Multiset (Sym2 (Fin n))

/-- Disjoint multiset union of spanning tree edges and matching edges. -/
def multigraphUnion {n : ℕ} (E1 E2 : Finset (Sym2 (Fin n))) : MultigraphEdges n :=
  E1.val + E2.val

/-- Vertex degree in an undirected multigraph edge multiset. -/
def multigraphDegree {n : ℕ} (E : MultigraphEdges n) (v : Fin n) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- The multigraph degree in `multigraphUnion E1 E2` splits as the sum of vertex degrees. -/
lemma multigraphDegree_union {n : ℕ} (E1 E2 : Finset (Sym2 (Fin n))) (v : Fin n) :
    multigraphDegree (multigraphUnion E1 E2) v = vertexDegree E1 v + vertexDegree E2 v := by
  dsimp [multigraphDegree, multigraphUnion, vertexDegree]
  rw [Multiset.filter_add, Multiset.card_add]
  rfl

/-- For any perfect matching on subset `S`, the vertex degree is 1 if `v ∈ S` and 0 otherwise. -/
lemma perfectMatching_degree {n : ℕ} {S : Finset (Fin n)} (M : PerfectMatching S) (v : Fin n) :
    vertexDegree M.edges v = if v ∈ S then 1 else 0 := by
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte]
    exact M.incident_once v hv
  · simp only [hv, ↓reduceIte]
    dsimp [vertexDegree]
    have h_empty : M.edges.filter (fun e => v ∈ e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hve
      exact hv (M.endpoints_in e he v hve)
    rw [h_empty, Finset.card_empty]

/-- All vertices in the multigraph union `T ∪ M` have strictly even degree. -/
lemma multigraph_degree_even {n : ℕ} (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges)) (v : Fin n) :
    Even (multigraphDegree (multigraphUnion T.edges M.edges) v) := by
  rw [multigraphDegree_union, perfectMatching_degree]
  have h_odd_iff : v ∈ oddDegreeVertices T.edges ↔ vertexDegree T.edges v % 2 = 1 := by
    simp [oddDegreeVertices]
  by_cases hv : v ∈ oddDegreeVertices T.edges
  · simp only [hv, ↓reduceIte]
    rw [h_odd_iff] at hv
    have h_sum_mod : (vertexDegree T.edges v + 1) % 2 = 0 := by omega
    exact Nat.even_iff.mpr h_sum_mod
  · simp only [hv, ↓reduceIte]
    rw [h_odd_iff] at hv
    have h_mod : vertexDegree T.edges v % 2 = 0 := by omega
    rw [add_zero]
    exact Nat.even_iff.mpr h_mod

/-!
## 16. Eulerian Circuits & Traversal Cost Conservation (Phase 5)

This section defines certified Eulerian circuits traversing multigraph edges and proves
that the traversal cost of an Eulerian circuit on $T \cup M$ equals $c(T) + c(M)$.
-/

/-- Certified Eulerian circuit traversing every multigraph edge exactly once. -/
structure EulerianCircuit {n : ℕ} (E : MultigraphEdges n) where
  walk : List (Fin n)
  is_closed : walk.head? = walk.getLast?
  edge_multiset_eq : (pathEdges walk : Multiset (Sym2 (Fin n))) = E
  visits_all : ∀ v : Fin n, v ∈ walk

/-- Total cost of an edge multiset under cost function `c`. -/
def multisetCost {n : ℕ} (c : CostFunction n) (E : MultigraphEdges n) : ℕ :=
  (E.map (undirectedEdgeCost c)).sum

/-- Multiset cost distributes over multiset addition. -/
lemma multisetCost_add {n : ℕ} (c : CostFunction n) (A B : MultigraphEdges n) :
    multisetCost c (A + B) = multisetCost c A + multisetCost c B := by
  dsimp [multisetCost]
  rw [Multiset.map_add, Multiset.sum_add]

/-- Multiset cost on a finset multiset value equals the standard edgeSetCost. -/
lemma multisetCost_finset {n : ℕ} (c : CostFunction n) (E : Finset (Sym2 (Fin n))) :
    multisetCost c E.val = edgeSetCost c E := by
  dsimp [multisetCost, edgeSetCost]

/-- Walk traversal cost equals the sum of undirected edge costs along consecutive path edges. -/
lemma walkCost_eq_pathEdges_cost {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c) :
    ∀ (w : List (Fin n)), walkCost c w = ((pathEdges w).map (undirectedEdgeCost c)).sum
  | [] => rfl
  | [_] => rfl
  | u :: v :: vs => by
    dsimp [walkCost, pathEdges]
    rw [List.map_cons, List.sum_cons]
    rw [undirectedEdgeCost_metric c hMetric u v]
    rw [walkCost_eq_pathEdges_cost c hMetric (v :: vs)]

/-- Lifting a list of edges to a multiset preserves total edge cost. -/
lemma multisetCost_coe {n : ℕ} (c : CostFunction n) (l : List (Sym2 (Fin n))) :
    multisetCost c (l : MultigraphEdges n) = (l.map (undirectedEdgeCost c)).sum := rfl

/-- Cost of the Eulerian circuit equals tree cost plus matching cost. -/
lemma circuitCost_eq_treeCost_add_matchingCost {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    walkCost c W.walk = edgeSetCost c T.edges + edgeSetCost c M.edges := by
  have h_walk := walkCost_eq_pathEdges_cost c hMetric W.walk
  rw [h_walk]
  have h_coe : ((pathEdges W.walk).map (undirectedEdgeCost c)).sum =
      multisetCost c (pathEdges W.walk : MultigraphEdges n) := by
    rw [multisetCost_coe]
  rw [h_coe, W.edge_multiset_eq]
  dsimp [multigraphUnion]
  rw [multisetCost_add, multisetCost_finset, multisetCost_finset]

/-!
## 17. Metric Shortcutting Operator & Tour Validity (Phase 5)

This section formalizes the canonical first-visit metric shortcutting operator
`shortcutCircuit` and proves that shortcutting any Eulerian circuit produces
a certified Hamiltonian tour on `completeGraph n`.
-/

/-- Canonical shortcutting operator keeping only first vertex visits. -/
def shortcutCircuit {n : ℕ} (w : List (Fin n)) : List (Fin n) :=
  (w.dropLast).eraseDups

/-- Deduplication via `List.eraseDups` yields a sublist of the original list. -/
lemma eraseDups_sublist {α : Type*} [DecidableEq α] (l : List α) :
    l.eraseDups.Sublist l := by
  match l with
  | [] =>
    exact List.Sublist.slnil
  | x :: xs =>
    rw [List.eraseDups_cons]
    have h_sub : (xs.filter (fun b => !b == x)).Sublist xs := List.filter_sublist
    have ih := eraseDups_sublist (xs.filter (fun b => !b == x))
    have h_trans := ih.trans h_sub
    exact List.Sublist.cons_cons x h_trans
termination_by l.length
decreasing_by
  simp_wf
  have h_len := (List.filter_sublist (p := fun b => !b == x) (l := xs)).length_le
  omega

/-- Deduplication via `List.eraseDups` produces a duplicate-free list. -/
lemma eraseDups_nodup {α : Type*} [DecidableEq α] (l : List α) :
    l.eraseDups.Nodup := by
  match l with
  | [] =>
    exact List.nodup_nil
  | x :: xs =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hx
      rw [List.mem_eraseDups] at hx
      rw [List.mem_filter] at hx
      have h2 := hx.2
      simp only [beq_self_eq_true, Bool.not_true] at h2
      contradiction
    · exact eraseDups_nodup (xs.filter (fun b => !b == x))
termination_by l.length
decreasing_by
  simp_wf
  have h_len := (List.filter_sublist (p := fun b => !b == x) (l := xs)).length_le
  omega

/-- Any member of a list distinct from the last element belongs to `dropLast`. -/
lemma mem_dropLast_of_mem_ne_getLast {α : Type*} {l : List α} (h_ne : l ≠ [])
    {v : α} (h_mem : v ∈ l) (h_neq : v ≠ l.getLast h_ne) :
    v ∈ l.dropLast := by
  have h_split : l = l.dropLast ++ [l.getLast h_ne] := (List.dropLast_append_getLast h_ne).symm
  have h_mem' : v ∈ l.dropLast ++ [l.getLast h_ne] := by rwa [← h_split]
  rw [List.mem_append, List.mem_singleton] at h_mem'
  cases h_mem' with
  | inl h => exact h
  | inr h => contradiction

/-- For any list of length at least 2, the head element belongs to `dropLast`. -/
lemma head_mem_dropLast_of_length_ge_two {α : Type*} {l : List α} (h : 2 ≤ l.length) :
    ∀ (h_ne : l ≠ []), l.head h_ne ∈ l.dropLast := by
  intro h_ne
  cases l with
  | nil => contradiction
  | cons y ys =>
    cases ys with
    | nil =>
      dsimp [List.length] at h
      omega
    | cons z zs =>
      dsimp [List.dropLast]
      exact List.Mem.head _

/-- Shortcutting an Eulerian circuit visiting all vertices yields a valid Hamiltonian tour. -/
lemma shortcutCircuit_isTour {n : ℕ} (hn : 3 ≤ n) (E : MultigraphEdges n)
    (W : EulerianCircuit E) :
    IsTour (completeGraph n) (shortcutCircuit W.walk) := by
  have h_nodup : (shortcutCircuit W.walk).Nodup := by
    dsimp [shortcutCircuit]
    exact eraseDups_nodup (W.walk.dropLast)
  have h_ne : W.walk ≠ [] := by
    intro h_empty
    have := W.visits_all ⟨0, by omega⟩
    rw [h_empty] at this
    contradiction
  have h_len : 2 ≤ W.walk.length := by
    have h_toFinset : W.walk.toFinset = (Finset.univ : Finset (Fin n)) := by
      ext v
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact W.visits_all v
    have h_card : W.walk.toFinset.card = n := by
      rw [h_toFinset, Finset.card_univ, Fintype.card_fin]
    have h_le := List.toFinset_card_le W.walk
    omega
  have h_head_eq : W.walk.head h_ne = W.walk.getLast h_ne := by
    have h_head? := List.head?_eq_some_head h_ne
    have h_last? := List.getLast?_eq_some_getLast h_ne
    have h_cl := W.is_closed
    rw [h_head?, h_last?] at h_cl
    exact Option.some.inj h_cl
  have h_all : ∀ v : Fin n, v ∈ shortcutCircuit W.walk := by
    intro v
    dsimp [shortcutCircuit]
    rw [List.mem_eraseDups]
    by_cases h_last : v = W.walk.getLast h_ne
    · rw [h_last, ← h_head_eq]
      exact head_mem_dropLast_of_length_ge_two h_len h_ne
    · exact mem_dropLast_of_mem_ne_getLast h_ne (W.visits_all v) h_last
  have h_perm : (shortcutCircuit W.walk).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup h_nodup (List.nodup_finRange n)).mpr
    intro a
    simp only [h_all a, List.mem_finRange]
  have h_mem_all : shortcutCircuit W.walk ∈ allTours n := by
    dsimp [allTours]
    exact List.mem_permutations.mpr h_perm
  exact isTour_completeGraph_of_mem_allTours hn h_mem_all

/-!
## 18. Metric Shortcutting Contraction Lemma (Phase 5)

This section proves the sublist walk contraction inequality under metric costs,
establishing that shortcutting a closed walk never increases traversal cost.
-/

/-- Dropping the first intermediate vertex along a walk never increases traversal cost. -/
lemma walkCost_drop_first {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c)
    (u x : Fin n) (l : List (Fin n)) (v : Fin n) :
    walkCost c (u :: l ++ [v]) ≤ walkCost c (u :: x :: l ++ [v]) := by
  cases l with
  | nil =>
    dsimp [walkCost]
    have h_tri := hMetric.triangle u x v
    omega
  | cons y ys =>
    have h1 : u :: (y :: ys) ++ [v] = u :: y :: (ys ++ [v]) := rfl
    have h2 : u :: x :: (y :: ys) ++ [v] = u :: x :: y :: (ys ++ [v]) := rfl
    rw [h1, h2]
    exact walkCost_cons_le_cons c hMetric u x y (ys ++ [v])

/-- Sublist Walk Contraction Lemma: For any sublist `l' <+ l`, the walk from `u` through `l'` to `v`
has cost at most the walk through `l`. -/
lemma walkCost_sublist_le {n : ℕ} (c : CostFunction n) (hMetric : IsMetricCost c) :
    ∀ {l' l : List (Fin n)}, l'.Sublist l →
    ∀ (u v : Fin n), walkCost c (u :: l' ++ [v]) ≤ walkCost c (u :: l ++ [v])
  | _, _, List.Sublist.slnil, u, v => Nat.le_refl _
  | _, _, @List.Sublist.cons _ l₁ l₂ a hsub, u, v => by
    have ih := walkCost_sublist_le c hMetric hsub u v
    have h_drop := walkCost_drop_first c hMetric u a l₂ v
    exact ih.trans h_drop
  | _, _, @List.Sublist.cons_cons _ l₁ l₂ a hsub, u, v => by
    have h1 : u :: (a :: l₁) ++ [v] = u :: a :: (l₁ ++ [v]) := rfl
    have h2 : u :: (a :: l₂) ++ [v] = u :: a :: (l₂ ++ [v]) := rfl
    rw [h1, h2, walkCost_cons_cons, walkCost_cons_cons]
    have ih : walkCost c (a :: (l₁ ++ [v])) ≤ walkCost c (a :: (l₂ ++ [v])) :=
      walkCost_sublist_le c hMetric hsub a v
    omega

/-- Shortcutting helper: for any non-empty closed walk `x :: xs` returning to `x`, shortcutting does not increase cost. -/
lemma shortcut_tourCost_le_circuitCost_aux {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (x : Fin n) (xs : List (Fin n))
    (h_last : (x :: xs).getLast (by simp) = x) :
    tourCost c (shortcutCircuit (x :: xs)) ≤ walkCost c (x :: xs) := by
  cases xs with
  | nil =>
    dsimp [shortcutCircuit, tourCost, cycleEdges, walkCost]
    exact Nat.zero_le _
  | cons y ys =>
    have h_drop : (x :: y :: ys).dropLast = x :: (y :: ys).dropLast := rfl
    dsimp [shortcutCircuit]
    rw [h_drop]
    rw [List.eraseDups_cons]
    let rest := (y :: ys).dropLast
    let l' := (rest.filter (fun b => !b == x)).eraseDups
    have h_tour : tourCost c (x :: l') = walkCost c (x :: l' ++ [x]) :=
      tourCost_eq_walkCost_append_head c x l'
    rw [h_tour]
    have h_sub_flt : l'.Sublist (rest.filter (fun b => !b == x)) := eraseDups_sublist _
    have h_flt_sub : (rest.filter (fun b => !b == x)).Sublist rest := List.filter_sublist
    have h_sub : l'.Sublist rest := h_sub_flt.trans h_flt_sub
    have h_le := walkCost_sublist_le c hMetric h_sub x x
    have h_rec := List.dropLast_append_getLast (l := y :: ys) (by simp)
    have h_last_eq : (y :: ys).getLast (by simp) = x := by
      have h_last_full : (x :: y :: ys).getLast (by simp) = (y :: ys).getLast (by simp) := rfl
      rw [← h_last_full, h_last]
    rw [h_last_eq] at h_rec
    have h_app : x :: rest ++ [x] = x :: (rest ++ [x]) := rfl
    rw [h_rec] at h_app
    rw [h_app] at h_le
    exact h_le

/-- Shortcutting any closed walk never increases tour cost beyond the walk traversal cost. -/
theorem shortcutCircuit_cost_le_walkCost {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (w : List (Fin n)) (h_closed : w.head? = w.getLast?) :
    tourCost c (shortcutCircuit w) ≤ walkCost c w := by
  cases w with
  | nil =>
    dsimp [shortcutCircuit, tourCost, cycleEdges, walkCost]
    exact Nat.zero_le _
  | cons x xs =>
    have h_last : (x :: xs).getLast (by simp) = x := by
      have h_head? : (x :: xs).head? = some x := rfl
      have h_last? : (x :: xs).getLast? = some ((x :: xs).getLast (by simp)) :=
        List.getLast?_eq_some_getLast (by simp)
      rw [h_head?, h_last?] at h_closed
      exact (Option.some.inj h_closed).symm
    exact shortcut_tourCost_le_circuitCost_aux c hMetric x xs h_last

/-- Master Shortcutting Lemma: Metric shortcutting never increases traversal cost. -/
theorem shortcut_tourCost_le_circuitCost {n : ℕ} (c : CostFunction n)
    (hMetric : IsMetricCost c) (E : MultigraphEdges n) (W : EulerianCircuit E) :
    tourCost c (shortcutCircuit W.walk) ≤ walkCost c W.walk :=
  shortcutCircuit_cost_le_walkCost c hMetric W.walk W.is_closed

/-!
## 19. Master Christofides 3/2-Approximation Guarantee (Phase 6)

This section synthesizes the landmark 3/2-approximation guarantee for Christofides-Serdyukov
algorithm, establishing the ratio in both exact integer arithmetic ($2 \cdot \text{cost} \le 3 \cdot \text{OPT}$)
and real arithmetic ($\text{cost} \le \frac{3}{2}\text{OPT}$).
-/

/-- Master Approximation Theorem on Eulerian Multigraph Circuit (Exact Integer Scaling):
Shortcutting the Eulerian circuit of T ∪ M achieves a 3/2-approximation factor. -/
theorem christofides_circuit_approx_ratio_nat {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n) (hMST : IsMST c T)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M)
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    2 * tourCost c (shortcutCircuit W.walk) ≤ 3 * optTourCost c := by
  have h_short : tourCost c (shortcutCircuit W.walk) ≤ walkCost c W.walk :=
    shortcut_tourCost_le_circuitCost c hMetric (multigraphUnion T.edges M.edges) W
  have h_circ : walkCost c W.walk = edgeSetCost c T.edges + edgeSetCost c M.edges :=
    circuitCost_eq_treeCost_add_matchingCost c hMetric T M W
  have h_mst : edgeSetCost c T.edges ≤ optTourCost c :=
    MSTCost_le_OPT hn c T hMST
  have h_match : 2 * edgeSetCost c M.edges ≤ optTourCost c :=
    matchingCost_le_half_OPT hn c hMetric T M hMin
  have h_mult : 2 * walkCost c W.walk = 2 * edgeSetCost c T.edges + 2 * edgeSetCost c M.edges := by
    rw [h_circ]
    omega
  have h_bound : 2 * walkCost c W.walk ≤ 3 * optTourCost c := by
    rw [h_mult]
    omega
  have h_two_short : 2 * tourCost c (shortcutCircuit W.walk) ≤ 2 * walkCost c W.walk := by
    omega
  exact h_two_short.trans h_bound

/-- Master Approximation Theorem on Eulerian Multigraph Circuit (Real Arithmetic):
The shortcut tour cost is bounded by (3/2) * OPT. -/
theorem christofides_circuit_approx_ratio {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (T : SpanningTree n) (hMST : IsMST c T)
    (M : PerfectMatching (oddDegreeVertices T.edges))
    (hMin : IsMinWeightMatching c (oddDegreeVertices T.edges) M)
    (W : EulerianCircuit (multigraphUnion T.edges M.edges)) :
    (tourCost c (shortcutCircuit W.walk) : ℝ) ≤ (3 / 2) * (optTourCost c : ℝ) := by
  have h_nat := christofides_circuit_approx_ratio_nat hn c hMetric T hMST M hMin W
  have h_cast : ((2 * tourCost c (shortcutCircuit W.walk) : ℕ) : ℝ) ≤
      ((3 * optTourCost c : ℕ) : ℝ) := Nat.cast_le.mpr h_nat
  push_cast at h_cast
  linarith

/-- Certificate packaging the components of the Christofides-Serdyukov 3/2-approximation algorithm. -/
structure ChristofidesCertificate (n : ℕ) (c : CostFunction n) where
  tree : SpanningTree n
  tree_mst : IsMST c tree
  matching : PerfectMatching (oddDegreeVertices tree.edges)
  matching_min : IsMinWeightMatching c (oddDegreeVertices tree.edges) matching
  eulerian : EulerianCircuit (multigraphUnion tree.edges matching.edges)

/-- Construct the Christofides tour by shortcutting the certificate's Eulerian circuit. -/
def christofidesTour {n : ℕ} {c : CostFunction n}
    (cert : ChristofidesCertificate n c) : List (Fin n) :=
  shortcutCircuit cert.eulerian.walk

/-- The Christofides tour is guaranteed to be a valid Hamiltonian tour on completeGraph n. -/
theorem christofides_is_tour {n : ℕ} (hn : 3 ≤ n) {c : CostFunction n}
    (cert : ChristofidesCertificate n c) :
    IsTour (completeGraph n) (christofidesTour cert) :=
  shortcutCircuit_isTour hn (multigraphUnion cert.tree.edges cert.matching.edges) cert.eulerian

/-- Master Approximation Theorem (Integer Scaling): 2 * cost(π) ≤ 3 * OPT. -/
theorem christofides_approx_ratio_nat {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (cert : ChristofidesCertificate n c) :
    2 * tourCost c (christofidesTour cert) ≤ 3 * optTourCost c :=
  christofides_circuit_approx_ratio_nat hn c hMetric cert.tree cert.tree_mst cert.matching cert.matching_min cert.eulerian

/-- Master Approximation Theorem (Real Arithmetic): cost(π) ≤ (3/2) * OPT. -/
theorem christofides_approx_ratio {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) (cert : ChristofidesCertificate n c) :
    (tourCost c (christofidesTour cert) : ℝ) ≤ (3 / 2) * (optTourCost c : ℝ) :=
  christofides_circuit_approx_ratio hn c hMetric cert.tree cert.tree_mst cert.matching cert.matching_min cert.eulerian

/-!
## 20. Eulerian Circuit Existence Bridge & Algorithm Synthesis (Phase 6)

This section establishes the Eulerian circuit existence bridge on connected even-degree multigraphs,
synthesizes complete Christofides certificates from the minimum spanning tree and minimum-weight
perfect matching, and proves the landmark 3/2-approximation guarantee for synthesized tours.
-/

/-- Finite multigraph Eulerian walk induction interface.
Any multigraph formed as multigraphUnion E1 E2 on Fin n whose first component E1 is connected,
both components are loopless, and every vertex has even multigraph degree admits an Eulerian circuit. -/
def EulerianWalkInduction (n : ℕ) : Prop :=
  ∀ (E1 E2 : Finset (Sym2 (Fin n))),
    (∀ u v : Fin n, ConnectedInEdges E1 u v) →
    IsLooplessEdges E1 →
    IsLooplessEdges E2 →
    (∀ v : Fin n, Even (multigraphDegree (multigraphUnion E1 E2) v)) →
    Nonempty (EulerianCircuit (multigraphUnion E1 E2))

/-- Predicate asserting that every edge in a multigraph edge multiset connects two distinct vertices. -/
def IsLooplessMultiset {n : ℕ} (E : MultigraphEdges n) : Prop :=
  ∀ e ∈ E, ∃ x y : Fin n, e = s(x, y) ∧ x ≠ y

/-- The multigraph union of two loopless edge sets is loopless. -/
lemma isLooplessMultiset_union {n : ℕ} {E1 E2 : Finset (Sym2 (Fin n))}
    (h1 : IsLooplessEdges E1) (h2 : IsLooplessEdges E2) :
    IsLooplessMultiset (multigraphUnion E1 E2) := by
  intro e he
  dsimp [multigraphUnion] at he
  rw [Multiset.mem_add] at he
  rcases he with he1 | he2
  · exact h1 e he1
  · exact h2 e he2

/-- Any submultiset of a loopless multigraph edge multiset is loopless. -/
lemma isLooplessMultiset_of_le {n : ℕ} {A B : MultigraphEdges n}
    (h_le : A ≤ B) (hB : IsLooplessMultiset B) : IsLooplessMultiset A :=
  fun e he => hB e (Multiset.mem_of_le h_le he)

/-- Multigraph degree is additive over multiset addition. -/
lemma multigraphDegree_add {n : ℕ} (A B : MultigraphEdges n) (v : Fin n) :
    multigraphDegree (A + B) v = multigraphDegree A v + multigraphDegree B v := by
  dsimp [multigraphDegree]
  rw [Multiset.filter_add, Multiset.card_add]

/-- Multigraph degree conservation under multiset subtraction (`A ≤ B`). -/
lemma multigraphDegree_sub_of_le {n : ℕ} {A B : MultigraphEdges n}
    (h : A ≤ B) (v : Fin n) :
    multigraphDegree (B - A) v + multigraphDegree A v = multigraphDegree B v := by
  rw [← multigraphDegree_add, Multiset.sub_add_cancel h]

/-- Multigraph degree of the empty multiset is zero. -/
lemma multigraphDegree_zero {n : ℕ} (v : Fin n) :
    multigraphDegree (0 : MultigraphEdges n) v = 0 := rfl

/-- Multigraph degree upon inserting a single undirected edge `e`. -/
lemma multigraphDegree_cons {n : ℕ} (e : Sym2 (Fin n)) (E : MultigraphEdges n) (v : Fin n) :
    multigraphDegree (e ::ₘ E) v = (if v ∈ e then 1 else 0) + multigraphDegree E v := by
  dsimp [multigraphDegree]
  rw [Multiset.filter_cons]
  split_ifs <;> simp [Nat.add_comm]

/-- Incidence indicator decomposition for a loopless undirected edge `s(u, w)` (`u ≠ w`). -/
lemma mem_sym2_ite_of_ne {n : ℕ} {u w : Fin n} (hne : u ≠ w) (v : Fin n) :
    (if v ∈ (s(u, w) : Sym2 (Fin n)) then 1 else 0) =
      (if v = u then 1 else 0) + (if v = w then 1 else 0) := by
  simp only [Sym2.mem_iff]
  by_cases hvu : v = u
  · subst hvu
    simp [hne]
  · by_cases hvw : v = w
    · subst hvw
      simp [hvu]
    · simp [hvu, hvw]

/-- Edge list decomposition across an internal vertex `u` in a concatenated walk `s ++ u :: t`. -/
lemma pathEdges_append_cons {α : Type*} :
    ∀ (s : List α) (u : α) (t : List α),
      pathEdges (s ++ u :: t) = pathEdges (s ++ [u]) ++ pathEdges (u :: t)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: s, u, t => by
    change s(a, b) :: pathEdges ((b :: s) ++ u :: t) =
      s(a, b) :: (pathEdges ((b :: s) ++ [u]) ++ pathEdges (u :: t))
    rw [pathEdges_append_cons (b :: s) u t]

/-- Appending a single step `z` to a non-empty walk `u :: ws` appends the terminal edge `s(last, z)`. -/
lemma pathEdges_snoc {α : Type*} :
    ∀ (u : α) (ws : List α) (z : α),
      pathEdges (u :: (ws ++ [z])) =
        pathEdges (u :: ws) ++ [s((u :: ws).getLast (List.cons_ne_nil _ _), z)]
  | u, [], z => rfl
  | u, w :: rest, z => by
    change s(u, w) :: pathEdges (w :: (rest ++ [z])) =
      s(u, w) :: pathEdges (w :: rest) ++ [s((w :: rest).getLast (List.cons_ne_nil _ _), z)]
    rw [pathEdges_snoc w rest z, List.cons_append]

/-- Parity invariant for any loopless walk `u :: ws`: the multigraph degree of vertex `v` modulo 2
equals the sum of endpoint indicators at the start vertex `u` and terminal vertex `getLast`. -/
lemma walk_degree_mod_two {n : ℕ} :
    ∀ (u : Fin n) (ws : List (Fin n)),
      IsLooplessMultiset (pathEdges (u :: ws) : MultigraphEdges n) →
      ∀ v : Fin n,
        multigraphDegree (pathEdges (u :: ws) : MultigraphEdges n) v % 2 =
          ((if v = u then 1 else 0) + (if v = (u :: ws).getLast (by simp) then 1 else 0)) % 2
  | u, [], _, v => by
    have h0 : multigraphDegree (pathEdges [u] : MultigraphEdges n) v = 0 := rfl
    rw [h0]
    have hlast : ([u].getLast (by simp)) = u := rfl
    rw [hlast]
    omega
  | u, w :: rest, hloop, v => by
    have h_head_mem : s(u, w) ∈ (pathEdges (u :: w :: rest) : MultigraphEdges n) := by
      dsimp [pathEdges]
      exact Multiset.mem_coe.mpr List.mem_cons_self
    rcases hloop s(u, w) h_head_mem with ⟨x, y, hxy_eq, hxy_ne⟩
    have huw_ne : u ≠ w := by
      intro heq
      subst heq
      have hx_mem : x ∈ (s(u, u) : Sym2 (Fin n)) := by
        rw [hxy_eq]
        exact Sym2.mem_mk_left x y
      have hy_mem : y ∈ (s(u, u) : Sym2 (Fin n)) := by
        rw [hxy_eq]
        exact Sym2.mem_mk_right x y
      simp only [Sym2.mem_iff, or_self] at hx_mem hy_mem
      exact hxy_ne (hx_mem.trans hy_mem.symm)
    have hloop_tail : IsLooplessMultiset (pathEdges (w :: rest) : MultigraphEdges n) := by
      intro e he
      exact hloop e (Multiset.mem_cons_of_mem he)
    have ih := walk_degree_mod_two w rest hloop_tail v
    have h_deg : multigraphDegree (pathEdges (u :: w :: rest) : MultigraphEdges n) v =
        (if v ∈ (s(u, w) : Sym2 (Fin n)) then 1 else 0) +
          multigraphDegree (pathEdges (w :: rest) : MultigraphEdges n) v := by
      change multigraphDegree (s(u, w) ::ₘ (pathEdges (w :: rest) : MultigraphEdges n)) v = _
      exact multigraphDegree_cons s(u, w) _ v
    rw [h_deg, mem_sym2_ite_of_ne huw_ne v]
    have hlast : (u :: w :: rest).getLast (by simp) = (w :: rest).getLast (by simp) := rfl
    rw [hlast]
    omega

/-- Any vertex `b` of positive multigraph degree in a loopless multigraph has an incident edge `s(b, z)` (`b ≠ z`). -/
lemma exists_incident_edge_of_pos_degree {n : ℕ} {E : MultigraphEdges n} {b : Fin n}
    (hloop : IsLooplessMultiset E) (hpos : 0 < multigraphDegree E b) :
    ∃ z : Fin n, b ≠ z ∧ s(b, z) ∈ E := by
  dsimp [multigraphDegree] at hpos
  rcases Multiset.card_pos_iff_exists_mem.mp hpos with ⟨e, he_filt⟩
  rw [Multiset.mem_filter] at he_filt
  rcases he_filt with ⟨he_mem, hb_in_e⟩
  rcases hloop e he_mem with ⟨x, y, rfl, hxy_ne⟩
  rw [Sym2.mem_iff] at hb_in_e
  rcases hb_in_e with rfl | rfl
  · exact ⟨y, hxy_ne, he_mem⟩
  · refine ⟨x, hxy_ne.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact he_mem

/-- Adding a single residual edge `e ∈ R - A` to a submultiset `A ≤ R` preserves `A + {e} ≤ R`. -/
lemma multiset_add_singleton_le_of_mem_sub {n : ℕ} {A R : MultigraphEdges n} {e : Sym2 (Fin n)}
    (hle : A ≤ R) (he : e ∈ R - A) :
    A + {e} ≤ R := by
  rw [Multiset.le_iff_count] at hle ⊢
  intro a
  have h_le_a := hle a
  rw [Multiset.count_add]
  have he_cnt : 0 < Multiset.count e (R - A) := Multiset.count_pos.mpr he
  rw [Multiset.count_sub] at he_cnt
  by_cases ha : a = e
  · subst ha
    have h1 : Multiset.count a ({a} : MultigraphEdges n) = 1 := Multiset.count_singleton_self a
    rw [h1]
    omega
  · have h0 : Multiset.count a ({e} : MultigraphEdges n) = 0 :=
      Multiset.count_eq_zero.mpr (by simp [ha])
    rw [h0]
    omega

/-- Combining a submultiset `A ≤ R` with a residual submultiset `B ≤ R - A` preserves `A + B ≤ R`. -/
lemma multiset_add_le_of_le_sub {n : ℕ} {A B R : MultigraphEdges n}
    (hA : A ≤ R) (hB : B ≤ R - A) :
    A + B ≤ R := by
  rw [Multiset.le_iff_count] at hA hB ⊢
  intro a
  have h1 := hA a
  have h2 := hB a
  rw [Multiset.count_sub] at h2
  rw [Multiset.count_add]
  omega

/-- Finite fuel induction extending any non-empty trail `u :: ws` in an even-degree loopless
multigraph `R` to a closed cycle starting and ending at `u`. -/
lemma extend_trail_to_cycle {n : ℕ} {R : MultigraphEdges n}
    (hloop : IsLooplessMultiset R)
    (heven : ∀ v : Fin n, Even (multigraphDegree R v)) :
    ∀ (fuel : ℕ) (u : Fin n) (ws : List (Fin n)),
      ws ≠ [] →
      (pathEdges (u :: ws) : MultigraphEdges n) ≤ R →
      R.card - (pathEdges (u :: ws)).length ≤ fuel →
      ∃ ws' : List (Fin n),
        ws' ≠ [] ∧
        (u :: ws').getLast (by simp) = u ∧
        (pathEdges (u :: ws') : MultigraphEdges n) ≤ R
  | 0, u, ws, hws_ne, hle, hfuel => by
    let b := (u :: ws).getLast (by simp)
    by_cases hb : b = u
    · exact ⟨ws, hws_ne, hb, hle⟩
    · exfalso
      have hA_loop : IsLooplessMultiset (pathEdges (u :: ws) : MultigraphEdges n) :=
        isLooplessMultiset_of_le hle hloop
      have h_mod := walk_degree_mod_two u ws hA_loop b
      have hb_def : (u :: ws).getLast (by simp) = b := rfl
      rw [hb_def] at h_mod
      simp only [hb, ↓reduceIte] at h_mod
      have h_sub := multigraphDegree_sub_of_le hle b
      have h_even_b : multigraphDegree R b % 2 = 0 := Nat.even_iff.mp (heven b)
      have h_pos_rem : 0 < multigraphDegree (R - (pathEdges (u :: ws) : MultigraphEdges n)) b := by
        omega
      have hR_sub_loop : IsLooplessMultiset (R - (pathEdges (u :: ws) : MultigraphEdges n)) :=
        isLooplessMultiset_of_le (Multiset.sub_le_self _ _) hloop
      rcases exists_incident_edge_of_pos_degree hR_sub_loop h_pos_rem with ⟨z, _, hz_mem⟩
      have h_next_le : (pathEdges (u :: (ws ++ [z])) : MultigraphEdges n) ≤ R := by
        rw [pathEdges_snoc]
        exact multiset_add_singleton_le_of_mem_sub hle hz_mem
      have h_card := Multiset.card_le_card h_next_le
      rw [Multiset.coe_card, pathEdges_snoc, List.length_append, List.length_singleton] at h_card
      omega
  | fuel + 1, u, ws, hws_ne, hle, hfuel => by
    let b := (u :: ws).getLast (by simp)
    by_cases hb : b = u
    · exact ⟨ws, hws_ne, hb, hle⟩
    · have hA_loop : IsLooplessMultiset (pathEdges (u :: ws) : MultigraphEdges n) :=
        isLooplessMultiset_of_le hle hloop
      have h_mod := walk_degree_mod_two u ws hA_loop b
      have hb_def : (u :: ws).getLast (by simp) = b := rfl
      rw [hb_def] at h_mod
      simp only [hb, ↓reduceIte] at h_mod
      have h_sub := multigraphDegree_sub_of_le hle b
      have h_even_b : multigraphDegree R b % 2 = 0 := Nat.even_iff.mp (heven b)
      have h_pos_rem : 0 < multigraphDegree (R - (pathEdges (u :: ws) : MultigraphEdges n)) b := by
        omega
      have hR_sub_loop : IsLooplessMultiset (R - (pathEdges (u :: ws) : MultigraphEdges n)) :=
        isLooplessMultiset_of_le (Multiset.sub_le_self _ _) hloop
      rcases exists_incident_edge_of_pos_degree hR_sub_loop h_pos_rem with ⟨z, _, hz_mem⟩
      have h_next_le : (pathEdges (u :: (ws ++ [z])) : MultigraphEdges n) ≤ R := by
        rw [pathEdges_snoc]
        exact multiset_add_singleton_le_of_mem_sub hle hz_mem
      have h_card := Multiset.card_le_card h_next_le
      rw [Multiset.coe_card, pathEdges_snoc, List.length_append, List.length_singleton] at h_card
      have h_fuel_next : R.card - (pathEdges (u :: (ws ++ [z]))).length ≤ fuel := by
        rw [pathEdges_snoc, List.length_append, List.length_singleton]
        omega
      exact extend_trail_to_cycle hloop heven fuel u (ws ++ [z]) (by simp) h_next_le h_fuel_next

/-- Every vertex `u` of positive degree in an even-degree loopless multigraph `R` lies on a
non-empty closed sub-walk `u :: (c_init ++ [u])` contained in `R`. -/
lemma exists_closed_walk_of_pos_degree {n : ℕ} {R : MultigraphEdges n} {u : Fin n}
    (hloop : IsLooplessMultiset R)
    (heven : ∀ v : Fin n, Even (multigraphDegree R v))
    (hpos : 0 < multigraphDegree R u) :
    ∃ c_init : List (Fin n),
      0 < (pathEdges (u :: (c_init ++ [u]))).length ∧
      (pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n) ≤ R := by
  rcases exists_incident_edge_of_pos_degree hloop hpos with ⟨w0, _, hw0_mem⟩
  have h_init_le : (pathEdges [u, w0] : MultigraphEdges n) ≤ R := by
    change ({s(u, w0)} : MultigraphEdges n) ≤ R
    rwa [Multiset.singleton_le]
  rcases extend_trail_to_cycle hloop heven R.card u [w0] (by simp) h_init_le (by omega) with
    ⟨ws', hws'_ne, hws'_last, hws'_le⟩
  have h_last_eq : ws'.getLast hws'_ne = u := by
    have h1 : (u :: ws').getLast (by simp) = ws'.getLast hws'_ne :=
      List.getLast_cons hws'_ne
    exact h1.symm.trans hws'_last
  have h_drop : ws'.dropLast ++ [u] = ws' := by
    rw [← h_last_eq]
    exact List.dropLast_append_getLast hws'_ne
  refine ⟨ws'.dropLast, ?_, ?_⟩
  · rw [h_drop, pathEdges_length (u :: ws') (by simp)]
    have h_len : 1 ≤ ws'.length := List.length_pos_of_ne_nil hws'_ne
    simp only [List.length_cons]
    omega
  · rw [h_drop]
    exact hws'_le

/-- Splicing a closed sub-walk `u :: (c_init ++ [u])` into `s ++ u :: t` at vertex `u`
adds their edge multisets. -/
lemma splice_pathEdges_multiset {n : ℕ} (s : List (Fin n)) (u : Fin n) (c_init t : List (Fin n)) :
    (pathEdges (s ++ u :: (c_init ++ u :: t)) : MultigraphEdges n) =
      (pathEdges (s ++ u :: t) : MultigraphEdges n) +
        (pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n) := by
  have h_list : pathEdges (s ++ u :: (c_init ++ u :: t)) =
      pathEdges (s ++ [u]) ++ (pathEdges (u :: (c_init ++ [u])) ++ pathEdges (u :: t)) := by
    rw [pathEdges_append_cons s u (c_init ++ u :: t)]
    change pathEdges (s ++ [u]) ++ pathEdges ((u :: c_init) ++ u :: t) = _
    rw [pathEdges_append_cons (u :: c_init) u t]
    rfl
  have h5 := pathEdges_append_cons s u t
  have h_coe1 : (pathEdges (s ++ u :: (c_init ++ u :: t)) : MultigraphEdges n) =
      (pathEdges (s ++ [u]) : MultigraphEdges n) +
        ((pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n) +
          (pathEdges (u :: t) : MultigraphEdges n)) := by
    rw [h_list, Multiset.coe_add, Multiset.coe_add]
  have h_coe2 : (pathEdges (s ++ u :: t) : MultigraphEdges n) =
      (pathEdges (s ++ [u]) : MultigraphEdges n) + (pathEdges (u :: t) : MultigraphEdges n) := by
    rw [h5, Multiset.coe_add]
  rw [h_coe1, h_coe2, add_assoc, add_comm (pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n)]

/-- Splicing a closed sub-walk at an internal vertex `u` preserves the closed-walk boundary condition. -/
lemma splice_is_closed {α : Type*} (s : List α) (u : α) (c_init t : List α)
    (h_closed : (s ++ u :: t).head? = (s ++ u :: t).getLast?) :
    (s ++ u :: (c_init ++ u :: t)).head? = (s ++ u :: (c_init ++ u :: t)).getLast? := by
  have h_head : (s ++ u :: (c_init ++ u :: t)).head? = (s ++ u :: t).head? := by
    cases s <;> rfl
  have h_last1 : (s ++ u :: (c_init ++ u :: t)).getLast? = (u :: t).getLast? := by
    rw [List.getLast?_append_of_ne_nil s (by simp)]
    change ((u :: c_init) ++ (u :: t)).getLast? = (u :: t).getLast?
    exact List.getLast?_append_of_ne_nil (u :: c_init) (by simp)
  have h_last2 : (s ++ u :: t).getLast? = (u :: t).getLast? :=
    List.getLast?_append_of_ne_nil s (by simp)
  rw [h_head, h_closed, h_last2, h_last1]

/-- Any non-empty closed loopless walk contributes an even multigraph degree at every vertex. -/
lemma closed_walk_even_degree {n : ℕ} {w : List (Fin n)}
    (hw_ne : w ≠ []) (hw_closed : w.head? = w.getLast?)
    (hloop : IsLooplessMultiset (pathEdges w : MultigraphEdges n)) (v : Fin n) :
    Even (multigraphDegree (pathEdges w : MultigraphEdges n) v) := by
  cases w with
  | nil => contradiction
  | cons u ws =>
    have h_last : (u :: ws).getLast (by simp) = u := by
      have h1 : (u :: ws).head? = some u := rfl
      have h2 : (u :: ws).getLast? = some ((u :: ws).getLast (by simp)) :=
        List.getLast?_eq_getLast_of_ne_nil (by simp)
      rw [h1, h2, Option.some.injEq] at hw_closed
      exact hw_closed.symm
    have h_mod := walk_degree_mod_two u ws hloop v
    rw [h_last] at h_mod
    exact Nat.even_iff.mpr (by omega)

/-- Iterated Hierholzer cycle-splicing induction: extends any closed subwalk `w` in an even-degree
loopless multigraph `E` until every visited vertex has zero residual degree in `E - pathEdges w_star`. -/
lemma extend_closed_walk_to_eulerian {n : ℕ} {E : MultigraphEdges n}
    (hloop : IsLooplessMultiset E)
    (heven : ∀ v : Fin n, Even (multigraphDegree E v)) :
    ∀ (fuel : ℕ) (w : List (Fin n)),
      w ≠ [] →
      w.head? = w.getLast? →
      (pathEdges w : MultigraphEdges n) ≤ E →
      E.card - (pathEdges w).length ≤ fuel →
      ∃ w_star : List (Fin n),
        w_star ≠ [] ∧
        w_star.head? = w_star.getLast? ∧
        (pathEdges w_star : MultigraphEdges n) ≤ E ∧
        (∀ x ∈ w, x ∈ w_star) ∧
        (∀ u ∈ w_star, multigraphDegree (E - (pathEdges w_star : MultigraphEdges n)) u = 0)
  | 0, w, hw_ne, hw_closed, hw_le, hfuel => by
    let R := E - (pathEdges w : MultigraphEdges n)
    by_cases h_ex : ∃ u ∈ w, 0 < multigraphDegree R u
    · exfalso
      rcases h_ex with ⟨u, hu_mem, hu_pos⟩
      rcases List.append_of_mem hu_mem with ⟨s, t, rfl⟩
      have hR_loop : IsLooplessMultiset R :=
        isLooplessMultiset_of_le (Multiset.sub_le_self _ _) hloop
      have hR_even : ∀ v : Fin n, Even (multigraphDegree R v) := by
        intro v
        have hw_loop := isLooplessMultiset_of_le hw_le hloop
        have hw_even := closed_walk_even_degree hw_ne hw_closed hw_loop v
        have h_sub := multigraphDegree_sub_of_le hw_le v
        change multigraphDegree R v + multigraphDegree (pathEdges (s ++ u :: t) : MultigraphEdges n) v =
          multigraphDegree E v at h_sub
        have hE_even := Nat.even_iff.mp (heven v)
        have hw_even' := Nat.even_iff.mp hw_even
        exact Nat.even_iff.mpr (by omega)
      rcases exists_closed_walk_of_pos_degree hR_loop hR_even hu_pos with ⟨c_init, hc_len, hc_le⟩
      let w' := s ++ u :: (c_init ++ u :: t)
      have hw'_edges : (pathEdges w' : MultigraphEdges n) =
          (pathEdges (s ++ u :: t) : MultigraphEdges n) +
            (pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n) :=
        splice_pathEdges_multiset s u c_init t
      have hw'_le : (pathEdges w' : MultigraphEdges n) ≤ E := by
        rw [hw'_edges]
        exact multiset_add_le_of_le_sub hw_le hc_le
      have h_card := Multiset.card_le_card hw'_le
      have h_len_add : (pathEdges w').length =
          (pathEdges (s ++ u :: t)).length + (pathEdges (u :: (c_init ++ [u]))).length := by
        have h_mc := congrArg Multiset.card hw'_edges
        simpa using h_mc
      rw [Multiset.coe_card] at h_card
      omega
    · refine ⟨w, hw_ne, hw_closed, hw_le, fun x hx => hx, ?_⟩
      intro u hu
      by_contra h_ne_zero
      exact h_ex ⟨u, hu, Nat.pos_of_ne_zero h_ne_zero⟩
  | fuel + 1, w, hw_ne, hw_closed, hw_le, hfuel => by
    let R := E - (pathEdges w : MultigraphEdges n)
    by_cases h_ex : ∃ u ∈ w, 0 < multigraphDegree R u
    · rcases h_ex with ⟨u, hu_mem, hu_pos⟩
      rcases List.append_of_mem hu_mem with ⟨s, t, rfl⟩
      have hR_loop : IsLooplessMultiset R :=
        isLooplessMultiset_of_le (Multiset.sub_le_self _ _) hloop
      have hR_even : ∀ v : Fin n, Even (multigraphDegree R v) := by
        intro v
        have hw_loop := isLooplessMultiset_of_le hw_le hloop
        have hw_even := closed_walk_even_degree hw_ne hw_closed hw_loop v
        have h_sub := multigraphDegree_sub_of_le hw_le v
        change multigraphDegree R v + multigraphDegree (pathEdges (s ++ u :: t) : MultigraphEdges n) v =
          multigraphDegree E v at h_sub
        have hE_even := Nat.even_iff.mp (heven v)
        have hw_even' := Nat.even_iff.mp hw_even
        exact Nat.even_iff.mpr (by omega)
      rcases exists_closed_walk_of_pos_degree hR_loop hR_even hu_pos with ⟨c_init, hc_len, hc_le⟩
      let w' := s ++ u :: (c_init ++ u :: t)
      have hw'_edges : (pathEdges w' : MultigraphEdges n) =
          (pathEdges (s ++ u :: t) : MultigraphEdges n) +
            (pathEdges (u :: (c_init ++ [u])) : MultigraphEdges n) :=
        splice_pathEdges_multiset s u c_init t
      have hw'_le : (pathEdges w' : MultigraphEdges n) ≤ E := by
        rw [hw'_edges]
        exact multiset_add_le_of_le_sub hw_le hc_le
      have h_card := Multiset.card_le_card hw'_le
      have h_len_add : (pathEdges w').length =
          (pathEdges (s ++ u :: t)).length + (pathEdges (u :: (c_init ++ [u]))).length := by
        have h_mc := congrArg Multiset.card hw'_edges
        simpa using h_mc
      rw [Multiset.coe_card] at h_card
      have hw'_ne : w' ≠ [] := by simp [w']
      have hw'_closed : w'.head? = w'.getLast? := splice_is_closed s u c_init t hw_closed
      have h_fuel_next : E.card - (pathEdges w').length ≤ fuel := by omega
      rcases extend_closed_walk_to_eulerian hloop heven fuel w' hw'_ne hw'_closed hw'_le h_fuel_next with
        ⟨w_star, hw_star_ne, hw_star_closed, hw_star_le, hw_star_sub, hw_star_deg⟩
      refine ⟨w_star, hw_star_ne, hw_star_closed, hw_star_le, ?_, hw_star_deg⟩
      intro x hx
      apply hw_star_sub
      simp only [w', List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hxs | rfl | hxt
      · exact Or.inl hxs
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr hxt)))
    · refine ⟨w, hw_ne, hw_closed, hw_le, fun x hx => hx, ?_⟩
      intro u hu
      by_contra h_ne_zero
      exact h_ex ⟨u, hu, Nat.pos_of_ne_zero h_ne_zero⟩

/-- Both endpoints of any edge `s(x, y) ∈ pathEdges w` belong to the vertex list `w`. -/
lemma mem_of_mem_pathEdges {α : Type*} :
    ∀ {w : List α} {x y : α}, s(x, y) ∈ pathEdges w → x ∈ w ∧ y ∈ w
  | [], _, _, h => by contradiction
  | [_], _, _, h => by contradiction
  | a :: b :: rest, x, y, h => by
    dsimp [pathEdges] at h
    rcases List.mem_cons.mp h with heq | htail
    · have hx : x ∈ (s(a, b) : Sym2 α) := by
        rw [← heq]
        exact Sym2.mem_mk_left x y
      have hy : y ∈ (s(a, b) : Sym2 α) := by
        rw [← heq]
        exact Sym2.mem_mk_right x y
      rw [Sym2.mem_iff] at hx hy
      refine ⟨?_, ?_⟩
      · rcases hx with rfl | rfl <;> simp
      · rcases hy with rfl | rfl <;> simp
    · rcases mem_of_mem_pathEdges htail with ⟨hx, hy⟩
      exact ⟨List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy⟩

/-- Constructive Hierholzer's Theorem on `multigraphUnion E1 E2`:
Unconditionally discharges `EulerianWalkInduction n` for all `n : ℕ`. -/
theorem eulerianWalkInduction_holds (n : ℕ) : EulerianWalkInduction n := by
  intro E1 E2 h_conn h_loop1 h_loop2 h_even
  let E := multigraphUnion E1 E2
  have hE_loop : IsLooplessMultiset E := isLooplessMultiset_union h_loop1 h_loop2
  cases n with
  | zero =>
    refine ⟨{
      walk := []
      is_closed := rfl
      edge_multiset_eq := ?_
      visits_all := fun v => Fin.elim0 v
    }⟩
    apply le_antisymm (Multiset.zero_le E)
    rw [Multiset.le_iff_count]
    intro e
    by_contra h_pos
    have he_mem : e ∈ E := Multiset.count_pos.mp (by omega)
    rcases hE_loop e he_mem with ⟨x, _, _, _⟩
    exact Fin.elim0 x
  | succ m =>
    let v0 : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
    have hw0_ne : [v0] ≠ [] := by simp
    have hw0_closed : [v0].head? = [v0].getLast? := rfl
    have hw0_le : (pathEdges [v0] : MultigraphEdges (m + 1)) ≤ E := by
      change (0 : MultigraphEdges (m + 1)) ≤ E
      exact Multiset.zero_le E
    rcases extend_closed_walk_to_eulerian hE_loop h_even E.card [v0] hw0_ne hw0_closed hw0_le (by omega) with
      ⟨w_star, hw_star_ne, hw_star_closed, hw_star_le, hw_star_sub, hw_star_deg⟩
    have hv0_mem : v0 ∈ w_star := hw_star_sub v0 (by simp)
    have h_step_mem : ∀ {a b : Fin (m + 1)}, s(a, b) ∈ E1 → a ∈ w_star → b ∈ w_star := by
      intro a b hab ha_mem
      have hab_E : s(a, b) ∈ E := by
        dsimp [E, multigraphUnion]
        exact Multiset.mem_add.mpr (Or.inl hab)
      have hab_not_rem : s(a, b) ∉ E - (pathEdges w_star : MultigraphEdges (m + 1)) := by
        intro h_in_rem
        have h_in_filt : s(a, b) ∈ (E - (pathEdges w_star : MultigraphEdges (m + 1))).filter (fun e => a ∈ e) := by
          rw [Multiset.mem_filter]
          exact ⟨h_in_rem, Sym2.mem_mk_left a b⟩
        have h_pos : 0 < multigraphDegree (E - (pathEdges w_star : MultigraphEdges (m + 1))) a :=
          Multiset.card_pos_iff_exists_mem.mpr ⟨s(a, b), h_in_filt⟩
        have h_zero := hw_star_deg a ha_mem
        omega
      have hab_in_walk : s(a, b) ∈ (pathEdges w_star : MultigraphEdges (m + 1)) := by
        have h_cnt_E : 0 < Multiset.count s(a, b) E := Multiset.count_pos.mpr hab_E
        have h_cnt_rem : Multiset.count s(a, b) (E - (pathEdges w_star : MultigraphEdges (m + 1))) = 0 :=
          Multiset.count_eq_zero.mpr hab_not_rem
        rw [Multiset.count_sub] at h_cnt_rem
        have h_cnt_walk : 0 < Multiset.count s(a, b) (pathEdges w_star : MultigraphEdges (m + 1)) := by
          omega
        exact Multiset.count_pos.mp h_cnt_walk
      rw [Multiset.mem_coe] at hab_in_walk
      exact (mem_of_mem_pathEdges hab_in_walk).2
    have h_conn_mem : ∀ u v : Fin (m + 1), ConnectedInEdges E1 u v → u ∈ w_star → v ∈ w_star := by
      intro u v h_c
      induction h_c with
      | refl _ => exact fun h => h
      | step hu_a _ ih => exact fun hu => ih (h_step_mem hu_a hu)
    have h_visits_all : ∀ v : Fin (m + 1), v ∈ w_star :=
      fun v => h_conn_mem v0 v (h_conn v0 v) hv0_mem
    have h_edges_eq : (pathEdges w_star : MultigraphEdges (m + 1)) = E := by
      apply le_antisymm hw_star_le
      rw [Multiset.le_iff_count]
      intro e
      by_contra h_gt
      have he_rem : e ∈ E - (pathEdges w_star : MultigraphEdges (m + 1)) := by
        rw [← Multiset.count_pos, Multiset.count_sub]
        omega
      have hR_loop : IsLooplessMultiset (E - (pathEdges w_star : MultigraphEdges (m + 1))) :=
        isLooplessMultiset_of_le (Multiset.sub_le_self _ _) hE_loop
      rcases hR_loop e he_rem with ⟨x, y, rfl, _⟩
      have h_in_filt : s(x, y) ∈ (E - (pathEdges w_star : MultigraphEdges (m + 1))).filter (fun e => x ∈ e) := by
        rw [Multiset.mem_filter]
        exact ⟨he_rem, Sym2.mem_mk_left x y⟩
      have h_pos : 0 < multigraphDegree (E - (pathEdges w_star : MultigraphEdges (m + 1))) x :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨s(x, y), h_in_filt⟩
      have h_zero := hw_star_deg x (h_visits_all x)
      omega
    exact ⟨{
      walk := w_star
      is_closed := hw_star_closed
      edge_multiset_eq := h_edges_eq
      visits_all := h_visits_all
    }⟩

/-- Constructive Eulerian circuit bridge discharging graph-theoretic preconditions
from spanning tree connectivity, loopless properties, and multigraph degree parity. -/
theorem exists_eulerianCircuit {n : ℕ} (T : SpanningTree n)
    (M : PerfectMatching (oddDegreeVertices T.edges))

    : ∃ _C : EulerianCircuit (multigraphUnion T.edges M.edges), True := by
  rcases eulerianWalkInduction_holds n T.edges M.edges T.connected T.loopless M.loopless (multigraph_degree_even T M) with ⟨C⟩
  exact ⟨C, trivial⟩

/-- Concrete Eulerian circuit witness along a valid Hamiltonian tour cycle walk. -/
lemma exists_hamiltonian_eulerianCircuit {n : ℕ} (hn : 3 ≤ n) (p : List (Fin n))
    (hp : IsTour (completeGraph n) p) :
    ∃ (E : MultigraphEdges n), Nonempty (EulerianCircuit E) := by
  cases heq : p with
  | nil =>
    have h_len := hp.1
    rw [heq, List.length_nil] at h_len
    omega
  | cons x xs =>
    rw [heq] at hp
    let w := (x :: xs) ++ [x]
    have h_head : w.head? = some x := rfl
    have h_last : w.getLast? = some x := by
      rw [show w = (x :: xs) ++ x :: [] from rfl, List.getLast?_append_cons]
      rfl
    have h_closed : w.head? = w.getLast? := by
      rw [h_head, h_last]
    have h_visits : ∀ v : Fin n, v ∈ w := by
      intro v
      have hv_p : v ∈ x :: xs := mem_of_isTour (x :: xs) hp v
      exact List.mem_append.mpr (Or.inl hv_p)
    refine ⟨(pathEdges w : Multiset (Sym2 (Fin n))), ⟨{
      walk := w
      is_closed := h_closed
      edge_multiset_eq := rfl
      visits_all := h_visits
    }⟩⟩

/-- Constructive synthesis of a complete Christofides certificate from MST,
minimum-weight matching, and Eulerian circuit induction. -/
theorem nonempty_christofidesCertificate {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :

    Nonempty (ChristofidesCertificate n c) := by
  rcases exists_mst hn c with ⟨T, hMST⟩
  rcases exists_minWeightMatching hn c T with ⟨M, hMin⟩
  rcases exists_eulerianCircuit T M with ⟨C, _⟩
  exact ⟨{
    tree := T
    tree_mst := hMST
    matching := M
    matching_min := hMin
    eulerian := C
  }⟩

/-- Existence of a complete Christofides certificate. -/
theorem exists_christofidesCertificate {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :

    ∃ _cert : ChristofidesCertificate n c, True := by
  rcases nonempty_christofidesCertificate hn c with ⟨cert⟩
  exact ⟨cert, trivial⟩

/-- Unconditional Synthesized 3/2-Approximation Theorem (Integer Scaling):
The synthesized Christofides tour achieves 2 * cost(p) ≤ 3 * optTourCost c. -/
theorem christofides_unconditional_approx_ratio_nat {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) :
    ∃ p : List (Fin n), IsTour (completeGraph n) p ∧ 2 * tourCost c p ≤ 3 * optTourCost c := by
  rcases exists_christofidesCertificate hn c with ⟨cert, _⟩
  refine ⟨christofidesTour cert, christofides_is_tour hn cert, ?_⟩
  exact christofides_approx_ratio_nat hn c hMetric cert

/-- Unconditional Synthesized 3/2-Approximation Theorem (Real Arithmetic):
The synthesized Christofides tour achieves cost(p) ≤ (3/2) * optTourCost c. -/
theorem christofides_unconditional_approx_ratio {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n)
    (hMetric : IsMetricCost c) :
    ∃ p : List (Fin n), IsTour (completeGraph n) p ∧ (tourCost c p : ℝ) ≤ (3 / 2 : ℝ) * (optTourCost c : ℝ) := by
  rcases exists_christofidesCertificate hn c with ⟨cert, _⟩
  refine ⟨christofidesTour cert, christofides_is_tour hn cert, ?_⟩
  exact christofides_approx_ratio hn c hMetric cert

/-- Alias for optimal tour cost, optionally accepting the vertex bound hn. -/
abbrev optCost {n : ℕ} (_hn : 3 ≤ n) (c : CostFunction n) : ℕ := optTourCost c

/-- Baseline optimal-tour existence witness (`p_opt`, 1 * OPT ≤ 1.5 * OPT) in integer arithmetic. -/
theorem tour_approx_ratio_nat_unconditional {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :
    ∃ p : List (Fin n), IsTour (completeGraph n) p ∧ 2 * tourCost c p ≤ 3 * optTourCost c := by
  rcases exists_optTour hn c with ⟨p_opt, hp_opt, h_optCost⟩
  refine ⟨p_opt, hp_opt, ?_⟩
  rw [h_optCost]
  omega

/-- Baseline optimal-tour existence witness (`p_opt`, 1 * OPT ≤ 1.5 * OPT) in real arithmetic. -/
theorem tour_approx_ratio_unconditional {n : ℕ} (hn : 3 ≤ n) (c : CostFunction n) :
    ∃ p : List (Fin n), IsTour (completeGraph n) p ∧ (tourCost c p : ℝ) ≤ (3 / 2 : ℝ) * (optTourCost c : ℝ) := by
  rcases exists_optTour hn c with ⟨p_opt, hp_opt, h_optCost⟩
  refine ⟨p_opt, hp_opt, ?_⟩
  have h_nat : 2 * tourCost c p_opt ≤ 3 * optTourCost c := by
    rw [h_optCost]
    omega
  have h_cast : ((2 * tourCost c p_opt : ℕ) : ℝ) ≤ ((3 * optTourCost c : ℕ) : ℝ) :=
    Nat.cast_le.mpr h_nat
  push_cast at h_cast
  linarith

end TSP

end IJM




