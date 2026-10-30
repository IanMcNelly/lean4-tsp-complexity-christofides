-- Lean 4 Palomar Challenge Module for Decision TSP Complexity, Polyhedral Barriers & Reductions
-- Matches solution module: TSPComplexity

module

public import Mathlib

@[expose] public section

namespace IJM
namespace TSP

/-! # Advertised Statement: Polyhedral Barriers, Parameterized Solvers, and Reductions for Decision TSP -/

/-- Simple undirected finite graph on vertex set `Fin n`. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ u, ¬ adj u u

/-- Non-negative edge weight function. -/
def CostFunction (n : ℕ) := Fin n → Fin n → ℕ

/-- Ordered sequence of cycle edges formed by adjacent elements in a circular list. -/
def cycleEdges {n : ℕ} (p : List (Fin n)) : List (Fin n × Fin n) :=
  match p with | [] => [] | x :: xs => p.zip (xs ++ [x])

/-- Total traversal cost of the cycle edge sequence. -/
def tourCost {n : ℕ} (c : CostFunction n) (p : List (Fin n)) : ℕ :=
  ((cycleEdges p).map (fun e => c e.1 e.2)).sum

/-- A valid Hamiltonian tour visits every vertex in `Fin n` bijectively along graph edges. -/
def IsTour {n : ℕ} (G : Graph n) (p : List (Fin n)) : Prop :=
  p.length = n ∧ p.Nodup ∧ (∀ e ∈ cycleEdges p, G.adj e.1 e.2)

/-- Decision TSP predicate: existence of a Hamiltonian tour of cost at most `B`. -/
def ValidTourBound {n : ℕ} (G : Graph n) (c : CostFunction n) (B : ℕ) : Prop :=
  ∃ p : List (Fin n), IsTour G p ∧ tourCost c p ≤ B

/-- Specification for an exact decision procedure for TSP. -/
def DecidesTSP (algo : (n : ℕ) → Graph n → CostFunction n → ℕ → Bool) : Prop :=
  ∀ (n : ℕ) (G : Graph n) (c : CostFunction n) (B : ℕ), algo n G c B = true ↔ ValidTourBound G c B

inductive SearchStatus (n : ℕ) where
  | searching | accepted (witness : List (Fin n)) | rejected
  deriving DecidableEq

/-- Search state configuration of the subtour elimination state machine. -/
structure SolverState (n : ℕ) where
  status : SearchStatus n
  queue : List (List (Fin n))
  bestCost : Option ℕ
  bestTour : Option (List (Fin n))
  steps : ℕ

open scoped Classical

/-- Initial search state with full permutation frontier. -/
noncomputable def SolverState.init (n : ℕ) : SolverState n :=
  ⟨SearchStatus.searching, (List.finRange n).permutations, none, none, 0⟩

/-- Single transition step of the certified solver. -/
noncomputable def step {n : ℕ} (G : Graph n) (c : CostFunction n) (B : ℕ) (s : SolverState n) : SolverState n :=
  match s.status with
  | .accepted _ => s
  | .rejected => s
  | .searching =>
    match s.queue with
    | [] =>
      match s.bestTour with
      | some t => ⟨.accepted t, [], s.bestCost, s.bestTour, s.steps + 1⟩
      | none => ⟨.rejected, [], none, none, s.steps + 1⟩
    | p :: ps =>
      if _hp : IsTour G p ∧ tourCost c p ≤ B then
        ⟨.accepted p, ps, some (tourCost c p), some p, s.steps + 1⟩
      else ⟨.searching, ps, s.bestCost, s.bestTour, s.steps + 1⟩

/-- Multi-step execution bounded by a fuel budget. -/
noncomputable def run {n : ℕ} (G : Graph n) (c : CostFunction n) (B : ℕ) (fuel : ℕ) (s : SolverState n) : SolverState n :=
  match fuel with
  | 0 => s
  | fuel' + 1 => match s.status with | .searching => run G c B fuel' (step G c B s) | _ => s

/-- Cycle-Separation Rank on the unpruned initial permutation frontier (`n! ≤ n^k`). -/
structure StructuralRank (n : ℕ) (G : Graph n) (c : CostFunction n) (k : ℕ) where
  cut_width_bound : ℕ
  rank_le : cut_width_bound ≤ k
  queue_cardinality : (SolverState.init n).queue.length ≤ n ^ k

def stepBudget (n : ℕ) (k : ℕ) : ℕ := n ^ (k + 3) + n ^ 2 + 1

noncomputable def structuralTSPSolver (n : ℕ) (G : Graph n) (c : CostFunction n) (B : ℕ) : Bool :=
  match (run G c B (stepBudget n 1) (SolverState.init n)).status with
  | .accepted _ => true | _ => false

/-- Canonical zero edge-cost function on `Fin n`. -/
def zeroCost (n : ℕ) : CostFunction n := fun _ _ => 0

def CrossesCut {n : ℕ} (S : Finset (Fin n)) (e : Fin n × Fin n) : Prop :=
  (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)
instance {n : ℕ} (S : Finset (Fin n)) (e : Fin n × Fin n) : Decidable (CrossesCut S e) :=
  inferInstanceAs (Decidable ((e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)))

def tourCutEdges {n : ℕ} (p : List (Fin n)) (S : Finset (Fin n)) : List (Fin n × Fin n) :=
  (cycleEdges p).filter (CrossesCut S)

abbrev FractionalAssignment (n : ℕ) := Fin n → Fin n → ℝ

def DegreeConservation {n : ℕ} (x : FractionalAssignment n) : Prop :=
  ∀ v : Fin n, (∑ u : Fin n, if u ≠ v then x v u else 0) = 2

noncomputable def cutCapacity {n : ℕ} (x : FractionalAssignment n) (S : Finset (Fin n)) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ (Finset.univ \ S), x u v

def SubtourCutConstraint {n : ℕ} (x : FractionalAssignment n) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 2 ≤ cutCapacity x S

structure HeldKarpPoint (n : ℕ) where
  x : FractionalAssignment n
  symmetric : ∀ u v, x u v = x v u
  loopless : ∀ v, x v v = 0
  nonneg : ∀ u v, 0 ≤ x u v
  unit_le : ∀ u v, x u v ≤ 1
  degrees : DegreeConservation x
  subtours : SubtourCutConstraint x

noncomputable def fractionalCost {n : ℕ} (c : CostFunction n) (x : FractionalAssignment n) : ℝ :=
  (1 / 2) * (∑ u : Fin n, ∑ v : Fin n, (c u v : ℝ) * x u v)
noncomputable def tourPoint {n : ℕ} (p : List (Fin n)) : FractionalAssignment n :=
  fun u v => if (u, v) ∈ cycleEdges p ∨ (v, u) ∈ cycleEdges p then 1 else 0
noncomputable def TSPPolytope (n : ℕ) : Set (FractionalAssignment n) :=
  convexHull ℝ { x | ∃ p : List (Fin n), p.length = n ∧ p.Nodup ∧ x = tourPoint p }

def petersenAdj (u v : Fin 10) : Prop :=
  u ≠ v ∧
  ((u.val < 5 ∧ v.val < 5 ∧ ((u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val)) ∨
   (5 ≤ u.val ∧ 5 ≤ v.val ∧
    (((u.val - 5) + 2) % 5 = v.val - 5 ∨ ((v.val - 5) + 2) % 5 = u.val - 5)) ∨
   (u.val < 5 ∧ 5 ≤ v.val ∧ v.val = u.val + 5) ∨
   (5 ≤ u.val ∧ v.val < 5 ∧ u.val = v.val + 5))
instance (u v : Fin 10) : Decidable (petersenAdj u v) := by unfold petersenAdj; infer_instance
noncomputable def petersenFractional : FractionalAssignment 10 :=
  fun u v => if petersenAdj u v then (2 / 3 : ℝ) else 0

abbrev DFJCut (n : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ}
noncomputable def dfjSlack {n : ℕ} (x : FractionalAssignment n) (S : DFJCut n) : ℝ := cutCapacity x S.1 - 2
lemma petersen_singleton_proper (v : Fin 10) : ({v} : Finset (Fin 10)) ≠ Finset.univ := by revert v; decide
def petersenSingletonCut (v : Fin 10) : DFJCut 10 := ⟨{v}, Finset.singleton_nonempty v, petersen_singleton_proper v⟩

structure HasAffineLift (n r : ℕ) : Prop where
  affine_projection :
    ∃ (L : AffineSubspace ℝ (Matrix (Fin r) (Fin r) ℝ))
      (T : Matrix (Fin r) (Fin r) ℝ →ᵃ[ℝ] (FractionalAssignment n)),
      T '' {X | X ∈ L ∧ X.PosSemidef} = TSPPolytope n
  slack_factorization :
    ∃ (A : DFJCut n → Matrix (Fin r) (Fin r) ℝ)
      (B : List (Fin n) → Matrix (Fin r) (Fin r) ℝ),
      (∀ S, (A S).PosSemidef) ∧
      (∀ p, p.length = n → p.Nodup → (B p).PosSemidef) ∧
      (∀ (S : DFJCut n) (p : List (Fin n)),
        p.length = n → p.Nodup → dfjSlack (tourPoint p) S = Matrix.trace (A S * B p))

def SatisfiesFioriniRothvossBound (n r : ℕ) (C : ℝ) : Prop :=
  4 ≤ n →
  (∀ (A : DFJCut n → Matrix (Fin r) (Fin r) ℝ) (B : List (Fin n) → Matrix (Fin r) (Fin r) ℝ),
    (∀ S, (A S).PosSemidef) →
    (∀ p, p.length = n → p.Nodup → (B p).PosSemidef) →
    (∀ (S : DFJCut n) (p : List (Fin n)),
      p.length = n → p.Nodup → dfjSlack (tourPoint p) S = Matrix.trace (A S * B p)) →
    (n : ℝ) ^ (Nat.ceil C + 1) < (r : ℝ))

namespace Reduction

def Literal := Nat × Bool
def Clause := Vector Literal 3
structure Formula where
  clauses : List Clause

def SatisfiesClause (assign : Nat → Bool) (c : Clause) : Bool :=
  c.toArray.any (fun l => assign l.1 == l.2)

def Satisfiable (F : Formula) : Prop :=
  ∃ assign : Nat → Bool, ∀ c ∈ F.clauses, SatisfiesClause assign c = true

def triangleIdx {n : ℕ} (u : Fin n) : ℕ := u.val / 3
def isInternalTriangleEdge {n : ℕ} (u v : Fin n) : Prop := u ≠ v ∧ triangleIdx u = triangleIdx v
def isBridgeEdge {n : ℕ} (u v : Fin n) : Prop := u ≠ v ∧ triangleIdx u ≠ triangleIdx v
def ringOfTrianglesAdj {n : ℕ} (u v : Fin n) : Prop := isInternalTriangleEdge u v ∨ isBridgeEdge u v

lemma ringOfTrianglesAdj_symm {n : ℕ} (u v : Fin n) :
    ringOfTrianglesAdj u v → ringOfTrianglesAdj v u := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

lemma ringOfTrianglesAdj_loopless {n : ℕ} (u : Fin n) : ¬ ringOfTrianglesAdj u u := by
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h rfl

def ringOfTrianglesGraph (n : ℕ) : Graph n where
  adj := ringOfTrianglesAdj
  symm := ringOfTrianglesAdj_symm
  loopless := ringOfTrianglesAdj_loopless

structure TSPGadget (F : Formula) where
  n : ℕ
  graph : Graph n
  cost : CostFunction n
  budget : ℕ
  size_bound : n ≤ 12 * F.clauses.length + 6
  min_vertices : 3 ≤ n
  budget_bound : n ≤ budget
  encodeTour : (Nat → Bool) → List (Fin n)
  decodeAssign : List (Fin n) → (Nat → Bool)
  encode_length : ∀ assign, (encodeTour assign).length = n
  encode_nodup : ∀ assign, (encodeTour assign).Nodup
  encode_edges_valid : ∀ assign, ∀ e ∈ cycleEdges (encodeTour assign), graph.adj e.1 e.2
  encode_edge_cost : ∀ assign, (∀ c ∈ F.clauses, SatisfiesClause assign c = true) →
    ∀ e ∈ cycleEdges (encodeTour assign), cost e.1 e.2 ≤ 1
  clause_interlock_penalty : ∀ (p : List (Fin n)) (c : Clause),
    IsTour graph p → c ∈ F.clauses → SatisfiesClause (decodeAssign p) c = false →
    ∃ e ∈ cycleEdges p, budget + 1 ≤ cost e.1 e.2

def hcReductionCost {n : ℕ} (G : Graph n) [DecidableRel G.adj] : CostFunction n :=
  fun u v => if G.adj u v then 0 else 1

theorem sat_to_tsp_reduction_correct (F : Formula) (gadget : TSPGadget F) :
    Satisfiable F ↔ ValidTourBound gadget.graph gadget.cost gadget.budget := by sorry
theorem hc_to_tsp_reduction_correct {n : ℕ} (hn : 3 ≤ n) (G : Graph n) [DecidableRel G.adj] :
    (∃ p : List (Fin n), IsTour G p) ↔ ValidTourBound (ringOfTrianglesGraph n) (hcReductionCost G) 0 := by sorry
end Reduction

def SolverState.initPruned {n : ℕ} (frontier : List (List (Fin n))) : SolverState n :=
  ⟨SearchStatus.searching, frontier, none, none, 0⟩

structure PrunedStructuralRank (n : ℕ) (G : Graph n) (c : CostFunction n)
    (B : ℕ) (k : ℕ) (frontier : List (List (Fin n))) where
  cut_width_bound : ℕ
  rank_le : cut_width_bound ≤ k
  frontier_tours : ∀ p ∈ frontier, IsTour G p
  frontier_complete : ∀ p : List (Fin n), IsTour G p ∧ tourCost c p ≤ B → p ∈ frontier
  frontier_cardinality : frontier.length ≤ n ^ k

noncomputable def prunedStructuralTSPSolver (n : ℕ) (G : Graph n) (c : CostFunction n)
    (B : ℕ) (frontier : List (List (Fin n))) : Bool :=
  match (run G c B (stepBudget n 1) (SolverState.initPruned frontier)).status with
  | .accepted _ => true | _ => false

theorem queue_clearance_halts {n : ℕ} (G : Graph n) (c : CostFunction n) (B : ℕ) :
    ∀ (fuel : ℕ) (s : SolverState n),
      s.status = SearchStatus.searching →
      s.queue.length + 1 ≤ fuel →
      (run G c B fuel s).status ≠ SearchStatus.searching := by sorry
theorem polynomial_termination_rank_one {n : ℕ} (G : Graph n) (c : CostFunction n) (B : ℕ)
    (s₀ : SolverState n) (hSearch : s₀.status = .searching)
    (hBound : s₀.queue.length ≤ n) (hn : 1 ≤ n) :
    (run G c B (n + 1) s₀).status ≠ SearchStatus.searching := by sorry
theorem tsp_soundness (n : ℕ) (G : Graph n) (c : CostFunction n) (B : ℕ)
    (fuel : ℕ) (w : List (Fin n)) (s₀ : SolverState n)
    (hSearch : s₀.status = .searching) (hInit : s₀.bestTour = none) :
    (run G c B fuel s₀).status = .accepted w →
    ValidTourBound G c B := by sorry
theorem tsp_completeness (n : ℕ) (G : Graph n) (c : CostFunction n) (B : ℕ) (hValid : ValidTourBound G c B) :
    ∃ (fuel : ℕ) (w : List (Fin n)), (run G c B fuel (SolverState.init n)).status = .accepted w := by sorry
theorem structural_solver_decides_tsp (n : ℕ) (G : Graph n) (c : CostFunction n) (B : ℕ)
    (hRank : StructuralRank n G c 1) : structuralTSPSolver n G c B = true ↔ ValidTourBound G c B := by sorry
theorem structuralRank_inhabited :
    ∃ (n : ℕ) (G : Graph n) (c : CostFunction n), 1 ≤ n ∧ Nonempty (StructuralRank n G c 1) := by sorry
theorem dfj_subtour_cut_bound {n : ℕ} (G : Graph n) (p : List (Fin n)) (hn : 3 ≤ n) (hTour : IsTour G p)
    (S : Finset (Fin n)) (hS_nonempty : S.Nonempty) (hS_proper : S ≠ Finset.univ) :
    2 ≤ (tourCutEdges p S).length := by sorry
theorem tour_is_held_karp_point {n : ℕ} (G : Graph n) (p : List (Fin n)) (hn : 3 ≤ n) (hTour : IsTour G p) :
    ∃ hk : HeldKarpPoint n, hk.x = tourPoint p := by sorry
theorem held_karp_strictly_contains_tsp_polytope :
    ∃ n : ℕ, 4 ≤ n ∧ ∃ hk : HeldKarpPoint n, hk.x ∉ TSPPolytope n := by sorry
theorem petersen_dfjSlack_singleton_zero (v : Fin 10) :
    dfjSlack petersenFractional (petersenSingletonCut v) = 0 := by sorry
theorem petersen_dfjSlack_nontrivial_ge_two_thirds (S : DFJCut 10)
    (hS_ge_two : 2 ≤ S.1.card) (hS_le_eight : S.1.card ≤ 8) :
    (2 / 3 : ℝ) ≤ dfjSlack petersenFractional S := by sorry
theorem tsp_extension_complexity_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ r : ℕ,
      HasAffineLift n r → SatisfiesFioriniRothvossBound n r C → (n : ℝ) ^ C < (r : ℝ) := by sorry
theorem pruned_structural_solver_decides_tsp (n : ℕ) (G : Graph n) (c : CostFunction n)
    (B : ℕ) (frontier : List (List (Fin n))) (hRank : PrunedStructuralRank n G c B 1 frontier) :
    prunedStructuralTSPSolver n G c B frontier = true ↔ ValidTourBound G c B := by sorry
theorem prunedStructuralRank_inhabited_all_ge_three (n : ℕ) (hn : 3 ≤ n) :
    ∃ (G : Graph n) (c : CostFunction n) (B : ℕ) (frontier : List (List (Fin n))),
      Nonempty (PrunedStructuralRank n G c B 1 frontier) := by sorry
theorem pruned_solver_accepts_necklace_all_ge_three (n : ℕ) (hn : 3 ≤ n) :
    (run (Reduction.ringOfTrianglesGraph n) (zeroCost n) 0 (stepBudget n 1)
      (SolverState.initPruned [List.finRange n])).status = SearchStatus.accepted (List.finRange n) := by sorry

end TSP
end IJM
