# Phase 5 & Phase 9 Empirical Benchmark Report (`RESULTS.md`)

**Project:** Computational Complexity & Formal Verification of Decision TSP  
**Module:** `benchmarks/`  
**Engine:** [`branch_and_cut.py`](branch_and_cut.py) & [`adversarial_instances.py`](adversarial_instances.py)  
**Environment:** Python 3.12.0, SciPy 1.18.1 (`highs` LP solver), NumPy 2.5.3, NetworkX 3.7  

---

## 1. Executive Summary

This report documents the empirical stress testing of the **Continuous Held-Karp LP Relaxation**, the **Certified Branch-and-Cut State Machine** (`SolverState`, `step`, `run`), and the **Yannakakis DFJ Subtour Slack Matrix** (`DFJCut`, `dfjSlack`, `HasAffineLift`) formalized in [`TSPComplexity.lean`](../TSPComplexity.lean):

1. **Petersen Graph Fractional Stall ($P_{10}$):**
   - Verifies that the uniform fractional assignment $x_e = 2/3$ on all 15 edges of the 10-vertex Petersen graph satisfies all axioms of `HeldKarpPoint 10` with **zero degree error** ($\max_v |\deg(v) - 2| = 0.0$) and **global minimum cut capacity** $\min_{\emptyset \subsetneq S \subsetneq V} x(\delta(S)) = 2.0000$ under both **Stoer-Wagner** and **Edmonds-Karp** separation oracles.
   - Confirms that dynamic Dantzig-Fulkerson-Johnson (DFJ) subtour cut generation stalls at fractional solutions ($x_e = 2/3$ under capacity $2/3$; $10$ fractional edges at $x_e = 1/2$ under simplex vertex selection) with **zero remaining violated DFJ cuts**, forcing the branch-and-bound state machine to branch and refute Hamiltonian feasibility (`SearchStatus.rejected`).
   - Empirically validates the hyperplane separation theorem `held_karp_strictly_contains_tsp_polytope` on $K_{10}$ under `petersenSepCost`: the Held-Karp LP achieves cost $0.0000$, whereas the minimum integral tour cost is $1.0000$.

2. **Ring-of-Triangles 3-SAT Gadget Explosion ($G_{\text{path}}$):**
   - Demonstrates that on the $3m$-vertex Ring-of-Triangles gadget graph $G_{\text{path}}(m)$, the initial degree-2 relaxation collapses into $m$ disconnected 0-cost triangles $F^{(0)} = \bigcup_{i=1}^m T_i$ ($\text{min-cut} = 0.0$).
   - Dynamic DFJ min-cut separation adds $m$ triangle subtour cuts at the root node, lifting the LP lower bound from $0.0$ to $m$. At the resulting half-integral LP point $x(e_{i,T}) = x(e_{i,F}) = 1/2$, every 3-SAT clause constraint $x(\overline{e}_{j,1}) + x(\overline{e}_{j,2}) + x(\overline{e}_{j,3}) \le 2$ is strictly satisfied ($0.5 + 0.5 + 0.5 = 1.5 \le 2.0$), rendering the continuous LP relaxation blind to global 3-SAT unsatisfiability across shallow tree depths.
   - Consequently, the `SolverState` branch-and-bound tree is forced to evaluate **exactly $2^m - 1 = 2^{|V|/3} - 1 = \Omega(2^{|V|/3})$** nodes on unsatisfiable instances (and $\Theta(2^{|V|/3})$ nodes on uniquely satisfiable instances), whereas the **Bounded Cycle-Separation Rank ($\kappa = 1$)** control family resolves in **1 node** across all sizes.

3. **Yannakakis DFJ Subtour Slack Matrix ($S_{\text{DFJ}}(n)$) & $P_{10}$ Cut Slack Profile (Phase 9):**
   - Constructs the exact $(2^n - 2) \times ((n-1)!/2)$ subtour slack matrix $S_{\text{DFJ}}[S, p] = \text{dfjSlack}(\text{tourPoint}(p), S)$ for $n \in \{4, 5, 6, 7\}$, empirically verifying non-negativity (`dfjSlack_nonneg_of_tour`, $\min S_{\text{DFJ}} = 0.0$), even-integer parity (`cyclic_cut_crossings_even`), and exact degree-cut tightness ($S[\{v\}, p] = 0$).
   - Profiles all $2^{10} - 2 = 1,022$ proper cuts of $P_{10}$ under `petersenFractional`, confirming that the **20 singleton/co-singleton degree cuts** ($|S| \in \{1, 9\}$) have **exact zero slack** (`petersen_dfjSlack_singleton_zero`), while all **1,002 non-trivial DFJ cuts** ($2 \le |S| \le 8$) have strictly positive interior slack $\ge 2/3 \approx 0.6667$ (`petersen_dfjSlack_nontrivial_ge_two_thirds`).

---

## 2. Benchmark 1: The 10-Vertex Petersen Graph ($P_{10}$) Integrality Gap

### 2.1 Continuous Polyhedral Verification (`HeldKarpPoint 10`)

| Property / Lean 4 Theorem | Measured Value | Target / Bound | Status |
| :--- | :---: | :---: | :---: |
| `petersenFractional_symmetric` ($\max_{u,v} |x_{uv} - x_{vu}|$) | `0.00e+00` | $= 0$ | **PASS** |
| `petersenFractional_loopless` ($\max_v |x_{vv}|$) | `0.00e+00` | $= 0$ | **PASS** |
| `petersenFractional_degrees` ($\max_v |\sum_{u \ne v} x_{vu} - 2|$) | `0.00e+00` | $= 0$ | **PASS** |
| `petersenFractional_subtours` (Stoer-Wagner Global Min-Cut) | `2.0000` | $\ge 2.0$ | **PASS** |
| `petersenFractional_subtours` (Edmonds-Karp All-Pairs $s$-$t$ Min-Cut) | `2.0000` | $\ge 2.0$ | **PASS** |
| Fractional Edges at $x_e = 2/3$ (`lp_two_thirds_stall`) | `15 / 15` | $x_e = 2/3 \;\forall e \in E(P_{10})$ | **STALL CONFIRMED** |

### 2.2 Branch-and-Cut Execution on $P_{10}$ and $K_{10}$ (`petersenSepCost`)

| Instance | $\|V\|$ | $\|E\|$ | Budget $B$ | Root LP Bound | Root Min-Cut | DFJ Cuts Added | LP Solves | B&B Nodes (`steps`) | Final Status | Best Integral Cost | Time (ms) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `Petersen_P10_Hypohamiltonian` | 10 | 15 | `10.0` | `10.0000` | `2.0000` | 12 | 15 | 7 (`8`) | `rejected` | `None` (Infeasible) | `31.89` |
| `Petersen_K10_SepCost_B0` | 10 | 45 | `0.0` | `0.0000` | `2.0000` | 12 | 17 | 9 (`10`) | `rejected` | `None` (Infeasible) | `42.00` |
| `Petersen_K10_SepCost_B1` | 10 | 45 | `1.0` | `0.0000` | `2.0000` | 4 | 7 | 5 (`5`) | `accepted` | `1.0000` | `19.89` |

---

## 3. Benchmark 2: Ring-of-Triangles 3-SAT Gadget Graph ($G_{\text{path}}$)

### 3.1 Exponential Node Count Explosion ($\Omega(2^{|V|/3})$) — Unsatisfiable 3-SAT Family

For each $m \in \{3, \dots, 9\}$ ($|V| = 3m$, $|E| = 5m$, budget $B = m$), the root degree-2 LP initially selects the $m$ disconnected triangles of cost $0.0$. Dynamic Stoer-Wagner separation adds $m$ DFJ subtour cuts at the root node, lifting the LP bound to $m$. The solver then explores the binary variable choices across the ring, evaluating **exactly $2^m - 1 = 2^{|V|/3} - 1$** nodes before proving `SearchStatus.rejected`:

| Triangles $m$ | Vertices $\|V\| = 3m$ | Edges $\|E\| = 5m$ | Budget $B$ | Root LP Bound | DFJ Cuts Added | Total LP Solves | B&B Nodes Evaluated | Theoretical $2^{\|V\|/3} - 1$ | Growth Factor ($\Delta m = +1$) | Status | Time (ms) |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 3 | 9 | 15 | `3.0` | `3.0000` | 3 | 8 | **7** | 7 | — | `rejected` | `17.69` |
| 4 | 12 | 20 | `4.0` | `4.0000` | 4 | 16 | **15** | 15 | `2.14x` | `rejected` | `37.44` |
| 5 | 15 | 25 | `5.0` | `5.0000` | 5 | 32 | **31** | 31 | `2.07x` | `rejected` | `82.91` |
| 6 | 18 | 30 | `6.0` | `6.0000` | 6 | 64 | **63** | 63 | `2.03x` | `rejected` | `183.30` |
| 7 | 21 | 35 | `7.0` | `7.0000` | 7 | 128 | **127** | 127 | `2.02x` | `rejected` | `398.57` |
| 8 | 24 | 40 | `8.0` | `8.0000` | 8 | 256 | **255** | 255 | `2.01x` | `rejected` | `897.99` |
| 9 | 27 | 45 | `9.0` | `9.0000` | 9 | 512 | **511** | 511 | `2.00x` | `rejected` | `2053.13` |

### 3.2 Uniquely Satisfiable 3-SAT Gadget vs. Bounded Cycle-Separation Rank ($\kappa = 1$) Control

Comparing the adversarial `UNIQUE-SAT` 3-SAT gadget family against the bounded rank ($\kappa = 1$) necklace graph on the identical $3m$-vertex topology demonstrates the sharp dichotomy between unconstrained 3-SAT subtour patching ($\Omega(2^{|V|/3})$ nodes) and bounded Cycle-Separation Rank (`polynomial_termination_rank_one`, constant $1$ node):

| Triangles $m$ | Vertices $\|V\| = 3m$ | `UNIQUE-SAT` Nodes | `UNIQUE-SAT` Cuts | `UNIQUE-SAT` Status | `UNIQUE-SAT` Time (ms) | `Rank-1` ($\kappa = 1$) Nodes | `Rank-1` Cuts | `Rank-1` Status | `Rank-1` Time (ms) |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 3 | 9 | **7** | 3 | `accepted` ($c=3.0$) | `18.63` | **1** | 3 | `accepted` ($c=3.0$) | `5.03` |
| 4 | 12 | **13** | 4 | `accepted` ($c=4.0$) | `34.46` | **1** | 4 | `accepted` ($c=4.0$) | `5.78` |
| 5 | 15 | **25** | 5 | `accepted` ($c=5.0$) | `68.55` | **1** | 5 | `accepted` ($c=5.0$) | `5.55` |
| 6 | 18 | **57** | 6 | `accepted` ($c=6.0$) | `160.96` | **1** | 6 | `accepted` ($c=6.0$) | `6.27` |
| 7 | 21 | **121** | 7 | `accepted` ($c=7.0$) | `374.71` | **1** | 7 | `accepted` ($c=7.0$) | `7.37` |
| 8 | 24 | **241** | 8 | `accepted` ($c=8.0$) | `877.82` | **1** | 8 | `accepted` ($c=8.0$) | `9.13` |
| 9 | 27 | **505** | 9 | `accepted` ($c=9.0$) | `2341.04` | **1** | 9 | `accepted` ($c=9.0$) | `9.04` |

---

## 4. Benchmark 3: Complete Graphs $K_n$ — Stoer-Wagner vs. Edmonds-Karp Separation

On clustered Euclidean complete graphs $K_n$ ($n \in \{6, 8, 10, 12\}$) where the initial degree-2 relaxation splits into two disconnected cluster subtours, both `stoer_wagner` and `edmonds_karp` dynamically separate the violated DFJ subtour constraints at the root node and recover the exact optimal tour in 1 branch-and-bound node:

| Instance | $\|V\|$ | $\|E\|$ | Oracle | Root LP Bound | DFJ Cuts Added | LP Solves | B&B Nodes | Optimal Tour Cost | Status | Time (ms) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `Clustered_K6` | 6 | 15 | Stoer-Wagner | `253.0` | 2 | 2 | 1 | `253.0` | `accepted` | `5.08` |
| `Clustered_K6` | 6 | 15 | Edmonds-Karp | `253.0` | 2 | 2 | 1 | `253.0` | `accepted` | `4.67` |
| `Clustered_K8` | 8 | 28 | Stoer-Wagner | `264.0` | 4 | 3 | 1 | `264.0` | `accepted` | `10.90` |
| `Clustered_K8` | 8 | 28 | Edmonds-Karp | `264.0` | 4 | 3 | 1 | `264.0` | `accepted` | `10.59` |
| `Clustered_K10` | 10 | 45 | Stoer-Wagner | `267.0` | 2 | 2 | 1 | `267.0` | `accepted` | `6.24` |
| `Clustered_K10` | 10 | 45 | Edmonds-Karp | `267.0` | 2 | 2 | 1 | `267.0` | `accepted` | `5.73` |
| `Clustered_K12` | 12 | 66 | Stoer-Wagner | `270.0` | 2 | 2 | 1 | `270.0` | `accepted` | `6.96` |
| `Clustered_K12` | 12 | 66 | Edmonds-Karp | `270.0` | 2 | 2 | 1 | `270.0` | `accepted` | `6.53` |

---

## 5. Benchmark 4: Yannakakis DFJ Subtour Slack Matrix ($S_{\text{DFJ}}(n)$) & $P_{10}$ Cut Slack Profile

### 5.1 Complete Graph Subtour Slack Matrices $S_{\text{DFJ}}(n)$ ($n \in \{4, 5, 6, 7\}$)

Directly mirroring `OAI.TSP.DFJCut`, `OAI.TSP.dfjSlack`, `OAI.TSP.dfjSlack_nonneg_of_tour`, and `OAI.TSP.HasAffineLift` in [`TSPComplexity.lean`](../TSPComplexity.lean), `compute_yannakakis_dfj_slack_matrix(n)` evaluates $S_{\text{DFJ}}[S, p] = |\delta(S) \cap E(p)| - 2$ across all $2^n - 2$ proper non-empty cuts $S \subsetneq V$ and all $(n-1)!/2$ distinct undirected Hamiltonian tour extreme points `tourPoint p`:

| Instance | DFJ Cuts ($2^n - 2$) | Non-Trivial Cuts ($2 \le \|S\| \le n-2$) | Distinct Tour Vertices ($(n-1)!/2$) | Permutations ($n!$) | $\min S_{\text{DFJ}}$ (`dfjSlack_nonneg_of_tour`) | $\max S_{\text{DFJ}}$ | Even Integers (`cyclic_cut_crossings_even`) | Singleton Cuts $= 0$ | Linear Rank $\text{rank}_{\mathbb{R}}(S_{\text{DFJ}})$ | Theoretical $\binom{n-1}{2}$ | Tight Entry Fraction ($S=0$) | Time (ms) |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| $K_4$ | 14 | 6 | 3 | 24 | `0.0` | `2.0` | `True` | `True` | **3** | 3 | `0.8571` | `0.45` |
| $K_5$ | 30 | 20 | 12 | 120 | `0.0` | `2.0` | `True` | `True` | **6** | 6 | `0.6667` | `0.83` |
| $K_6$ | 62 | 50 | 60 | 720 | `0.0` | `4.0` | `True` | `True` | **10** | 10 | `0.4839` | `2.96` |
| $K_7$ | 126 | 112 | 360 | 5,040 | `0.0` | `4.0` | `True` | `True` | **15** | 15 | `0.3333` | `31.86` |

* **Algebraic vs. Positive Cone Rank Dichotomy:** Over unconstrained $\mathbb{R}$, the linear rank of $S_{\text{DFJ}}(n)$ equals $\binom{n-1}{2} = \dim(P_{\text{TSP}}(n)) + 1 \in \{3, 6, 10, 15\}$ (reflecting the unconstrained algebraic dimension of the subtour slack space, see [`MONOGRAPH.md`](../MONOGRAPH.md) §2.2). In contrast, when factorized through positive semidefinite matrices $A(S), B(p) \succeq 0$ (`HasAffineLift.slack_factorization`), the cone positivity constraints force super-polynomial extension complexity $r = 2^{\Omega(n^{1/4})}$ (`tsp_extension_complexity_lower_bound`).

### 5.2 Complete DFJ Cut Slack Profile of `petersenFractional` ($P_{10}$, $1,022$ Proper Cuts)

Evaluating `dfjSlack petersenFractional S` across all $2^{10} - 2 = 1,022$ proper cuts $S \in \text{DFJCut}(10)$ empirically confirms `petersen_dfjSlack_singleton_zero` and `petersen_dfjSlack_nontrivial_ge_two_thirds`:

| Cut Family in $\text{DFJCut}(10)$ | Cut Count | Cut Edge Count $\|\delta_{P_{10}}(S)\|$ | Continuous Capacity $x(\delta(S))$ | DFJ Slack $x(\delta(S)) - 2$ | Corresponding Lean 4 Theorem |
| :--- | :---: | :---: | :---: | :---: | :--- |
| Singleton & Co-Singleton Cuts ($\|S\| \in \{1, 9\}$) | **20** | $3$ | `2.0000` | **`0.0000` (Tight)** | `petersen_dfjSlack_singleton_zero` |
| 4-Edge Non-Trivial Cuts ($\|S\| \in \{2, 8\}$ adjacent) | **30** | $4$ | `2.6667` | `0.6667` ($2/3$) | `petersen_dfjSlack_nontrivial_ge_two_thirds` |
| 5-Edge Non-Trivial Cuts (e.g. induced $C_5$ / $P_3$) | **72** | $5$ | `3.3333` | `1.3333` ($4/3$) | `petersen_dfjSlack_nontrivial_ge_two_thirds` |
| Higher-Capacity Cuts ($\|\delta_{P_{10}}(S)\| \in \{6\dots 12\}$) | **900** | $6 \dots 12$ | `4.0000` – `8.0000` | `2.0000` – `6.0000` | `petersen_dfjSlack_nontrivial_ge_two_thirds` |
| **Total Proper Non-Empty Cuts ($\text{DFJCut}(10)$)** | **1,022** | $3 \dots 12$ | `2.0000` – `8.0000` | `0.0000` – `6.0000` | `dfjSlack_nonneg_of_heldKarp` |

---

## 6. Reproducibility

To reproduce all benchmark tables and verify the outputs:

```bash
python benchmarks/adversarial_instances.py
```

