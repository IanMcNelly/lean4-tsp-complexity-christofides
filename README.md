# Formalizing the Christofides–Serdyukov 3/2-Approximation Algorithm and the Held–Karp Petersen Integrality Gap in Lean 4

[![Palomar Registry](https://img.shields.io/badge/Palomar_Registry-PALOMAR--2026--10--30--000013-success.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000013&version=1)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.28.0-blue.svg)](https://leanprover.github.io/)
[![Zero Sorries](https://img.shields.io/badge/Sorries-0-brightgreen.svg)]()
[![Declarations](https://img.shields.io/badge/Verified_Decls-413-success.svg)]()
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Docs](https://img.shields.io/badge/Docs-Interactive_Proof_Explorer-purple.svg)](https://ianmcnelly.github.io/lean4-tsp-complexity-christofides/)

This repository contains a machine-checked Lean 4 (v4.28.0 / Mathlib) formalization of the **Christofides–Serdyukov $3/2$-approximation algorithm** for the metric Traveling Salesperson Problem (`Christofides.lean`, accepted and indexed in the [Palomar Formalization Registry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000013&version=1) under ID `PALOMAR-2026-10-30-000013`) together with unconditional polyhedral companion theorems on the **Held–Karp LP relaxation and the 10-vertex Petersen graph ($P_{10}$) integrality gap** (`TSPComplexity.lean` §§5–6).

## Preprints & Manuscripts (`latex/`)

- **Research Note (1-column arXiv / Preprint format):** [`latex/research_note.pdf`](latex/research_note.pdf) (source: [`latex/research_note.tex`](latex/research_note.tex) + [`latex/note_body.tex`](latex/note_body.tex))
- **Proof Pearl (2-column CPP / ITP Short Paper format):** [`latex/proof_pearl.pdf`](latex/proof_pearl.pdf) (source: [`latex/proof_pearl.tex`](latex/proof_pearl.tex) + [`latex/note_body.tex`](latex/note_body.tex))
- **Extended Technical Report:** [`latex/monograph.pdf`](latex/monograph.pdf) (source: [`latex/monograph.tex`](latex/monograph.tex))

---

## 1. Core Unconditional Results

### 1.1 The Christofides–Serdyukov $3/2$-Approximation Theorem (`Christofides.lean`)
Registered in the Palomar Formalization Registry ([`PALOMAR-2026-10-30-000013`](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000013&version=1)) and verified by [`Christofides.json`](Christofides.json) against [`ChallengeChristofides.lean`](ChallengeChristofides.lean):

- **Constructive Optimal Tour & Finite Existence:** Avoids non-constructive `Classical.choose` on optimal tours via `Finset.min'` over the finite nonempty subtype of Hamiltonian tours (`optTourCost`, `optTourCost_le_tourCost`), and proves finite existence of a minimum spanning tree (`exists_mst`) and a minimum-weight perfect matching on odd-degree vertices (`exists_minWeightMatching`).
- **MST Lower Bound (`MSTCost_le_OPT`):** Deleting the closing edge of any Hamiltonian tour yields an $(n-1)$-edge acyclic spanning tree of cost at most $\mathrm{OPT}$.
- **Handshaking Parity & $1/2 \cdot \mathrm{OPT}$ Matching Bound (`even_card_oddDegreeVertices`, `matchingCost_le_half_OPT`):** Any loopless graph has an even number of odd-degree vertices (`even_card_oddDegreeVertices`). Shortcutting an optimal tour onto the $2k$ odd-degree vertices of $T$ and decomposing the resulting cycle into two complementary perfect matchings `evenMatching` and `oddMatching` (`cycle_matchings_cost_sum`) yields $2 \cdot \mathrm{matchingCost}(c, M) \le \mathrm{optTourCost}(c)$.
- **Constructive Hierholzer Cycle-Splicing & Shortcutting (`exists_eulerianCircuit`, `christofides_certificate_approx_ratio_unconditional`):** Combines $T$ and $M$ into an even-degree Eulerian multigraph (`multigraph_degree_even`), constructs an Eulerian circuit by strong induction on unused multigraph edges (`eulerianWalkInduction_holds`), and shortcuts duplicate vertices via `List.eraseDups` (`shortcutCircuit_isTour`, `shortcut_tourCost_le_circuitCost`) to prove:
  $$2 \cdot \mathrm{tourCost}(c, \mathrm{christofidesTour}(\mathrm{cert})) \le 3 \cdot \mathrm{optTourCost}(c) \quad\text{and}\quad \mathrm{tourCost}(c, \pi) \le \frac{3}{2}\,\mathrm{optTourCost}(c).$$

### 1.2 Held–Karp Polytope & Petersen $P_{10}$ Integrality Gap (`TSPComplexity.lean` §§5–6)
- **$\mathbb{Z}_2$ Telescoping Proof of the DFJ Cut Bound (`dfj_subtour_cut_bound`):** Re-indexing signed cut-indicator differences along the cyclic shift bijection `cycleNextEquiv : Fin n ≃ Fin n` shows $\sum_i \Delta_i = 0 \in \mathbb{Z}$; projecting via $|z| \equiv z \pmod 2$ to `ZMod 2` proves every Hamiltonian tour crosses any proper non-empty cut $\emptyset \subsetneq S \subsetneq V$ an even number of times, and hence at least twice.
- **Held–Karp LP Embedding (`tour_is_held_karp_point`, `fractionalCost_tourPoint_le_tourCost`):** Every Hamiltonian tour embeds into the continuous Held–Karp relaxation `HeldKarpPoint n`, providing a valid lower bound for all symmetric cost functions.
- **Strict Polytope Separation & $11/10$ Metric Gap on $P_{10}$ (`petersen_strictly_separates_held_karp`, `petersen_heldKarp_metric_integrality_gap`):** Setting $x_e = 2/3$ on the 15 edges of the 10-vertex Petersen graph $P_{10}$ satisfies all degree-2 equations and all $2^{10}-2 = 1{,}022$ DFJ subtour cuts (`petersenHK`), with zero slack on singleton cuts (`petersen_dfjSlack_singleton_zero`) and slack $\ge 2/3$ on non-trivial cuts (`petersen_dfjSlack_nontrivial_ge_two_thirds`). Kernel evaluation of length-10 closed walks certifies that $P_{10}$ is non-Hamiltonian (`petersen_no_hamiltonian_tour`), separating `HeldKarpPoint 10` from the integral TSP polytope (`held_karp_strictly_contains_tsp_polytope`) and yielding an unconditional $11/10$ graphic metric integrality gap (`petersen_heldKarp_metric_integrality_gap`) under the shortest-path metric `petersenMetricCost`.
- **Yannakakis Slack Non-Negativity (`hasAffineLift_trace_nonneg`):** Any affine positive semidefinite (PSD) lift of the DFJ slack matrix has non-negative trace inner products across all cuts and tours.

### 1.3 Auxiliary & Conditional Specifications (`TSPComplexity.lean` §§1–4, §6c, §§7–8)
For transparency, the remaining sections of `TSPComplexity.lean` contain auxiliary state-machine, reduction, and conditional specifications:
- **Hamiltonian Cycle $\le_p$ Decision TSP (`Reduction.hc_to_tsp_reduction_correct`):** Unconditional polynomial reduction assigning cost $0$ to graph edges and $1$ to non-edges with budget $B = 0$, plus computable variable-triangle orientation codecs (`orientSingleTriangle`, `tourReadsTrue_orientSingleTriangle`) and a sparse necklace graph with certified non-completeness (`sparseNecklaceGraph_six_not_complete`).
- **Fuel-Bounded Permutation-Frontier Verifier (§§3–4, §8):** Models a fuel-bounded list scanner `SolverState` over candidate permutations (`queue_clearance_halts`, `tsp_soundness`, `tsp_completeness`). Note that in `StructuralRank` (§4), the queue bound $n! \le n^1$ on the full permutation list restricts `k = 1` instances to $n \le 2$, while `PrunedStructuralRank` (§8) packages frontier completeness as a structure hypothesis to model external support pruning.
- **Conditional Wrappers (§6c, §7):** `tsp_extension_complexity_lower_bound` proves Archimedean ceiling domination (`rpow_lt_natPow_ceil_succ`) conditioned on the Fiorini–Rothvoß scaling hypothesis `SatisfiesFioriniRothvossBound`, and `sat_to_tsp_reduction_correct` proves 3-SAT $\le_p$ Decision TSP conditioned on an abstract `TSPGadget` interface.

---

## 2. Directory Structure

```
tsp_research/
├── README.md                          # Project overview and verification inventory (this file)
├── formalization.yaml                 # Palomar Registry v0.4 metadata
├── comparator.json                    # Default Lean Comparator config (ChallengeChristofides -> Christofides)
├── Christofides.json                  # Palomar Comparator config for Christofides 3/2-Approximation
├── TSPComplexity.json                 # Comparator config for TSPComplexity declarations
├── ChallengeChristofides.lean         # Palomar challenge statement module for Christofides (15 theorems)
├── ChallengeTSPComplexity.lean        # Challenge statement module for TSPComplexity (24 theorems)
├── Christofides.lean                  # Christofides 3/2-Approximation formalization (2,735 LOC; 178 decls; 0 sorries)
├── TSPComplexity.lean                 # Polyhedral & complexity formalization (3,119 LOC; 235 decls; 0 sorries)
├── lakefile.lean                      # Lean 4 Lake package configuration
├── lean-toolchain                     # Pinned Lean 4 toolchain (v4.28.0)
├── latex/                             # LaTeX manuscripts & compiled PDFs
│   ├── note_body.tex                  # Shared manuscript body for research_note.tex and proof_pearl.tex
│   ├── research_note.tex              # 1-column arXiv / Research Note wrapper
│   ├── research_note.pdf              # Compiled 1-column Research Note PDF
│   ├── proof_pearl.tex                # 2-column CPP / ITP Proof Pearl wrapper
│   ├── proof_pearl.pdf                # Compiled 2-column Proof Pearl PDF
│   ├── monograph.tex                  # Extended technical report source
│   ├── monograph.pdf                  # Extended technical report PDF
│   └── README.md                      # Compilation and arXiv / CPP submission instructions
├── docs/                              # Interactive HTML proof explorer
│   ├── index.html                     # Multi-module interactive proof explorer
│   ├── Christofides.html              # Standalone explorer for Christofides.lean
│   └── TSPComplexity.html             # Standalone explorer for TSPComplexity.lean
├── scripts/                           # Build verification & documentation scripts
└── benchmarks/                        # Python reference scripts & empirical checks
```

---

## 3. Section-by-Section Declaration Summary

### 3.1 `Christofides.lean` (178 Verified Declarations, 0 `sorry`s)

| Section | Lines | Theorems / Lemmas | Definitions / Structures | `sorry`s |
| :--- | :---: | :---: | :---: | :---: |
| **§§1–4. Metric Cost Spaces, Walk Contraction & Constructive OPT** | 52–402 | 22 | 12 | **0** |
| **§§5–7. Spanning Trees, Hamiltonian Path Witness & `MSTCost_le_OPT`** | 403–709 | 17 | 7 | **0** |
| **§§8–10. Handshaking Lemma & Odd-Degree Vertex Parity (`even_card_oddDegreeVertices`)** | 710–841 | 9 | 2 | **0** |
| **§§11–14. Tour Projection, Alternating Matchings & `matchingCost_le_half_OPT`** | 842–1630 | 36 | 8 | **0** |
| **§§15–18. Eulerian Multigraphs, Shortcutting & `shortcut_tourCost_le_circuitCost`** | 1631–1966 | 18 | 6 | **0** |
| **§§19–20. Constructive Hierholzer Induction & Unconditional $3/2$-Approximation** | 1967–2735 | 32 | 5 | **0** |
| **Total (`IJM.TSP.Christofides`)** | **1–2735** | **134 (138 incl. inline)** | **40** | **0** |

### 3.2 `TSPComplexity.lean` (235 Verified Declarations, 0 `sorry`s)

| Section | Lines | Theorems / Lemmas | Definitions / Structures | `sorry`s |
| :--- | :---: | :---: | :---: | :---: |
| **§§1–2. Discrete Graph, Tour & Cost Foundations** | 35–115 | 8 | 12 | **0** |
| **§§3–4. Fuel-Bounded Permutation-Frontier Verifier & `StructuralRank`** | 129–607 | 20 | 12 | **0** |
| **§5. $\mathbb{Z}_2$ Cyclic Parity & DFJ Subtour Cut Bound (`dfj_subtour_cut_bound`)** | 616–925 | 18 | 8 | **0** |
| **§6. Held–Karp LP, Petersen $P_{10}$ Metric Gap & Slack Non-Negativity** | 1034–2221 | 53 | 20 | **0** |
| **§7. $\mathrm{HC} \le_p \mathrm{TSP}$, Triangle Codecs & Conditional `TSPGadget`** | 2241–2646 | 33 | 24 | **0** |
| **§8. Sparse Necklace Graph & `PrunedStructuralRank`** | 2687–3067 | 19 | 8 | **0** |
| **Total (`IJM.TSP`)** | **1–3119** | **151** | **84** | **0** |

---

## 4. Verification & Reproducibility

To verify the Lean 4 modules directly with Lake:

```bash
lake env lean Christofides.lean
lake env lean TSPComplexity.lean
```

To run the full verification script (zero-`sorry` audit, Python reference suites, and Lean kernel check):

```powershell
# Windows PowerShell
powershell -ExecutionPolicy Bypass -File ./scripts/verify_build.ps1
```

```bash
# Linux / macOS
bash ./scripts/verify_build.sh
```

---

## 5. Citation

If you reference this formalization or the accompanying research note, please cite:

```bibtex
@misc{mcnelly2026christofides,
  author       = {McNelly, Ian},
  title        = {Formalizing the {Christofides--Serdyukov} $3/2$-Approximation Algorithm and the {Held--Karp} {Petersen} Integrality Gap in {Lean~4}},
  year         = {2026},
  howpublished = {Palomar Formalization Registry (\texttt{PALOMAR-2026-10-30-000013}), \url{https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000013&version=1}},
  note         = {Source code and preprint at \url{https://github.com/imcn23/tsp}}
}
```
