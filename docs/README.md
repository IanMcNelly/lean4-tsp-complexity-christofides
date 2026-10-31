# Interactive Documentation & DocGen (`docs/`)

This directory houses the interactive HTML documentation and explorer for the `IJM.TSP.TSPComplexity` and `IJM.TSP.Christofides` formalizations in Lean 4.

## Features of the Interactive Proof Explorer

1. **Pre-rendered Single-Page Application (`index.html`, `TSPComplexity.html`, & `Christofides.html`)**:
   - Zero-dependency static HTML view playable directly in any browser (Chromium, Firefox, Safari, Edge).
   - Instant live search by declaration name, type signature, or informal mathematical concept.
   - Interactive category filtering across all **413 declarations** (235 in `TSPComplexity.lean` and 178 in `Christofides.lean`):
     - **All Declarations**: Full index of all 235 declarations in `TSPComplexity` and 178 declarations in `Christofides`.
     - **Landmark Challenges**: Highlights the 24 synchronized comparator theorems from `TSPComplexity.json` and 15 from `Christofides.json` (39 total).
     - **Theorems & Lemmas**: All 289 machine-checked proofs (151 in `TSPComplexity` and 138 in `Christofides`).
     - **Definitions & Structures**: All 124 combinatorial, polyhedral, certificate, and state machine structures (84 in `TSPComplexity` and 40 in `Christofides`).
   - **Collapsible Proof Trees**: Click *Show Proof* on any theorem or lemma to unfold the exact Lean 4 proof tactics.
   - **Syntax Highlighting**: Custom color-coded highlighting matching standard Lean 4 keywords, types, and mathematical symbols.
   - **Dark / Light Theme Toggle**: Persistent theme switching with optimized contrast.

## Generating Documentation

To regenerate the static HTML documentation from `TSPComplexity.lean` and `Christofides.lean`:
```bash
python scripts/generate_docs.py
```

## Lean 4 Doc-Gen4 Pipeline

For upstream `doc-gen4` documentation generation with Lake:
```bash
lake update
lake build :docs
```
Toolchain and dependency configurations are pinned in:
- `lean-toolchain` (`leanprover/lean4:v4.35.0-rc2`)
- `lakefile.lean` (requiring canonical Mathlib `v4.35.0-rc2` matching Palomar Registry multi-kernel specifications)
