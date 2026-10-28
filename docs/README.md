# Interactive Documentation & DocGen (`docs/`)

This directory houses the interactive HTML documentation and explorer for the `IJM.TSP.TSPComplexity` and `IJM.TSP.Christofides` formalizations in Lean 4.

## Features of the Interactive Proof Explorer

1. **Pre-rendered Single-Page Application (`index.html`, `TSPComplexity.html`, & `Christofides.html`)**:
   - Zero-dependency static HTML view playable directly in any browser (Chromium, Firefox, Safari, Edge).
   - Instant live search by declaration name, type signature, or informal mathematical concept.
   - Interactive category filtering across all **337 declarations** (196 in `TSPComplexity.lean` and 141 in `Christofides.lean`):
     - **All Declarations**: Full index of all 196 declarations in `TSPComplexity` and 141 declarations in `Christofides`.
     - **Landmark Challenges**: Highlights the 15 synchronized comparator theorems from `TSPComplexity.json` and 13 from `Christofides.json` (28 total).
     - **Theorems & Lemmas**: All 227 machine-checked proofs (123 in `TSPComplexity` and 104 in `Christofides`).
     - **Definitions & Structures**: All 110 combinatorial, polyhedral, certificate, and state machine structures (73 in `TSPComplexity` and 37 in `Christofides`).
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
- `lean-toolchain` (`leanprover/lean4:v4.34.1`)
- `lakefile.lean` (requiring `doc-gen4` at `953c8992d174b4e56955e01e101d46668c68f2bb` and Mathlib)
