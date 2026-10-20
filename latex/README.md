# LaTeX Archival Monograph Packaging (`latex/`)

This directory contains the peer-review and arXiv-compatible LaTeX source for the archival monograph:

- **`monograph.tex`**: Self-contained LaTeX document based on `MONOGRAPH.md`, with:
  - Vector TikZ graph figure for the 10-vertex Petersen Graph ($P_{10}$) integrality gap witness ($x_e = 2/3$).
  - Vector TikZ graph figure for the Ring-of-Triangles 3-SAT Gadget Graph ($G_{\text{path}}$) with variable 2-opt bridges and clause-interlock penalties ($c_{\text{penalty}} = B + 1$).
  - Vector TikZ diagram for the three formalized mathematical obstructions (Polyhedral Integrality Gaps on $P_{10}$, PSD Extension Complexity & Yannakakis Slack Factorization, and Combinatorial NP-Hardness Reductions).
  - Vector TikZ plot for the Branch-and-Bound search node explosion ($2^m - 1$ vs. 1) and the Christofides-Serdyukov 3/2-approximation pipeline.
  - Complete formal theorem statements and proof sketches matching `TSPComplexity.lean` (196 declarations) and `Christofides.lean` (141 declarations; 337 total declarations).
  - Comprehensive bibliography with 10 seminal citations.

## Compilation Instructions

### Local Compilation (pdfLaTeX)
```bash
cd latex
pdflatex -interaction=nonstopmode monograph.tex
pdflatex -interaction=nonstopmode monograph.tex
```

### arXiv / Overleaf Submission
The file `monograph.tex` is fully self-contained, standard `pdfLaTeX`-compatible, and requires no external proprietary packages or shell escapes (`-shell-escape` is NOT required; listings is used instead of minted for 100% arXiv compatibility).
