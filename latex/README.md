# LaTeX Manuscripts (`tsp_research/latex`)

This directory contains the LaTeX manuscripts accompanying the Lean 4 formalization of the Christofides--Serdyukov $3/2$-approximation algorithm (`Christofides.lean`, registered in the Palomar Formalization Registry under [`PALOMAR-2026-10-30-000013`](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000013&version=1)) and the Held--Karp / Petersen $P_{10}$ polyhedral separation theorems (`TSPComplexity.lean` §§5–6).

## Primary Manuscripts (Research Note & Proof Pearl)

Both primary manuscripts share a single unified source body (`note_body.tex`) so that mathematical statements, Lean 4 identifiers, and declaration tables remain synchronized across formats:

| File | Output PDF | Format & Target Venue |
| :--- | :--- | :--- |
| [`note_body.tex`](note_body.tex) | *(shared input)* | Core manuscript body (§§1–6, Table 1 declaration inventory, bibliography) |
| [`research_note.tex`](research_note.tex) | [`research_note.pdf`](research_note.pdf) | **1-column `article` (11pt)** — Preprint format for arXiv (`cs.LO` / `cs.DS` / `math.CO`), GitHub, and AFM |
| [`proof_pearl.tex`](proof_pearl.tex) | [`proof_pearl.pdf`](proof_pearl.pdf) | **2-column `article` (10pt)** — Proof Pearl / Short Paper format for ACM CPP or ITP |
| [`monograph.tex`](monograph.tex) | [`monograph.pdf`](monograph.pdf) | Extended archival technical report covering all repository declarations |

## Building the PDFs

Run `pdflatex` twice on either wrapper file to resolve cross-references:

```bash
cd latex
pdflatex -interaction=nonstopmode research_note.tex
pdflatex -interaction=nonstopmode research_note.tex

pdflatex -interaction=nonstopmode proof_pearl.tex
pdflatex -interaction=nonstopmode proof_pearl.tex
```

## Switching `proof_pearl.tex` to `acmart` for ACM CPP Submission

For direct submission to the ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP) Proof Pearl / Short Paper track, replace the `\documentclass` line at the top of `proof_pearl.tex` with:

```latex
\documentclass[sigplan,10pt,review,anonymous]{acmart}
```

## Packaging for arXiv Submission

When uploading to arXiv (`cs.LO` primary, cross-listed to `cs.DS` and `math.CO`), include only the two source files:
- `research_note.tex`
- `note_body.tex`

The bibliography is embedded directly via `\begin{thebibliography}` inside `note_body.tex`, requiring no external `.bib` or `.bbl` build step on arXiv's TeX Live builder.
