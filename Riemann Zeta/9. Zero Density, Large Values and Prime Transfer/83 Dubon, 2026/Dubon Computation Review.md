# Dubon 2026 — computation and numerical review

**GOAL ACTIVE — 0/20 proof gates complete.** No author-code or numerical replay is claimed. Lean implementation is tracked separately in the Reproduction Manifest.

The frozen arXiv source tarball has exactly two regular files: `00README.json` and `Zero_Density_Concentration_for_Dirichlet_Polynomials.tex`. There are no ancillary scripts, notebooks, tables of certified numerical bounds or companion-code instructions in that archive. [Archive evidence](Tools/author_code_observation.json) records both member hashes; the inspection tool compares those bytes to the extracted files without executing anything.

The proof is analytic and asymptotic. Lemma 4.1's constants depend on K and need not be optimized numerically. The Gaussian/intermediate/far-tail Fourier estimates and negative-log integral are uniform mathematical assertions, not sampling problems. A plot of zeros or random Steinhaus simulation would be exploratory only and would not prove a height limit, coefficient-uniform small-ball bound, weak convergence or Sato–Tate.

No author-code replay runner was copied from Project 78: its AFE optimizer has no role in this paper. The matching template role is an archive/code-availability inspection tool. Any future exploratory programs must be separate from source artifacts and from Lean proof acceptance. External optimizer output, floating-point bounds and runtime checks must never become assumed lemmas or unsafe proof evidence.

PDFium 5.14.0 was used in ignored task scratch space to inspect the source PDF and primary references. It is a research-only reader, not a selected Lean/project dependency. It extracted the 28-page Dubon PDF, 59-page BLGG preprint, 31-page Andersson preprint and 143-page Jessen–Tornehave paper. Rendered theorem pages were checked against the TeX and extracted text; no PDF or TeX bytes were edited.
