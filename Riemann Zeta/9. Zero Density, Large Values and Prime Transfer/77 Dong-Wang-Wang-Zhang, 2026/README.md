# Dong–Wang–Wang–Zhang 2026: active formalization

Research snapshot and explicit goal activation: **4 October 2026**. Status: **ACTIVE DEVELOPMENT; 7/20 proof gates complete (DWWZ-01/03/05/06/07/08/10).** The isolated Lean package proves the actual-sum interfaces, maximizing-twist existence, prime-phase estimates and the phase-specialized source comparison (2.2), including its coefficient mean/tail/Euler-product inputs. The actual summatory transforms, sharp full-series derivative mean square and two-sided far tail are proved. Poisson reproduction transports the original maximizer rightward and supplies a full weighted-summatory mean-square bound with that same maximizer. Both main theorems and full hybrid Halász (2.1) remain unproved. The phase-specialized all-real Lipschitz estimate and full Lemma 2.2 are kernel-checked and passed combined BAT/audit acceptance.

Quartic-cell sieve smoothing, damping-parameter integration and the actual Euler bound prove ordinary mean-value control by the prime distance. `exists_large_sum_twist_bounds` now proves three clauses of Lemma 2.2 at one actual maximizing twist: `|t₀| ≤ 4N`, `M ≤ (1/100) log log x + log log log x + C`, and reversed comparison error at most `4x/(log x)^(3/4)`. Constants and threshold are absolute. Uniform Lipschitz and the full combined Lemma 2.2 are kernel-checked in `DilationLipschitz`; DWWZ-05/06 are DONE after both BATs and the semantic audit passed. The direct ordinary-mean-value proof is not a claim to full hybrid source (2.1).

`TwoPointEuler` now proves actual prime-correlation and two-point zeta bounds using the installed, proved `MediumPNT`. A finite trigonometric majorant of mean `75/113<2/3` yields off-frequency control at the same source maximizer, with the prime scale chosen internally. The optimized dilation-factor bound and its rightward transport are also proved. `DilationMeanSquare` now proves the actual weighted-difference Parseval identity and full near/far mean-square consumer. `DilationSmoothing` now proves the actual difference's pointwise-to-average estimate, with active-cutoff floor control and logarithmic dilation loss. The capped mean-square bound retains `min(M_A+16,4/δ)`. `DilationAssembly` proves the actual same-maximizer bound with its damping integral evaluated by an arbitrarily small power loss. `DilationLipschitz` now proves scalar absorption, the all-real cutoff estimate and full Lemma 2.2; combined BAT/audit acceptance passed. This is a supporting specialization, not a proof of the optimal GS03 `2/π` estimate.

Paper: Zikang Dong, Ruihua Wang, Weijia Wang and Hao Zhang, *Large zeta sums and zeros of the Riemann zeta function*, [arXiv:2608.31060v1](https://arxiv.org/abs/2608.31060v1), submitted 31 August 2026, 19 pages. The arXiv history and first author's publication page still list this preprint at the research date; no later version or journal publication was identified.

The main target is a pointwise inverse theorem: a large value of the actual sum `S(x,t) = Σ_{1≤n≤x} n^(it)` forces many nontrivial zeta zeros, with analytic multiplicity, in a specified open disk near height `t`. A second theorem deduces cancellation from a local zero-window hypothesis. These are not the exponent-pair/density-table targets of node 63.

## Uniform zeta bound

`norm_zeta_left_strip_le` in `ZetaUniformBounds.lean`
proves Lemma 3.1 with constant 8, uniformly for every real height and
`0<λ≤1/2`. The installed Euler–Maclaurin continuation is consumed with its
pole explicit. The module and four new semantic regressions compile cleanly;
DWWZ-07 is DONE after both BATs and the exact consumer audit passed.

## Xi and the real logarithmic derivative

The actual xi divisor, critical-strip bounds, exact zeta multiplicity fibers,
reflection and genus-one summability are proved. The source real logarithmic
derivative and its exact zeta/gamma decomposition compile, with no assumed
factorization or zero-sum identity. Seven new regressions pass; DWWZ-08 is DONE after
combined BAT/audit and semantic acceptance. Disk/window count bridges and the quantitative
zero-repulsion/zero-sum bounds remain open.

## Exact Gaussian transform

`source_gaussian_identity` now compiles at the full Lemma 3.3 statement,
including the positive residue `2π/(1+it) exp((λ+it)²/(2V))`.
Both original integrals are proved absolutely convergent. The proof subtracts
the actual power-sum main term, continues its bounded remainder's Mellin
transform, applies justified Gaussian Fubini, and restores the explicit term.
DWWZ-10 is DONE after combined BAT/audit and semantic acceptance; both main theorems remain open.

## Start here

- [Goal Prompt](Dong-Wang-Wang-Zhang%20Goal%20Prompt.md): active whole-proof objective and unchanged completion contract.
- [Source Contract](Dong-Wang-Wang-Zhang%20Source%20Contract.md): frozen mathematical outputs and quantifier conventions.
- [Checklist](Dong-Wang-Wang-Zhang%20Checklist.md), [Architecture](Dong-Wang-Wang-Zhang%20Architecture.md), and [Research Agenda](Dong-Wang-Wang-Zhang%20Research%20Agenda.md): the same twenty implementation gates, two DONE and eighteen OPEN.
- [Crosswalk](Dong-Wang-Wang-Zhang%20Crosswalk.md): every numbered theorem, lemma and proposition mapped to an implemented or proposed consumer, explicitly distinguished.
- [Sources](Dong-Wang-Wang-Zhang%20Sources.md): dated literature/repository survey, query results and access limits.
- [Reproduction Manifest](Dong-Wang-Wang-Zhang%20Reproduction%20Manifest.md): commands, dependency decisions and verification scope.
- [Errata](Dong-Wang-Wang-Zhang%20Errata.md): source-version distinctions and issues requiring checking, not invented corrections.
- [Template Inventory](Dong-Wang-Wang-Zhang%20Template%20Inventory.md): how every node-63 file/folder role was adapted or deliberately omitted.

## Human-facing BATs

From this directory, or by launching the BAT from elsewhere:

```powershell
cmd /c run_dong_wang_wang_zhang_build.bat --no-pause
```

It now verifies the **active development package**: exhaustive file inventory, local links, source hashes, parent/extension dependency pins, gate-status consistency, all production imports, prohibited-proof scan, Lake build, semantic regressions, exhaustive transitive axioms and declaration linters. It writes a timestamped log, rejects Lean diagnostics and returns nonzero on failure. Double-click mode pauses. Its success label is `DEVELOPMENT PASS — CURRENT MODULES VERIFIED; MAIN PAPER CONTRACTS INCOMPLETE`, never a claim that T1/T2 are complete.

Maintain this BAT as new modules and exact public-consumer regressions are added; historical scaffold PASS logs are not proof evidence. Maintain and run the root [run_lake_build.bat](../../run_lake_build.bat) as well, sequentially, after relevant implementation or runner changes. The goal prompt makes this mandatory.

The folder-local [push_to_github.bat](push_to_github.bat) is the separate **owner-only repository synchronization** interface. Double-click to enter a commit message, or run `push_to_github.bat "Describe the changes"`; add `-NoPause` for non-pausing operation. It resolves and enters the Git root, requires branch `main`, rejects an empty/whitespace message, stages **all repository changes** with `git add -A`, commits if needed, and runs `git push origin main`. Every Git exit code is checked. It does not automatically rebase, force-push or push tags; a rejected push remains a visible failure for the owner to resolve. The scaffold verifier never invokes it, and agents must not run it without separate explicit authorization.

## Folder boundary

`Sources/` contains the pinned paper PDF/TeX and essential primary references. `Dependencies/` records the selected pinned graph and reuse candidates. `Extension/` contains the small active package, without proof placeholders. `Tools/` contains its development verifier and the separate owner-only synchronization implementation. `logs/` and Lake caches are generated locally and ignored. The node-73 survey found no relevant reuse for the initial obligation; no node-73 dependency was added.

The existing foundation and nodes 63, 73 and 74 are unchanged. No prior completion counts, repair authorizations, counterexamples, or historical logs are copied as evidence for this paper. Recovery-record maintenance is permanently skipped. Both folder-local BAT interfaces are present; this setup neither runs repository synchronization nor commits or pushes.
