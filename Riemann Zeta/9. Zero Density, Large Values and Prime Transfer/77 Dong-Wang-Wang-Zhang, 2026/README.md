# Dong–Wang–Wang–Zhang 2026: project template

Research snapshot: **4 October 2026**. Status: **PLANNING ONLY — formalization not started; 0/20 proof gates complete.** No Lean package, theorem, proof build, or active conversion goal is created by this scaffold.

Paper: Zikang Dong, Ruihua Wang, Weijia Wang and Hao Zhang, *Large zeta sums and zeros of the Riemann zeta function*, [arXiv:2608.31060v1](https://arxiv.org/abs/2608.31060v1), submitted 31 August 2026, 19 pages. The arXiv history and first author's publication page still list this preprint at the research date; no later version or journal publication was identified.

The main target is a pointwise inverse theorem: a large value of the actual sum `S(x,t) = Σ_{1≤n≤x} n^(it)` forces many nontrivial zeta zeros, with analytic multiplicity, in a specified open disk near height `t`. A second theorem deduces cancellation from a local zero-window hypothesis. These are not the exponent-pair/density-table targets of node 63.

## Start here

- [Goal Prompt](Dong-Wang-Wang-Zhang%20Goal%20Prompt.md): ready for a later explicit instruction to begin; inactive now.
- [Source Contract](Dong-Wang-Wang-Zhang%20Source%20Contract.md): frozen mathematical outputs and quantifier conventions.
- [Checklist](Dong-Wang-Wang-Zhang%20Checklist.md), [Architecture](Dong-Wang-Wang-Zhang%20Architecture.md), and [Research Agenda](Dong-Wang-Wang-Zhang%20Research%20Agenda.md): the same twenty open implementation gates.
- [Crosswalk](Dong-Wang-Wang-Zhang%20Crosswalk.md): every numbered theorem, lemma and proposition mapped to a future consumer.
- [Sources](Dong-Wang-Wang-Zhang%20Sources.md): dated literature/repository survey, query results and access limits.
- [Reproduction Manifest](Dong-Wang-Wang-Zhang%20Reproduction%20Manifest.md): commands, dependency decisions and verification scope.
- [Errata](Dong-Wang-Wang-Zhang%20Errata.md): source-version distinctions and issues requiring checking, not invented corrections.
- [Template Inventory](Dong-Wang-Wang-Zhang%20Template%20Inventory.md): how every node-63 file/folder role was adapted or deliberately omitted.

## Human-facing BATs

From this directory, or by launching the BAT from elsewhere:

```powershell
cmd /c run_dong_wang_wang_zhang_build.bat --no-pause
```

At this stage it performs **offline scaffold verification only**: required files, local links, archived-source SHA-256 hashes, source labels, parent pins, all-open gate consistency, and absence of accidental Lean/package files. It prints `SCAFFOLD PASS` with `LEAN PROOF BUILD: NOT STARTED`, writes a timestamped log, and returns nonzero on failure. Double-click mode pauses. It does not invoke Lake, download dependencies, or activate the goal.

When formalization is separately authorized, upgrade this same BAT's implementation into the complete paper build/audit/regression gate; do not preserve a planning PASS as proof evidence. Maintain and run the root [run_lake_build.bat](../../run_lake_build.bat) as well, sequentially, after relevant implementation or runner changes. The goal prompt makes this mandatory.

The folder-local [push_to_github.bat](push_to_github.bat) is the separate **owner-only repository synchronization** interface. Double-click to enter a commit message, or run `push_to_github.bat "Describe the changes"`; add `-NoPause` for non-pausing operation. It resolves and enters the Git root, requires branch `main`, rejects an empty/whitespace message, stages **all repository changes** with `git add -A`, commits if needed, and runs `git push origin main`. Every Git exit code is checked. It does not automatically rebase, force-push or push tags; a rejected push remains a visible failure for the owner to resolve. The scaffold verifier never invokes it, and agents must not run it without separate explicit authorization.

## Folder boundary

`Sources/` contains the pinned paper PDF/TeX and essential primary references. `Dependencies/` records reuse candidates without installing or duplicating them. `Extension/` reserves the future package without adding Lean placeholders. `Tools/` contains the scaffold verifier and the separate owner-only synchronization implementation. `logs/` is generated locally and ignored.

The existing foundation and nodes 63, 73 and 74 are unchanged. No prior completion counts, repair authorizations, counterexamples, or historical logs are copied as evidence for this paper. Recovery-record maintenance is permanently skipped. Both folder-local BAT interfaces are present; this setup neither runs repository synchronization nor commits or pushes.
