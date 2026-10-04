# Dong–Wang–Wang–Zhang 2026 — future whole-proof goal prompt

**INACTIVE TEMPLATE. Created 4 October 2026.** The owner has authorized research and project setup, explicitly **not** starting Lean conversion. Reading this file, running the scaffold BAT, or discovering it in the workspace is not an instruction to activate a goal. Begin the following work only after a subsequent explicit owner instruction to implement this paper.

## Objective upon explicit activation

Implement *Large zeta sums and zeros of the Riemann zeta function*, Dong–Wang–Wang–Zhang, arXiv:2608.31060v1, in this existing Lean repository. Prove both main theorems at their exact [frozen source contracts](Dong-Wang-Wang-Zhang%20Source%20Contract.md), discharge the analytic dependencies, and satisfy all twenty [checklist gates](Dong-Wang-Wang-Zhang%20Checklist.md). Preserve the existing Guth–Maynard foundation and all completed extensions, audits, counterexamples and source freezes.

Use the full paper name for human-facing files. The prospective Lean namespace is `DongWangWangZhang2026`; the task prefix is `DWWZ`. Do not carry over node-63 theorem names or completion claims.

## Read before implementation

Read `../../AGENTS.md`, the current foundation status/audit/architecture and the paper's README, Source Contract, Checklist, Architecture, Crosswalk, Research Agenda, Sources, Errata, Reproduction Manifest, and `Dependencies/README.md`. Read the pinned TeX and the precise cited statements, not just abstracts. Verify `Sources/SHA256SUMS.txt`. Recheck for a newer primary-paper revision when the goal is actually activated; retain v1 and explicitly compare any new version before changing scope.

## Non-negotiable public results

1. T1: absolute `c,T₀`, actual `S(x,t)`, every stated `T,x,N` range, **one** center `φ` before **every** admissible `L`, open radius `L log T/(log x)²`, displacement `cN`, lower cutoff `cN⁶`, and multiplicity-weighted lower count `L/360`. Both signs of `t` are required.
2. T2: absolute window-displacement `C`; fixed `A>0`, `0<δ≤1/4`; threshold depending only on `(A,δ)`; strict `ε>(log T)^(-1/3)`; every prescribed nearby window has count at most `δε² log T/400`; conclude the actual-sum bound on **all** `T^ε≤x≤T^A`, with implied constant depending only on `A`.

Do not weaken endpoints, move quantifiers, replace multiplicity by cardinality, add RH, remove the local-zero premise from T2, or turn a main conclusion into a hypothesis. Supplementary remarks are separately labelled; they neither substitute for nor silently expand the two-main-theorem contract.

## Mathematical execution

Prefer the paper's Granville–Soundararajan proof path. Search existing local code, installed Mathlib, node 63, node 74/PNT+, and the dated external survey before creating new support modules. Inspect actual theorem types and assumptions; matching names or comments are not enough. Choose a single compatible dependency graph, not moving upstream branches or mixed Mathlib versions. Do not vendor a completed project's full tree unless its needed audited import closure genuinely requires that scope.

Prioritize the smallest faithful mean-value/twist/Lipschitz theorem that closes Lemma 2.2 for `n^(it)` and feeds Proposition 4.1. The Hilbert-space Halász–Montgomery inequality is not the pretentious mean-value theorem. A proved specialization may avoid unnecessary generality, but document exactly what source result it replaces and keep its original statement intact. Alternate proofs must establish the exact public end contract.

Maintain a short actual-obligation DAG: analytic mean value and maximizing twist → uniform Lipschitz/comparison → Gaussian lower bound; in parallel xi product/convergence → zero repulsion/log derivative, and Gaussian Fourier/contour identity **with residue**; then actual weighted forcing → near/far zero count → T1 → local-window contradiction plus large-x estimate → T2. Work on terminal analytic blockers, not endless families of conditional wrappers. If one route stalls, test a materially different faithful route. Keep all scales linked to `x,t,T`; carry the actual sum and zero divisor through every consumer.

Keep numerical constants and uniformity explicit. Prove integrability, summability, maximum attainment or a quantitatively equivalent witness, nonvanishing, pole separation, conjugation of zero multiplicity, and boundary conversions. Never silently invoke a totalized integral, infinite sum, complex division, or analytic order outside its mathematical validity conditions.

## Integrity, source errors and progress

No `sorry`, `admit`, project axiom, unsafe/external proof oracle, `native_decide`, disguised conclusion hypothesis, toy object, missing production import, or suppressed Lean diagnostic. Computational experiments and literature citations are discovery evidence, never kernel proofs. Standard logical axioms remain visible in genuine transitive audits.

Preserve the frozen source and every end statement. If a defect is found, distinguish a source error, an attribution/version issue, and a missing formal bridge. Record a precise demonstration and any counterexample permanently in Errata and regressions. A supporting repair must be labelled as such, with its authorization and effect on downstream consumers; never call it a proof of a false original. Do not silently substitute a weaker end theorem.

Recovery-record maintenance is permanently optional and skipped: do not create, edit, replace or wait on recovery-record files. A denied optional write is not a mathematical blocker. Continue all already-authorized writable mathematical work and verification. Do not ask the owner about recovery-record approval.

## BAT maintenance is part of the goal

Maintain **`run_dong_wang_wang_zhang_build.bat`** and its PowerShell implementation throughout conversion. Its current scaffold-only result is not a proof PASS. Before any claim of formalization, upgrade it to verify pins, enumerate all production/test files, check root import coverage, build the package and every retained regression, reject every Lean warning/error, run explicit public and exhaustive transitive axiom audits, scan for prohibited shortcuts, test exact public contracts, and write timestamped log/evidence with reliable failure exit codes. Preserve arbitrary-caller-directory operation, visible diagnostics, double-click pause and `--no-pause`.

Also maintain and execute **`../../run_lake_build.bat --no-pause`** for the frozen foundation after relevant Lean/import/package/audit/runner changes. Run the foundation and paper BATs **sequentially**. Focused Lake builds supplement, never replace, these interfaces. Do not narrow their coverage or relabel an unperformed proof build as passed. If the paper runner changes mode, synchronize README, Tools, Checklist and Reproduction Manifest in the same change.

Keep the folder-local **`push_to_github.bat`** and `Tools/push_to_github.ps1` present and usable as the owner's separate synchronization interface. Preserve root resolution, main-branch protection, a required owner-supplied commit message with no hard-coded default, repository-wide staging and checked Git exit codes. Never invoke synchronization from a build/audit runner, run it without separate explicit authorization, or force-push. Update the exhaustive scaffold inventory when tooling changes; missing owner interfaces must fail setup verification.

## Completion and handoff

Continue after activation until both public source contracts and every acceptance gate are genuinely closed, or a specific essential blocker remains after safe alternatives. A helper lemma, a green unrelated build, source collection, or a precise plan is not completion of the activated proof task. Keep progress claims local and evidence-backed.

Before claiming DONE: unfold both public theorem types and principal objects; demonstrate real upstream consumption and all constants/ranges; run semantic regressions, full source/coverage checks, audits and both BATs; record exact toolchain/revisions, commands, exit codes, diagnostic counts, log paths and hashes; synchronize the twenty gate statuses across all documents. Distinguish internal kernel/project completion from independent semantic review or publication. Do not stage, commit, run synchronization BATs, or push unless separately instructed; propose a commit message for the owner.
