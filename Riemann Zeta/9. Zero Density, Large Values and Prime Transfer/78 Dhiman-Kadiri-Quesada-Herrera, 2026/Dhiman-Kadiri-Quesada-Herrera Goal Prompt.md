# Dhiman–Kadiri–Quesada-Herrera 2026 — whole-paper goal prompt

## Owner-approved corrected contracts — 5 October 2026

The owner has explicitly adopted all five proposals in the attached instruction accompanying “Proceed”: the Part-II E₁ envelope A−(B−C)/y; the four positive-frequency quotient monotonicity conditions for h=g′ and h=g(f′−N); the full-positive-gap Corollary 0.1 repair with halfSecondEndpointDelta and the complete finite-head coefficient; the proof-consistent Theorem-10 branch assignments; and every certified Table 1–2 proposal in Computation Review at commit a9ddec65b578914f19199443a3e8ffa3a406e8e8. The present values are identical to that commit. The literal Corollary 0.2 remains unchanged. These are owner-approved local corrected contracts, not author-issued corrections.

All original displays, counterexamples and proof diagnostics remain preserved. Historical sections saying “pending” describe their original checkpoint and are superseded by this decision. All explicit public consumers, the final semantic comparison and sequential release verification have passed: 20/20 gates are accepted. No scope decision listed here remains blocked on owner approval.

The owner also authorizes mathematically justified repairs of this class without repeated approval. First attempt an independent proof of the original conclusion under the original hypotheses. When a repair is necessary, preserve the original, identify the precise failure, prove the replacement, expose every changed hypothesis/constant, verify its applications, and distinguish failed proof steps from false theorems. Escalation is reserved for abandoning a required result, changing the central objective, or unresolved competing contracts that materially change the program. Proof integrity, source preservation and acceptance checks remain mandatory.

**GOAL COMPLETE — 6 October 2026. 20/20 proof gates complete.** All DKQH-01–DKQH-20 acceptance tests pass for the adopted corrected contracts. The frozen source and its diagnostics remain preserved; this is internal kernel/project completion, not proof of every unchanged statement in v1 or independent review.

## Completed objective and retained instructions

Formalize the mathematical content of *Explicit Exponential Sum Estimates and Approximate Functional Equations for the Zeta Function*, Dhiman–Kadiri–Quesada-Herrera, arXiv:2609.00537v1, in an isolated extension of this existing repository. Close Theorem 8 Parts I and II, Theorems 9 and 10, introductory Corollaries 0.1–0.5, Corollary 8.1, and the supporting analytic and numerical obligations required for their exact conclusions. Resolve and document the frozen source discrepancies before adopting any corrected public contract. Meet every DKQH-01–DKQH-20 acceptance test. Source references alone and unverified numerical computations are not proofs.

Use full author names in human-facing filenames, `DhimanKadiriQuesadaHerrera2026` as the Lean namespace, and `DKQH` as the task prefix. Preserve all completed work in nodes 63, 71, 73, 74 and 77, the foundation freeze, source ledgers, counterexamples, repairs, audits and owner scripts.

## Read first and freeze the actual scope

Read `../../AGENTS.md`, the root README/publication audit/manuscript and node-71 status/checklist/architecture/audit; then this folder's README, Source Contract, Errata, Checklist, Architecture, Crosswalk, Research Agenda, Sources, Computation Review, Reproduction Manifest and `Dependencies/README.md`. Verify `Sources/SHA256SUMS.txt`. Read the actual PDF and TeX, `AFE2026ago31.bbl`, `anc/AFE1.sage` and `anc/AFE2.py`. Recheck arXiv and author pages for a revision newer than v1; retain the frozen v1 bytes and compare rather than silently replacing them.

Start by resolving DKQH-01's source discrepancies. Separate a literal published statement, a typographical correction supported by the proof, a substantive strengthening, and a missing formal bridge. Preserve counterexamples and evidence. A false literal statement cannot be a Lean target. Record any required change to mathematical scope before implementation; do not label a corrected or weaker result as the unchanged original. Routine notation repair with an established mathematical justification need not interrupt otherwise authorized work; a change to the central objective requires an explicit scope decision; the owner’s standing authorization below covers justified source repairs.

## Accepted source repair — 5 October 2026

For Theorem 8 Part I, the owner explicitly accepted the additional hypotheses that `|g′|` and `|g′|/(1+f′−N)` are nonincreasing, as documented in Errata. Preserve the original statement and its counterexample. Prove the corrected theorem and verify the added hypotheses for every AFE application; do not label the corrected general theorem as the unchanged printed result. The five subsequent source repairs and standing authorization are adopted above; their semantic and verification requirements remain mandatory.

## Mandatory mathematical outcomes

1. Theorem 8: the actual sum of `g(n) * exp(2π i f(n))` on `a < n ≤ b`, the actual sum of Fourier integrals for `N ≤ ν ≤ floor(f'(a))`, and both complete explicit `T_N` estimates, including boundary terms, `G`, `H`, `H_1`, `B`, `E_1`, `E_2`, digamma and δ. General endpoints and half-integer simplifications are separate obligations. Prove every monotonicity/regularity/integrability hypothesis used by a consumer. Do not substitute an unspecified big-O constant, unweighted bound or merely an exponent-pair transformation.
2. Corollaries 0.1, 0.2 and 8.1: discharge constant-weight boundary cases, preserve stationary phase `-1/8`, the actual stationary points and `2.686`, `1.251`, logarithmic coefficients, and δ-dependent terms. Justify all positive scale assumptions omitted or implicit in prose.
3. Theorem 9 and Corollary 0.3: prove the sharp sum including the `n=1` term under the documented source repair, exact `m(c)` and `c_0` formulas, half-integer-to-real-cutoff transfer, `0 < σ ≤ 1`, and constants `1.2552` for `t₀=14.13472` and `1.2127` for `t₀=3·10^12`. The latter threshold is a numerical parameter, not an RH assumption.
4. Theorem 10: for `1/2 ≤ σ ≤ 1`, `|t| ≥ t₀ ≥ 2π`, `x,y ∈ ℤ+1/2`, `x,y ≥ h ≥ 3/2`, and `2πxy=|t|`, prove the actual two-polynomial AFE with the correct χ factor and both explicit error branches. Preserve the logarithmic loss. Track both signs of t by a proved conjugation/branch bridge, use positive `|t|` in real powers, and resolve equation (5.2) against the derivation. Do not claim an all-real-cutoff AFE2: that extension is left open by the paper.
5. Corollaries 0.4–0.5: derive uniform maxima over the exact σ interval, rigorous outward bounds for the accepted Table 1–3 constants, the `1 ≤ k ≤ 50` finite range, the `11 ≤ k ≤ 50` bound `k/π+1.1601`, and the displayed constant-6 consequence for `min(x,y) ≤ 10^6`. Account for rounded numbers that do not certify an upper bound. Table 4 is an attributed comparison with Simonič, not an additional obligation to formalize his whole paper. Any changed decimal bound must remain visibly a corrected bound, with a preserved original and explanation.

## Reuse this repository before developing new foundations

Consult the dated exact-type inventory `Tools/local_reuse_inventory.json`. Existing node-71 Euler–Maclaurin/zeta truncation, smooth Poisson and finite derivative tests; node-63 continuous derivative, B-process and digamma machinery; node-74 sharp truncation/gamma work; node-73 stationary Fourier bounds; and node-77 digamma, complex-power and finite logarithmic-sum work are real starting points. Inspect proof bodies and transitive import/axiom closures. Record which theorem shortens which DKQH obligation and prove the normalization adapter. A matching name does not prove matching strength: the existing `vanDerCorput_B_process` is a discrete second-difference bound, and smooth zeta-square AFEs are not this sharp unsmoothed ζ AFE.

Keep the root's pinned Lean 4.30/Mathlib/PNT+ graph unless a justified, separately scoped migration is needed. Current upstream HEADs use newer toolchains and are research observations, not selected dependencies. Prefer a path dependency on the root and the smallest audited closure. Do not duplicate an entire completed extension simply to acquire one gamma lemma. If adapting code, retain provenance, license, exact source hashes, modifications and complete import closure; scan and audit that closure. The completed density results are available context but do not automatically imply this paper's explicit numerical estimates.

## Execution and numerical integrity

Follow the actual dependency DAG: harmonic/digamma and finite/tail exponential sums → weighted Poisson I/II; stationary phase → B-process; Poisson I plus exact truncation → AFE1 → real cutoff; Poisson II plus weighted stationary integrals and χ estimates → AFE2 direct/reflected branches → certified constants. Carry the actual phase, weight, finite sum and remainder through each public consumer. Make endpoint, floor, sign, positivity, branch, convergence and uniformity bridges explicit.

Author-code replay is a distinct non-proof activity. `AFE1.sage` mixes interval checks with floating-point display; `AFE2.py` uses local optimization, finite differences, approximate `2π` and double precision. Never convert their output into an axiom, assumed inequality or certificate accepted outside Lean's kernel. Use analytic monotonicity or verified interval/rational certificates with a kernel-checked checker. Prove global coverage, extrema, endpoint values and outward rounding. Cover parameter intervals, not a sample grid. Preserve raw author scripts and place adaptations separately.

No `sorry`, `admit`, project axioms, conclusion-equivalent hypothesis, constant/toy model, `native_decide`, unsafe evaluation, suppressed warning, missing production import or hidden premise. Standard logical axioms remain visible in actual transitive audits. A helper lemma, a proposition definition, a green build or a replayed table is not a completed source theorem. Keep the public statements and intended constants fixed except for explicit mathematically justified repairs.

## Build, audit and synchronization interfaces

Maintain `run_dhiman_kadiri_quesada_herrera_build.bat` and its Tools implementation. Its active-development mode must check complete module classification, root-import coverage, package builds, public exact-type regressions, explicit and exhaustive transitive axiom audit, integrity scans and zero-warning gates. A failed or warning-producing stage must fail the BAT. Preserve arbitrary-caller-directory operation, timestamped logs, reliable exit codes, double-click pause and `--no-pause`. Run every intended module and retained test; do not narrow coverage to get a PASS.

Maintain and run `../../run_lake_build.bat --no-pause` for the existing foundation after relevant Lean/import/package/audit/runner changes. Run foundation and paper verifiers sequentially. Focused builds supplement these interfaces. Record checkout/toolchain/dependency/source hashes, exact commands, exits, diagnostics, log paths and log hashes. Keep README, Checklist, Architecture, Research Agenda, Crosswalk, contract and reproduction evidence synchronized.

Keep the node-63-derived `push_to_github.bat` as the owner's separate synchronization interface, with required supplied commit message, Git-root resolution, repository-wide staging, checked Git failures and pull/rebase-before-push behavior. Do not hard-code a commit message, force-push, run this BAT from verification, stage, commit or push without separate explicit authorization. Report a proposed message at handoff.

Recovery-record maintenance is optional and skipped. Do not create, modify or wait on a recovery record; continue already-authorized mathematical work if such an optional action is unavailable.

## Acceptance after activation

Persist until the exact agreed public contracts and all twenty gates are closed, or a specific essential obstruction remains after substantive safe alternatives. Do not replace the activated task with a plan or a progress-only handoff. Before marking DONE, unfold the public types, show actual upstream consumption, verify source/semantic correspondence separately from axiom integrity, check every constant/range and run both BATs. Preserve any unresolved source defect as open. Internal kernel/project completion is separate from independent review, publication or community acceptance.
