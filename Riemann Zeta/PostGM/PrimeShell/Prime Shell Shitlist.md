# Prime Shell Shitlist

This checklist is exhaustive for the isolated program. Checking an infrastructure item does not authorize checking a downstream theorem item. The frozen GM proof is an input and must remain unchanged.

## Phase I - Kernel feasibility

- [x] **PSH-00 - Isolation boundary.** Create the `PostGM/PrimeShell/` program, identify the frozen GM commit, prohibit edits to frozen GM modules, and record the toolchain split.
- [ ] **PSH-01 - Pinned Zeta23 reproduction.** Check out tag `v1.0` / commit `3635e748...`; build unchanged with its pinned toolchain; run its Comparator and axiom checks; record exact commands, warnings, failures, and artifact hashes.
- [ ] **PSH-02 - Exact source crosswalk.** Map paper equations (2.7), (5.10), (5.11), Proposition 5.4, Theorem 5.7, and Section 7.2 to exact Lean declarations. Record all normalizations and interval/Fourier conventions.
- [ ] **PSH-03 - Exact prime-prime decomposition.** Expose `M[P_X,P_X]` as an exact equality with diagonal and each off-diagonal contribution independently accessible. Recover the existing `X <= T` theorem from this decomposition.
- [ ] **PSH-04 - Exact shift kernel.** Prove the dyadic `m=n+h` rewrite, literal `K_{N,T}(h)`, support, regularity, variation, tail, endpoint, and remainder bounds.
- [ ] **PSH-05 - Honest GM arithmetic interface.** State the exact uniform cumulative correlation estimate suggested by GM Corollary 1.4, with `pi`-to-`psi`, prime powers, exceptional weighted set, endpoints, lengths, and errors exposed. Do not assume or formalize it yet.
- [ ] **PSH-06 - F1 kernel verdict.** Prove either:
  - a summation-by-parts transfer from the PSH-05 prefix estimate to the exact PSH-04 kernel within the required trace error; or
  - a rigorous no-go/counterexample identifying the stronger arithmetic information required.

Phase I is complete only when PSH-01 through PSH-06 are all discharged and F1 has a theorem-level PASS or FAIL verdict.

## Phase II - Structural and value feasibility

- [ ] **PSH-07 - F2 disconnected-shell theorem.** Prove that the actual Zeta23 test family admits the low block plus high shell, or prove that its positivity/Fourier constraints forbid it. Evaluate every low-shell cross term.
- [ ] **PSH-08 - Arithmetic-only oracle consumer.** Introduce only a narrow explicit theorem parameter about finite von Mangoldt sums; prove the full conditional trace and zero-side consumer rather than projecting the parameter.
- [ ] **PSH-09 - F3 certified pricing.** Optimize the actual finite spectral problem, produce an exact-rational or interval-certified result, and decide CONTINUE/STOP. Separate internally checked results from external enclosure hypotheses.
- [ ] **PSH-C - Optional PairCeiling reproduction.** Obtain and independently verify the `EnclOK` interval certificate before treating `0.6818287` as an unconditional numerical comparator. This is optional and is not allowed to block a structural Prime Shell theorem.

## Phase III - Analytic proof

- [ ] **PSH-10 - Complete informal theorem.** Write a source-facing proof with no hidden uniformity, endpoint, smoothing, exceptional-set, or epsilon losses.
- [ ] **PSH-11 - Source choice.** Select GM only if its cumulative information passed F1 and F3. Otherwise test MRT at `alpha > 33/25`. Record and kill routes that fail.
- [ ] **PSH-12 - Toolchain architecture.** Choose a standalone Zeta23 extension or explicit cross-project statement bridge. Do not port the frozen GM repository wholesale and do not change its public proofs.

## Phase IV - Formal theorem

- [ ] **PSH-13 - Native arithmetic input.** Formalize the exact selected source theorem and every unavailable dependency, with no `sorry`, `admit`, project axiom, theorem-equivalent hypothesis, unsafe bypass, or toy object.
- [ ] **PSH-14 - Native weighted trace.** Replace the arithmetic oracle and prove the complete prime-side trace theorem with all main terms and errors.
- [ ] **PSH-15 - Native spectral consumer.** Consume the real trace through the finite compression, rank/inertia, zero counting, multiplicity, and window chain.
- [ ] **PSH-16 - Public Prime Shell theorem.** State and prove a new unconditional zero-distribution theorem that transitively uses arithmetic information strictly beyond support one and is outside a precisely defined support-one certificate class.

## Phase V - Verification and publication

- [ ] **PSH-17 - Dependency audit.** Explicit `#print axioms` or environment-level audits for every public and critical theorem; only permitted Lean/Mathlib logical axioms may remain.
- [ ] **PSH-18 - Clean build.** Zero Lean errors, zero warnings, zero linter diagnostics, and repository-wide integrity scans in the isolated project.
- [ ] **PSH-19 - Trusted statement check.** Comparator or equivalent independent statement equality for the public result.
- [ ] **PSH-20 - Reproduction release.** Fresh-clone build, immutable SHA/tag, manifests, commands, source crosswalk, and honest documentation.
- [ ] **PSH-21 - External review.** Independent expert scrutiny of the arithmetic transfer, kernel analysis, and zero-side consumer. Kernel acceptance is not represented as peer review.

## Completion contract

The program is not complete merely because a decomposition, conditional theorem, optimizer run, or focused build passes. Completion requires PSH-13 through PSH-20 and an exact public theorem at PSH-16. Phase I may be closed separately with a rigorous negative verdict; that closure must say the Prime Shell theorem remains unproved.
