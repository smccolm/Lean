# Dhiman–Kadiri–Quesada-Herrera checklist

**PLANNING ONLY. 0/20 proof gates complete. Every gate is OPEN.** Setup success is not proof completion. Module names below are proposals, not existing Lean declarations.

| Gate | Status | Target | Acceptance test | Proposed module |
|---|---|---|---|---|
| DKKH-01 | OPEN | Source edition and errata | Resolve E01–E09 against immutable PDF/TeX/code; document the exact accepted corrected or literal targets and all scope differences. | `SourceReview` |
| DKKH-02 | OPEN | Actual objects and conventions | Define integer/positive-index sums, sharp cutoffs, exp(2πif), principal cpow, χ and literal remainder; prove sign, floor and endpoint adapters. | `Objects` |
| DKKH-03 | OPEN | Harmonic and digamma estimates | Prove Lemma 1 and Appendix Lemma 11 with all δ and N domains, constants and special values; reuse Mathlib/PNT+ digamma APIs. | `HarmonicDigamma` |
| DKKH-04 | OPEN | Finite exponential sums | Prove Lemma 2 for S₀, S₁ and tilde-S₁, including integer and half-integer cases and all denominator conditions. | `FiniteExponentialSums` |
| DKKH-05 | OPEN | Oscillatory tails | Prove Lemma 3 and Appendix A.4 for Z₀/Z₁, convergence and all rational/half-integer refinements actually consumed. | `ExponentialTails` |
| DKKH-06 | OPEN | Stationary phase and weighted integrals | Prove Lemmas 4–5 with exact boundary and error terms for the actual J(a,b,m); derive stationary points and branch phases. | `StationaryPhase` |
| DKKH-07 | OPEN | Explicit χ and gamma constants | Prove Lemmas 6–7, exact C₀–C₃, positive/negative-height treatment and the valid functional equation orientation. | `ChiGamma` |
| DKKH-08 | OPEN | Theorem 8 Part I | Prove the complete weighted truncated Poisson identity/error for the accepted full hypothesis set, general endpoints and all N; no assumed remainder bound. | `WeightedPoissonI` |
| DKKH-09 | OPEN | Theorem 8 Part II | Prove the refined complete T_N estimate and each derivative monotonicity condition; verify the f−Nx substitution throughout H/H₁/B/E terms. | `WeightedPoissonII` |
| DKKH-10 | OPEN | Poisson corollaries | Derive Corollary 0.1 and Corollary 8.1, half-integer endpoint cancellation, δ=1/2 evaluations, and rigorous constant-weight specialization. | `PoissonCorollaries` |
| DKKH-11 | OPEN | Explicit B-process | Prove Corollary 0.2 with actual stationary dual sum, −1/8 phase and full displayed constants/error. | `ExplicitBProcess` |
| DKKH-12 | OPEN | Theorem 9 AFE1 | From actual truncation and weighted Poisson prove the source-intended n≥1 theorem with exact m(c), all σ,c,t,t₀ assumptions and small-cutoff review. | `AFEFirstKind` |
| DKKH-13 | OPEN | Corollary 0.3 and AFE1 constants | Prove real-cutoff transfer, c₀ maximum, threshold 14 and certified stated decimal bounds at 14.13472 and 3·10^12. | `AFEFirstKindConstants` |
| DKKH-14 | OPEN | Theorem 10 direct branch | Assemble the actual two-polynomial AFE for x≥y with A₀,B₀,C₀, the correct E₀ branch, x₀=max(h,sqrt(t₀/2π)), endpoints and all explicit losses. | `AFESecondKindDirect` |
| DKKH-15 | OPEN | Theorem 10 reflected branch | Derive x<y from the actual functional equation/dual remainder, including σ=1 and dual σ=0, both signs of t and exact branch bounds. | `AFESecondKindReflection` |
| DKKH-16 | OPEN | Corollary 0.4 / Table 1 | Prove global σ maxima and outward-certified numerical bounds with exact t₀=2π; independently separate displayed approximations from upper bounds. | `AFESecondKindConstants` |
| DKKH-17 | OPEN | Corollary 0.5 / Tables 2–3 | Prove k=1..50 bounds, k/π+1.1601 for 11..50, constant-6 consequence and all accepted table cells; attribute Table 4 comparisons. | `BoundedRangeConstants` |
| DKKH-18 | OPEN | Reuse and package integration | Install only justified compatible import closures; pin and license dependencies, preserve upstream proofs, include every production module in root graph. | `DependencyIntegration` |
| DKKH-19 | OPEN | Semantic regressions and audit | Audit every public/critical theorem transitively; exact-type tests cover constants, signs, branches, endpoint weights and actual-source consumers. | `SemanticRegressionAndAudit` |
| DKKH-20 | OPEN | Final sequential verification | Both foundation and paper BATs pass zero-diagnostic checks; all preceding gates accepted; synchronize contract/checklist/DAG/reproduction and distinguish external review. | `ReleaseAcceptance` |

A DONE gate requires an actual public theorem with the intended unfolded type, genuine upstream consumption, compatible imports, passing dependency audit and source correspondence. A theorem assumed as a parameter, numerical optimizer result or signature-only definition cannot close a gate. E01–E09 are review identifiers in Errata; their resolution may require several separately documented corrections. Preserve all original displays.
