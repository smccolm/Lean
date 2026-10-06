# Dhiman–Kadiri–Quesada-Herrera checklist

The corrected formalization is complete: 20/20 gates, 127 production modules and 299 exact-type semantic consumers. Both sequential verifiers passed with zero Lean diagnostics. Historical checkpoint sections retain their original counts and pending-decision wording; the final accepted contracts and release receipt supersede them.

**GOAL COMPLETE — 6 October 2026. 20/20 proof gates complete.** All DKQH-01–DKQH-20 acceptance tests pass for the adopted corrected contracts. The frozen source and its diagnostics remain preserved; this is internal kernel/project completion, not proof of every unchanged statement in v1 or independent review.

| Gate | Status | Target | Acceptance test | Proposed module |
|---|---|---|---|---|
| DKQH-01 | DONE | Source edition and errata | Resolve E01–E09 against immutable PDF/TeX/code; document the exact accepted corrected or literal targets and all scope differences. | `SourceReview` |
| DKQH-02 | DONE | Actual objects and conventions | Define integer/positive-index sums, sharp cutoffs, exp(2πif), principal cpow, χ and literal remainder; prove sign, floor and endpoint adapters. | `Objects` |
| DKQH-03 | DONE | Harmonic and digamma estimates | Prove Lemma 1 and Appendix Lemma 11 with all δ and N domains, constants and special values; reuse Mathlib/PNT+ digamma APIs. | `HarmonicDigamma` |
| DKQH-04 | DONE | Finite exponential sums | Prove Lemma 2 for S₀, S₁ and tilde-S₁, including integer and half-integer cases and all denominator conditions. | `FiniteExponentialSums` |
| DKQH-05 | DONE | Oscillatory tails | Prove Lemma 3 and Appendix A.4 for Z₀/Z₁, convergence and all rational/half-integer refinements actually consumed. | `ExponentialTails` |
| DKQH-06 | DONE | Stationary phase and weighted integrals | Prove Lemmas 4–5 with exact boundary and error terms for the actual J(a,b,m); derive stationary points and branch phases. | `StationaryPhase` |
| DKQH-07 | DONE | Explicit χ and gamma constants | Prove Lemmas 6–7, exact C₀–C₃, positive/negative-height treatment and the valid functional equation orientation. | `ChiGamma` |
| DKQH-08 | DONE | Theorem 8 Part I | Prove the complete weighted truncated Poisson identity/error for the accepted full hypothesis set, general endpoints and all N; no assumed remainder bound. | `WeightedPoissonI` |
| DKQH-09 | DONE | Theorem 8 Part II | Prove the refined complete T_N estimate and each derivative monotonicity condition; verify the f−Nx substitution throughout H/H₁/B/E terms. | `WeightedPoissonII` |
| DKQH-10 | DONE | Poisson corollaries | Derive Corollary 0.1 and Corollary 8.1, half-integer endpoint cancellation, δ=1/2 evaluations, and rigorous constant-weight specialization. | `PoissonCorollaries` |
| DKQH-11 | DONE | Explicit B-process | Prove Corollary 0.2 with actual stationary dual sum, −1/8 phase and full displayed constants/error. | `ExplicitBProcess` |
| DKQH-12 | DONE | Theorem 9 AFE1 | From actual truncation and weighted Poisson prove the source-intended n≥1 theorem with exact m(c), all σ,c,t,t₀ assumptions and small-cutoff review. | `AFEFirstKind` |
| DKQH-13 | DONE | Corollary 0.3 and AFE1 constants | Prove real-cutoff transfer, c₀ maximum, threshold 14 and certified stated decimal bounds at 14.13472 and 3·10^12. | `AFEFirstKindConstants` |
| DKQH-14 | DONE | Theorem 10 direct branch | Assemble the actual two-polynomial AFE for x≥y with A₀,B₀,C₀, the correct E₀ branch, x₀=max(h,sqrt(t₀/2π)), endpoints and all explicit losses. | `AFESecondKindDirect` |
| DKQH-15 | DONE | Theorem 10 reflected branch | Derive x<y from the actual functional equation/dual remainder, including σ=1 and dual σ=0, both signs of t and exact branch bounds. | `AFESecondKindReflection` |
| DKQH-16 | DONE | Corollary 0.4 / Table 1 | Prove global σ maxima and outward-certified numerical bounds with exact t₀=2π; independently separate displayed approximations from upper bounds. | `AFESecondKindConstants` |
| DKQH-17 | DONE | Corollary 0.5 / Tables 2–3 | Prove k=1..50 bounds, k/π+1.1601 for 11..50, constant-6 consequence and all accepted table cells; attribute Table 4 comparisons. | `BoundedRangeConstants` |
| DKQH-18 | DONE | Reuse and package integration | Install only justified compatible import closures; pin and license dependencies, preserve upstream proofs, include every production module in root graph. | `DependencyIntegration` |
| DKQH-19 | DONE | Semantic regressions and audit | Audit every public/critical theorem transitively; exact-type tests cover constants, signs, branches, endpoint weights and actual-source consumers. | `SemanticRegressionAndAudit` |
| DKQH-20 | DONE | Final sequential verification | Both foundation and paper BATs pass zero-diagnostic checks; all preceding gates accepted; synchronize contract/checklist/DAG/reproduction and distinguish external review. | `ReleaseAcceptance` |

A DONE gate requires an actual public theorem with the intended unfolded type, genuine upstream consumption, compatible imports, passing dependency audit and source correspondence. A theorem assumed as a parameter, numerical optimizer result or signature-only definition cannot close a gate. E01–E09 are review identifiers in Errata; their resolution may require several separately documented corrections. Preserve all original displays.

## Final acceptance evidence

All twenty gates are accepted after the final exact-source comparison, 299 semantic consumers, 2379 exhaustive theorem dependencies, 1465 explicit consumers, all 16 linters, source/inventory fixtures and sequential zero-diagnostic foundation/paper BATs. The per-gate public consumers and evidence are recorded in Tools/proof_gates.json; the complete regularity-field derivation and E01–E09 matrix are in Source Contract. The Reproduction Manifest records current-checkout commands and immutable log hashes. No required in-scope result remains open. Independent review remains external.

## Historical evidence without gate closure

SourceReview proves E01/E02 diagnostics. PoissonCounterexample proves the original Part-I bound false under its printed hypotheses. The owner accepted two added monotonicity conditions, and PowerWeights proves them for actual AFE weights. DKQH-01 remains OPEN until E01–E09 have complete accepted resolutions; The corrected Part-I estimate subsequently completed DKQH-08; Part II remains open.

`HarmonicDigamma` now derives the real digamma series and logarithmic bounds from pinned PNT+, proves convergence and all six nonalternating Lemma-1 estimates with the printed constants, and includes source-index reindexing bridges. Negative-shift bounds also cover N=0. AlternatingHarmonic completes both Appendix-Lemma-11 bounds with the printed constants. DKQH-03 is DONE after exact-type and dependency checks; the later Part-I and AFE1 sections record subsequent progress; Part II and AFE2 remain open.

## DKQH-03 completion evidence

Accepted after the sequential foundation/paper verifiers passed on 5 October 2026. The six SemanticRegression.lemma_one_* consumers and both lemma_eleven_* consumers have the literal source sums, parameter domains and coefficients. The real Gamma logarithmic-derivative bridge, special values, recurrence and duplication are explicitly audited. The corrected alternating identity and false printed version are preserved without changing either Lemma-11 bound. See the H1/H11 Source Contract for correspondence and the Reproduction Manifest for receipts. No conclusion is supplied as a hypothesis. Only this gate is closed.

## Corrected Part I at N = 0

AbelSawtooth proves the actual logarithmic Abel kernel, its paired Fourier expansion, uniform domination and the integral limit. PoissonFourier discharges absolute convergence of both integrated series from the accepted hypotheses and derives their explicit digamma/logarithmic bounds. EulerMaclaurin reuses pinned PNT+ and proves the integer translation needed for every real a≤b, with the literal (a,b] sum. PoissonPartI assembles the finite frequency integrations by parts and proves corrected_poisson_partI_zero, corrected_poisson_partI_zero_noninteger and corrected_poisson_partI_zero_half_integer. These preserve the actual weighted sum, Fourier main term, all N=0 logarithmic/digamma corrections, complex endpoint term and half-integer log(2) refinement. No Fourier identity, convergence result or remainder estimate is a supplied hypothesis. PartIRegularity contains only explicit differentiability, sign and monotonicity conditions, including the owner-approved repair.

The general-endpoint majorant uses the exact harmonic value at integer endpoints and the printed tilde-S₁ elsewhere; the actual complex boundary and its norm G are separate. These documented notation/domain repairs preserve the noninteger and half-integer formulas. Two unfolded source regressions and all public declarations are registered for the exhaustive audit. At the N=0 checkpoint the package had thirteen production modules and two verification modules, all imported and classified. That checkpoint left the fully shifted general-N statement and its final acceptance checks open; that historical checkpoint had 3/20 gates complete. Part II and all AFEs were still OPEN at that stage.

## Fully shifted Part I accepted implementation

PoissonShift proves the complete corrected Part I theorem for every natural N<f′(b). Its explicit hypothesis record is built from the printed strict phase monotonicity and positive weight together with the two owner-approved conditions; the core theorem also allows nonnegative weights. The proof transports every condition to f−Nx, proves equality at all integer samples (including negative integers), reindexes the actual Fourier range to N≤ν≤floor(f′(a)), and identifies δ=1−fract(f′(a)). The error uses floor(f′(a))−N consistently in both logarithmic and reciprocal terms, and its actual complex boundary uses the shifted phase. These are the fully shifted E06 corrections, not a claim that the derivative or general boundary is invariant.

Public endpoints are corrected_poisson_partI, corrected_poisson_partI_noninteger and corrected_poisson_partI_half_integer. Two unfolded general-N regressions complement the two N=0 consumers and preserve every constant and endpoint term. No result equivalent to a remainder bound is assumed. At the DKQH-08 checkpoint the inventory was 80 files, fourteen production modules and two verification modules. DKQH-08 was accepted after its exact-source review, focused audit and sequential foundation/paper BATs passed. That acceptance checkpoint had 4/20 gates complete.

## DKQH-08 completion evidence

The accepted source contract is the owner-approved Part-I monotonicity repair with the documented E01/E06 endpoint, Fourier and full phase-shift corrections. Public corrected_poisson_partI and its noninteger/half-integer specializations prove the actual weighted sum minus the actual Fourier main term for every natural N<f′(b). The regularity records contain only analytic hypotheses; partIRegularityAt_of_source_hypotheses derives the general record from the printed strict phase/positive weight assumptions plus the accepted repair. The proof permits zero/nonnegative weights without a limiting assumption. General integer endpoints use the exact harmonic finite sum, and half-integers have zero complex boundary and the printed log(2) refinement.

The four unfolded SemanticRegression.partI_zero_source, partI_zero_half_integer_source, partI_general_source and partI_general_half_integer_source consumers verify source objects, endpoints, δ, floor shifts, constants and the fully shifted G term independently of the exhaustive dependency check. The proof chain uses the existing foundation nonstationary theorem, Lemma 1/11 and Lemma 2, the new Abel integral argument, translated Euler–Maclaurin and finite integration by parts. G05’s oscillatory tail bounds are inputs to Part II, not the completed Part-I argument; the diagram removes the speculative G05→G08 edge.

Both sequential verifiers passed with zero Lean errors, warnings, tactic suggestions or linter failures. DKQH-08 is DONE and the total is 4/20. At that checkpoint DKQH-09/10/12 and all other unfinished gates remained OPEN. This is completion of the corrected Part-I contract, not the unchanged false printed theorem or the whole paper.

## Theorem 9 implementation and acceptance review

PoissonApplications derives the first Corollary-0.1 estimate from the constant weight and verifies every corrected Part-I hypothesis for the actual AFE power/logarithmic weights. ZetaTruncation consumes the existing node-71 Zeta0EqZeta and ZetaBnd_aux1b continuation/tail proofs, proves regularized Dirichlet-sum convergence, conjugates the actual wave to n^(-s), and proves the integer/natural sharp-cutoff and power-integral identities. AFEFirstKind.afe_first_kind assembles the exact m(c) bound for all 0<σ≤1, t≥t₀>0, c>1/(2π) and half-integer ct. The n=1 term is included under the documented E01 repair; ct=1/2 is explicitly covered, without importing the proof's unnecessary x>1 restriction.

The exact Gamma-derivative convention is proved by afeFirstConstant_eq_source. Three new unfolded semantic consumers cover Corollary 0.1 Part I, the complete source Theorem 9, and its smallest positive half-integer cutoff. At the DKQH-12 acceptance checkpoint there were 83 retained files, seventeen production modules and two verification modules, with all public declarations registered for the exhaustive audit. DKQH-12 is DONE after exact-source review and the sequential verifiers passed; the accepted count is 5/20. DKQH-10 remains OPEN for its other corollaries, and DKQH-13 retains real-cutoff transfer and certified decimal constants. Part II and AFE2 remain OPEN.

## Real-cutoff AFE1 analytic transfer

AFEFirstMonotonicity proves the actual factor increasing on 0<u<1, a uniform finite-difference bound from the convergent digamma series, m(c)/c decreasing for all allowed c, and m(c) increasing for c≥1 and t₀≥1. These are analytic proofs on full intervals, without sampling, optimizer output or assumed derivative inequalities.

AFEFirstRealCutoff chooses x=floor(t)+1/2, proves equality of the actual sharp sums, and derives its scale c=x/t and every admissibility condition. The two scale branches are bounded by the exact three-way maximum in eq:def-c0, yielding afe_first_kind_real_cutoff for every real t≥t₀≥14 and 0<σ≤1. The full real-Gamma source maximum is identified by afeFirstRealConstant_eq_source and tested with the source integer-floor convention in SemanticRegression.corollary_zero_three_source. At the real-cutoff analytic checkpoint there were 85 files, nineteen production modules and two verification modules. All new public declarations are registered for audit. That analytic checkpoint left DKQH-13 OPEN for its two decimal certificates; the subsequent certification section records their implementation. The later DKQH-13 acceptance receipts supersede this analytic checkpoint.

## AFE1 decimal certification and DKQH-13 acceptance review

AFEDigammaNumerics proves ψ(x)≥log(x)−1/(2x)−1/(12x²) for every x>0 by a positive logarithm series, an explicit rational remainder and a finite telescoping limit. The actual digamma recurrence and ψ(1)=−γ then bound both special-function values by 31 finite reciprocal terms and elementary logarithms. The logarithms use proved finite Taylor lower/upper bounds after argument reduction. AFEFirstConstants checks four finite rational certificates with ordinary kernel-checked norm_num; pi is rounded downward from Mathlib's proved enclosure, and each reciprocal argument is rounded upward using proved factor monotonicity.

All six branches in the exact c₀ maxima are bounded. afeFirstRealConstant_small_le proves c₀(14.13472)≤1.2552; afeFirstRealConstant_large_le proves c₀(3·10^12)≤1.2127. The public afe_first_kind_small_decimal and afe_first_kind_large_decimal consume those certificates and the actual real-cutoff AFE. Two unfolded source consumers preserve σ∈(0,1], the exact thresholds, inclusion of n=1, actual ζ and the displayed decimals. No assumption about zero verification or RH occurs. At DKQH-13 acceptance the inventory was 87 files, twenty-one production modules and two verification modules. All new public declarations and consumers are registered. DKQH-13 is DONE after the exact-source review and sequential foundation/paper checks passed; the accepted count is 6/20.

## Chi reflection and Lemma 7 implementation

ChiReflection proves the valid functional equation ζ(s)=χ(s)ζ(1−s), χ(s)χ(1−s)=1 for every nonreal s, conjugation of the literal chi product and sharp sums, the exact reflected remainder with exchanged x/y, and equality of remainder norms at both height signs. It directly consumes the existing node-71 zeta conjugation theorem and covers the σ=1/dual σ=0 identity without a strict-strip restriction. It also proves |χ|=1 on the critical line. These are algebraic/branch bridges; the AFE2 analytic bound is still open.

ChiGammaFactor proves the principal negative-imaginary power, the exact identity Γ(1−s)(2π/i)^(s−1)(1−exp(iπs))=χ(s), and the actual relative error exp(iπs)/(1−exp(iπs)). A uniform denominator bound gives the printed Lemma-7 estimate for |Im s|≥t₀>0, including negative heights. The printed e^(−πt) is large but valid when t<0; it is not silently replaced by e^(−π|t|) with the same branch. The conjugated theorem uses 2π/(−i) and proves the decaying e^(−π|t|) bound at negative heights. Five unfolded regressions cover the corrected functional equation, literal remainder reflection/conjugation, printed Lemma 7 and conjugate branch.

At the reflection/Lemma-7 checkpoint the inventory was 89 retained files, twenty-three production modules and two verification modules. All new public theorems and consumers are registered. At that checkpoint DKQH-07 remained OPEN for Lemma 6 and the accepted count was 6/20; the later Lemma-6 acceptance closes it. DKQH-15 remains OPEN for the actual reflected AFE bound. The subsequent reflection/digamma sequential checkpoint verifies this scope; the earlier focused audit recorded 591 exhaustive theorem dependencies and 367 registered consumers with zero diagnostics.

## Explicit digamma input for Lemma 6

GammaDigammaReal proves |Re ψ(x+it)−log t|≤1/(2t) for every t>0 and 0≤x≤1/2, including x=0. The proof consumes the actual complex digamma series, specializes the existing Euler–Maclaurin theorem, and computes the full variation of the real reciprocal u/(u²+t²) on either side of its critical point u=t. Finite endpoint terms are retained before taking the limit. This is a uniform analytic inequality, without a grid or an assumed Gamma estimate. It supplies the full χ bound with C₀–C₃ in the subsequent accepted DKQH-07 chain.

The preceding digamma checkpoint had 90 retained files, twenty-four production modules and two verification modules. All new public theorems are registered; the focused audit passed with 624 exhaustive theorem dependencies, 396 registered consumers and zero diagnostics. The accepted count remains 6/20.

## DKQH-07 acceptance: full Lemmas 6–7 — 5 October 2026

GammaHorizontal proves the logarithmic Gamma derivative and explicit horizontal comparison on the closed real-part interval [0,1/2], including zero. GammaAnchors derives the exact norms at 0+it and 1/2+it from Gamma reflection, recurrence and conjugation. GammaStrip combines them with the proved digamma inequality to bound the actual Gamma modulus using the distance to the nearer endpoint.

ChiConstants defines the literal printed C₀–C₃, proves the exact factorization C₀=C₂(1+exp(−πt₀))(1+C₁/t₀), and proves uniform absorption of both exponential corrections. ChiBound.norm_chi_le_chiC0 concludes the source inequality for every 1/2≤σ≤1 and |t|≥t₀≥1/π. Its proof consumes the actual Gamma product and principal-power identity, preserves the height scale, and transfers negative heights by proved conjugation. SemanticRegression.lemma_six_source unfolds the chi product and all four printed formulas. No numerical sample, Stirling remainder assumption or additional source hypothesis is used.

The current inventory is 95 retained files, twenty-nine production modules and two verification modules. Every new production module is classified and root-imported; all public theorems are registered. DKQH-07 is DONE after exact-source review, exhaustive audit and sequential foundation/paper verification. The accepted total is 7/20. The Reproduction Manifest records both log paths and hashes. Part II, stationary phase and the AFE2 estimates remain open.

## Weighted-integral development after DKQH-07 acceptance

FirstDerivativeTest proves source Lemma 4 with constant 2, both monotonicity directions and the supremum over the actual interval. The decreasing case directly consumes the existing node-71 theorem through NonstationaryPhase; reflection proves the increasing case. The maximum is proved to occur at an endpoint. WeightedIntegralSums proves the exact finite quadratic/reciprocal bound with its 1/(8y²) correction and the weighted alternating boundary estimate. These have exact-source consumers and registered public declarations.

WeightedIntegrals defines the actual finite J(a,b,m), proves local integrability for Re(s)<1 and performs both integrations by parts including the zero endpoint. LowerIntegralEstimate sums these identities before taking norms and proves the complete first inequality of Lemma 5, preserving both height signs, the physical scale, both half-integer cutoffs and every printed constant. UpperIntegralEstimate proves conditional improper convergence and the complete second inequality of Lemma 5, with constant 2/π and log(y)+1. DKQH-06 is DONE after the stationary-point and phase proofs and their sequential verification. The current inventory is 181 retained files, ninety-seven production modules and two verification modules; the accepted count is 8/20. The last full sequential receipts cover the preceding 119-file finite-inequality checkpoint; the Reproduction Manifest records exact scope, paths and hashes.

WeightedIntegralPhase discharges the actual power/logarithmic-phase quotient monotonicity for both height signs, applies Lemma 4 on positive truncated intervals, and passes to zero by proved continuity of the integrable primitive. Its source-scale consumer bounds the literal integral of u^(2−s) exp(2πimu) by x^(2−σ)/(π(y−m)), deriving the cutoff condition from 2πxy=|t|. The complete first Lemma-5 sum is now proved in LowerIntegralEstimate and consumed literally by lemma_five_lower_sum_source. The complete upper-tail bound and convergence are now proved in UpperIntegralEstimate and checked by lemma_five_upper_sum_source.

The minimal node-63 Fresnel adaptation now proves the actual symmetric quadratic-integral limit, its principal branch exp(−πi/4), and the quantitative finite-window error. StationaryPoints derives the unique point in the actual decreasing derivative range, proves the shifted phase derivative vanishes, identifies the logarithmic J-phase critical point and its height-sign restriction, and consumes the Fresnel limit to obtain exp(2πi(f(xν)−νxν−1/8))/sqrt(|f″(xν)|). Three independent source consumers check point selection, the finite-window estimate and the phase/amplitude limit. These complete DKQH-06 after the exact-source checks, exhaustive audit and sequential foundation/paper verification. DKQH-11 still requires the nonlinear replacement estimate and all printed B-process error constants. Attribution and exact source hashes are in Dependencies and local_reuse_inventory.json.

## Actual AFE integral assembly — 5 October 2026

DampedWeightedKernel directly consumes the pinned foundation's DFIComplexLaplace theorem for the actual exponentially damped kernel. Dominated convergence removes damping on finite intervals; integration by parts against the proved oscillatory primitive gives a damping-uniform tail bound. These prove the actual conditionally convergent J(0,∞,m) equals (−2πim)^(s−1)Γ(1−s), with the principal branch explicitly normalized to Γ(1−s)(2π/i)^(s−1)m^(s−1). Lemma 7 then supplies the actual χ factor and its signed-height relative error. No convergence or Gamma evaluation is an assumed theorem parameter.

WeightedIntegralAssembly sums the actual positive integer frequencies and isolates m=1 to prove the dual polynomial bound y^σ log(y)+1, including σ=0 in that finite bound. Its public norm_sum_weightedIntegral_sub_chi_le combines the exact main integral with both complete Lemma-5 estimates. SemanticRegression.weighted_integral_gamma_source, weighted_integral_chi_source and afe_integral_sum_source retain literal integrals, the physical relation 2πxy=|t|, half-integer cutoffs, principal powers, and every constant. The assembled integral estimate is proved for 0<σ<1; individual zero-endpoint/improper integrals are not asserted to converge at both strip endpoints.

This completes the integral stage of equation (4.59), not Theorem 10. DKQH-14 and DKQH-15 remain OPEN for the Poisson-to-zeta assembly, endpoint continuation, accepted error formulas and direct/reflected bounds. DKQH-09 still has the separate positive-frequency monotonicity gap; the Part-II E₁ sign correction remains an owner-decision proposal. No additional gate is accepted: 8/20 are DONE. The current inventory has 181 retained files, 115 production modules and two verification modules; all are classified and root-imported. The Reproduction Manifest distinguishes focused and sequential evidence.

## AFE second-derivative conditions and B-process decimal

AFESecondWeights proves the actual second derivatives of u^(−σ) and (t/(2π))log(u), and the derivative of their weight/phase-derivative product. It proves the printed decreasing conditions and strict positivity when σ,t>0. For every positive frequency, all four positive-frequency quotients normalize to a nonnegative constant times u^(−σ)/(νu+t/(2π))^k, k=2 or 3, and are proved nonincreasing on u>0. These proofs include σ=0. The actual functions and physical t/(2π) scale are unfolded in two semantic consumers. This resolves those application-specific conditions; the general Part-II inference remains unproved and no new general hypotheses have been adopted.

StationaryConstants proves (2/π)(γ+2log(2))≤1.251 from the existing finite Euler-constant/logarithm bounds and a rational pi enclosure. Its source consumer proves the literal −(2/π)Re ψ(1/2) bound. This certifies the numerical component in the B-process; the nonlinear stationary-phase replacement, endpoint modes and the complete 2.686/error estimate remain OPEN under DKQH-11. No new gate is accepted; 8/20 are DONE.

The preceding derivative/decimal scope has 112 retained files and 46 production modules, with two explicit verification modules. All production modules are classified and root-imported, and every new public theorem is registered. The latest full sequential receipts cover the preceding 119-file finite-inequality stage; current-scope verification is recorded separately in the Reproduction Manifest.

## Second oscillatory integration: actual source inputs

OscillatoryParts proves integration by parts for the actual weighted exponential, retaining the complex endpoint factor 1/(2πi). Its general technical estimate explicitly assumes the two amplitude/derivative quotients are nonincreasing and derives the remainder by the proved first-derivative test. The negative-frequency specialization derives both quotient conditions from decreasing |h|, |h′|, |f″| and f′ above the frequency cutoff. AFESecondModes applies the positive-frequency estimate to each actual amplitude h=g′ and h=gf′, using AFESecondWeights to discharge all regularity and quotient conditions, including σ=0. The source consumers retain the actual integrals, complex boundaries, squared/cubed denominators, physical t/(2π) scale and constants 1/(2π²).

These are proved integral estimates, not the complete weighted Poisson Part II formula. The infinite coefficient summation, full H/H₁/B/E assembly, general-N transfer and remaining source decisions stay OPEN under DKQH-09. The Part-II E₁ sign correction remains pending owner approval, and no new general Part-II hypotheses have been adopted. Current scope: 181 retained files, 115 production modules and both verification modules; 8/20 gates remain complete. Exact current-scope evidence is recorded in the Reproduction Manifest.

## Part-II positive-frequency inference: concrete diagnostic

PartIIMonotonicity proves a smooth polynomial example on [0,1]: f(u)=2u−u²/20+u³/300 and g(u)=10−u+u²/20−u³/6000. The printed positive/decreasing conditions hold strictly, and the already accepted Part-I conditions also hold. Nevertheless |g″|/(1+f′)² increases between the endpoints: its values are 1/90 and 110/9409. The complete hypothesis conjunction and failed quotient inference are kernel-checked; SemanticRegression unfolds both polynomials. This refutes the intermediate monotonicity assertion preceding bnd-int-plus-h1, not the full Part-II inequality.

A concrete candidate repair is to require, for h=g′ and h=g(f′−N), both |h′|/(ν+f′−N)² and |h f″|/(ν+f′−N)³ to be nonincreasing for every positive integer ν. These are four analytic input conditions, not the Poisson conclusion. AFESecondWeights already proves them for the actual N=0 AFE weights and phase, including σ=0; OscillatoryParts and AFESecondModes consume them in the second-integration estimate. No additional general Part-II hypotheses have been adopted. The scope decision and the separate E₁ sign decision remain distinct. DKQH-01 and DKQH-09 remain OPEN; total 8/20 DONE.

## Positive-frequency second-integration series

SecondModeTails proves absolute convergence of the actual series of integrals divided by 2πν, identifies its complex endpoint sums with positiveTail, and bounds the remaining square/cube series using the complete Lemma-1 coefficients. The endpoint cancellations are retained before taking norms. The generic theorem exposes the required analytic quotient conditions. AFESecondModes.afe_positive_second_tail_bound discharges all of them for h=g′ and h=gf′ with g(u)=u^(−σ), f(u)=(t/(2π))log(u), t>0 and σ≥0. The new semantic consumer states the literal integral series at that physical scale, including σ=0. This is the positive-frequency series component; the upper-frequency series, H/H₁ assembly, general-N transfer, E₁ decision and general Part-II scope decision remain open under DKQH-09. The accepted count remains 8/20.

## Upper-frequency series and actual Poisson coefficient assembly

UpperModeTails proves absolute convergence, exact oscillatory endpoint sums and both complete square/cube harmonic bounds for all frequencies above M. AFESecondWeights proves decreasing absolute amplitudes and their derivatives for both actual AFE choices, including σ=0. AFESecondModes.afe_upper_second_tail_bound discharges every analytic condition; its source consumer fixes M=floor(t/(2πa)) and derives the strict cutoff inequality.

SecondCoefficients proves the actual derivative integral splits into the g′ and gf′ integrals, tracks the factors 1/i and 2π in each Fourier coefficient, and sums those identities using proved convergence. Its afe_second_poisson_identity applies the existing exact finite Poisson identity to the actual AFE functions and derives all four series-convergence inputs from the new tail estimates. The physical-scale source consumer uses the actual logarithmic phase, power weight and floor cutoff. These close the series-to-Poisson identity bridge. The H/H₁/B/E inequality assembly, general-N transfer and unresolved source decisions remain OPEN under DKQH-09; AFE2 and the B-process remain incomplete. Current inventory: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Actual second-order finite AFE Poisson inequality

SecondCoeffBounds combines the two real-amplitude estimates into the literal H and H₁ numerators, deriving the product-derivative bound and proving the scalar coefficients nonnegative from their actual harmonic series. The generic coefficient-combination helpers expose their narrower amplitude-bound inputs; afe_positiveCoefficient_bound and afe_negativeCoefficient_bound discharge them from the proved AFE series estimates. The public afe_finite_poisson_second_bound then consumes the existing exact finite Poisson identity to bound the actual weighted integer sum minus the actual Fourier-integral sum, with both endpoints, the complex boundary norm, and both square/cube coefficient contributions present. Its source consumer states the literal finite sum and Fourier integrals at t/(2π), including σ=0.

The actual AFE inequality keeps the positive and negative square coefficients separate. Their exact equality to the proposed E₁ envelope divided by y is proved as a diagnostic, without adopting the pending repair. The cube coefficients assemble exactly to the unchanged printed E₂; a literal source consumer proves its bound on both actual cube tails. General Part-II scope, the E₁ decision, the Z₀/Z₁ endpoint simplification and shifted-N source contract remain open under DKQH-09. The AFE2 zeta-limit, direct/reflected bounds and numerical obligations remain open. The accepted count stays 8/20; current scope is 181 retained files, 115 production and two verification modules, 226 semantic consumers.

## Half-integer endpoints and uniform tails

SecondEndpoints proves conjugation of the actual positive tail, its norm symmetry, and the complete half-integer B bound with π/2, log(2), the first omitted-frequency correction and the 3/2 correction. It applies this bound and the existing exact half-integer boundary identities to the actual AFE finite Poisson inequality. All endpoint, cutoff and nonnegativity conditions are derived from the stated hypotheses; the two square coefficients remain separate pending the E₁ decision. The source consumer states the literal finite sum and Fourier integrals at t/(2π), including σ=0.

The actual tails also have uniform bounds 2 for the positive tail and 4 for the negative tail when 0<y≤1/2, at every real endpoint including integers. These are limiting-argument inputs, not new source constants. The general-N Part-II contract, source decisions and actual zeta-limit remain open. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Actual strict-strip AFE assembly

AFESecondLimits proves the upper-endpoint contribution tends to zero, conjugates the actual finite Poisson formula, and consumes the existing zeta truncation and convergent weighted-integral tails. The resulting afe_zeta_sub_sum_pole_integrals_bound has the actual ζ value, sharp polynomial, pole term and positive-frequency improper integrals. afe_strict_strip_bound then applies the proved Gamma/χ and lower-integral estimates to obtain the actual two-polynomial AFE for 0<σ<1 and positive t, with half-integer x,y≥1 and 2πxy=t. Every error term is retained explicitly; no remainder estimate or convergence certificate is an input.

The separate positive and negative square coefficients remain visible, so this theorem does not adopt the pending Part-II E₁ correction. DKQH-14/15 remain OPEN for closed-strip endpoints, accepted source error formulas, both height signs and the reflected quantitative branch. General Part-II scope and numerical obligations also remain OPEN. Earlier checkpoint descriptions of the missing Poisson-to-zeta assembly are superseded by this proof. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20. The Reproduction Manifest records verification scope separately from source completion.

## Closed-strip AFE and reflected quantitative estimate

AFESecondClosed extends the assembled estimate continuously to 0≤σ≤1. It proves continuity of the actual sharp polynomials, χ and nonreal ζ remainder, substitutes the exact H/H₁ formulas, and applies the strict-strip theorem on the closure. No convergence of the individual zero-endpoint improper integrals is assumed at σ=0 or σ=1. Conjugation gives afe_closed_strip_abs_bound with positive |t| throughout the error. afe_closed_strip_reflected_bound consumes the actual functional equation and the direct bound at 1−σ with exchanged cutoffs; afe_closed_strip_min_bound proves both estimates simultaneously.

The E07 dual-endpoint proof obligation is therefore resolved for this explicit assembled bound. E04's height-sign bridge is also quantitative. Theorem 10's stated constants, parameter-uniform A₀/B₀ simplifications and equation-(5.2) branch decision remain separate obligations under DKQH-14/15; these gates remain OPEN. No pending general Part-II correction is adopted. Earlier checkpoint lists of missing endpoint/reflection assembly are superseded by this proof. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20. Verification receipts are recorded in the Reproduction Manifest.

## Cancellation and half-integer coefficient simplification

SecondTailSharp retains the subtraction between two nonnegative paired reciprocal sums. It proves the actual negative tail is at most π/(2y), and the positive tail at most log(2)/y, at half-integer endpoints with δ≥1/2. Their sum is bounded by (π/2+log(2))/y. AFESecondLimits now consumes this stronger endpoint theorem, and AFESecondClosed carries the improved error through the same endpoint-continuity and reflection proofs. The older literal Corollary-8.1 endpoint bound remains preserved in SecondEndpoints.

SecondHalfErrors adds the positive and negative square/cube majorants exactly at half-integer y, retaining their correct signs. Analytic logarithmic and rational inequalities prove their bounds 46/(9y) and 230/(27y) on the source AFE domain. Unfolded consumers apply these to the actual infinite square/cube series. No numerical optimization, source-E₁ adoption or general Part-II hypothesis change is involved. The source-constant A₀/B₀ assembly and all remaining gate obligations remain OPEN. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Literal A/B formulas assembled for the actual AFE

AFESecondBounds proves afe_second_source_AB and afe_second_source_AB_reflected for the actual ζ remainder and both sharp Dirichlet polynomials, including σ=0, σ=1 and both height signs. The A expression contains every term of def:A(s,t,x,y); B is exactly def:B(s,t,x,y), evaluated at positive |t|. The stronger endpoint cancellation and the proved 46/9 and 230/27 bounds imply this source A expression, with an explicit nonnegative difference. The Gamma error factors exactly into B·y^(σ−1). Reflection cancels the reciprocal χ factors and yields log(x) with exchanged cutoffs and the dual exponent.

Two literal source consumers unfold both polynomials and every A/B coefficient. Uniform A₀/B₀ estimates, the equation-(5.2) branch resolution and certified table bounds remain OPEN under DKQH-14–17. This progress does not adopt the pending general Part-II repairs or close a gate. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Theorem-10 proof-consistent branches proved; E03 adoption pending

AFESecondUniform proves afe_second_uniform_direct, afe_second_uniform_reflected and their piecewise assembly afe_second_uniform_branches. They concern the actual ζ remainder and both sharp polynomials, with 1/2≤σ≤1, |t|≥t₀≥2π, half-integer x,y≥h≥3/2, and 2πxy=|t|. Every term of A₀, B₀ and the already proved C₀ is retained. The larger cutoff is proved to exceed x₀=max(h,sqrt(t₀/(2π))); the complete B numerator is proved decreasing analytically on the entire normalized interval z≥1. Source consumers unfold both polynomials and every A₀/B₀ term. The proofs include the diagonal, σ=1/dual σ=0, both height signs and exact logarithmic coefficients.

The proved assignment is E_direct=A₀(σ,h,t₀)+C₀(σ,t₀)B₀(σ,t₀) for x≥y and E_reflect=A₀(1−σ,h,t₀)C₀(σ,t₀)+B₀(1−σ,t₀) for x<y. This agrees with the derivation and ancillary call sites; the printed equation (5.2) reverses these E₀ assignments. The frozen printed version is preserved. Adopting the proof-consistent quantitative contract requires the explicit E03 scope decision before DKQH-14/15 can be marked DONE; neither the earlier Part-I approval nor the separate pending Part-II proposals supplies that decision. The existing whole-paper count remains 8/20. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers. Reproduction evidence distinguishes this implementation from source-contract acceptance.

## General second-order analytic interface and constant-weight Part I

PoissonCorollary proves Corollary 0.1 Part I with the actual unweighted sum, literal Fourier integrals, and every printed logarithmic/digamma constant. The constant weight discharges both accepted Part-I repair hypotheses, and the more general theorem retains every allowed lower frequency N.

PartIIInputs proves convergence, both coefficient estimates, and the complete finite second-order Poisson inequality for general f and g from an explicit provisional SecondOrderRegularity interface. Its inputs are closed-interval differentiability/continuity, decreasing absolute derivatives, and the two positive-frequency quotient conditions for each actual amplitude g′ and gf′. None is a remainder bound or conclusion-equivalent certificate. The actual AFE logarithmic phase and power weight satisfy every field, including sigma=0, and a separate consumer applies the general inequality to them. The two square coefficients remain separate, while the actual H/H₁ and boundary terms are retained.

This technical conditional theorem does not adopt a revised general source contract. The Part-II quotient and E₁ proposals and the Theorem-10 E03 decision remain pending. General-N Part-II transport, explicit endpoint-majorant packaging, Part-II corollaries and the B-process remain under DKQH-09–11. DKQH-10 is still OPEN because Part I alone does not complete all its corollaries. The accepted count remains 8/20. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers. Verification evidence and exact scope are recorded separately in the Reproduction Manifest.

## General second-order endpoint and frequency transport

PartIIBounds proves the complete explicit Poisson inequality from the provisional SecondOrderRegularity inputs at every real endpoint. Away from integers its endpoint factor is the literal Z₀+Z₁. At integer endpoints, where the printed sine denominator is undefined, the finite harmonic convention and exact absolute reciprocal-tail digamma bound give a proved extension. The actual complex G boundary is retained. A separate identity packages the two square coefficients into the proposed E₁ and the unchanged E₂ without adopting the pending quantitative repair.

The actual weighted integer sum and Fourier main sum transport to every allowed N through f(u)−Nu. The shifted half-integer theorem retains M=floor(f′(a))−N, y=f′(a)−N, the invariant δ=1−fract(f′(a)), every H/H₁ term and the literal half-integer B majorant for δ≥1/2. Exact consumers expose both sums. These close the analytic endpoint and general-N transport obligations for this provisional interface. Mapping and adopting the corrected source hypotheses, the pending E₁ decision, and the remaining Part-II corollary/B-process obligations still keep DKQH-09–11 OPEN. The accepted count remains 8/20. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers.

## Constant-weight second order and exact AFE maxima

PartIIConstant discharges every constant-weight field from explicit phase regularity and two positive-frequency quotient conditions. Its full unweighted half-integer estimate retains both square/cube coefficients and both endpoint B terms. The proved finite-head term is (log(2)+1/f′(a))/π. The printed Corollary 0.1 Part II writes half that term and references the δ=1/2 B formula without that restriction. These are unresolved source-correspondence issues, not silently accepted changes; the present specialization requires δ≥1/2 and keeps its proved coefficient. No counterexample to that entire printed corollary is claimed here.

AFEUniformMax proves continuity of every A₀/B₀/C₀ term, existence and attainment of the exact direct/reflected maxima on the whole closed interval [1/2,1], and nonnegativity of δ₀=max(C₀)−1. The actual two-polynomial AFE consumes these maxima in both Corollary-0.4 logarithmic branches. The exact hₖ=floor(exp(k−1))+1/2 band endpoints satisfy hₖ≥3/2, and both Corollary-0.5 band estimates follow for every integer k≥1, in particular k=1,...,50. The proof covers both height signs and sigma endpoints. No numerical maximum, decimal table value or optimization output is an assumption.

The global analytic maxima and band deductions are proved for the proof-consistent Theorem-10 assignment, whose E03 adoption remains pending. Table certification, accepted decimal rounding, the k/π+1.1601 bound and constant-6 consequence are still OPEN under DKQH-16/17. Earlier descriptions of global maximum existence and band transfer as missing are superseded by these proofs. DKQH-09–11 also remain OPEN for their stated source and stationary-phase obligations. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Literal constant-six consequence proved

AFECoarseConstants proves afe_constant_six_direct, afe_constant_six_reflected and the piecewise afe_constant_six. These are the actual two-polynomial remainder with the unchanged constant 6, 1/2≤sigma≤1, |t|≥2π, half-integer x,y≥1, 2πxy=|t|, and min(x,y)≤10^6. Both height signs, the diagonal and sigma=1 are covered. Two source consumers unfold both polynomials.

The proof derives C₀≤1+1/t₀ and B₀≤1/t₀², proves rational bounds on every A₀ term, and splits the smaller cutoff at 100. The physical product scale proves |t|≥60000 on the larger-cutoff interval, where A₀≤5/4. Finite exponential series certify log(2)≤7/10 and log(10)≤7/3. Thus no table decimal, numerical optimizer or assumed error bound enters this consequence. This closes the constant-six sub-obligation of DKQH-17; the table cells and k/π+1.1601 certification remain open. No pending source decision is silently adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## The unchanged large-k decimal bound certified

AFEBandConstants proves afe_band_coefficients_large_k: both exact source epsilon-k expressions are at most k/π+1.1601 for every integer 11≤k≤50 at t₀=10^10. The actual direct and reflected AFE consumers, afe_large_k_direct and afe_large_k_reflected, apply that certificate to the full sharp polynomials, including both height signs and sigma endpoints.

Finite rational logarithm/Euler bounds prove log(2)≤0.693148 and gamma≤0.577216; a finite exponential sum proves exp(10)≥22000. The physical x₀ exceeds 39890 at the exact threshold, independently of h. Every A₀ term is bounded on the complete sigma interval, giving A₀≤1.160097. The proved bounds C₀≤1+1/t₀ and B₀≤1/t₀² control both attained maxima and the k-delta correction with a rigorous margin below 1.1601. No floating-point value or optimizer result is used as evidence.

The large-k and constant-six sub-obligations are now proved. Table 1–3 cells and outward rounding/source adoption still keep DKQH-16/17 OPEN; the pending E03 decision and general Part-II decisions remain separate. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20. The Reproduction Manifest distinguishes the preceding full sequential scope from this expanded verification.

## Table 3 certified on every displayed range

AFETableThree proves both exact analytic epsilon coefficients lie below the eight unchanged source bounds, for every integer 11≤k≤50 and the entire closed sigma strip. Finite rational logarithm and Euler-constant enclosures, finite exponential series, global maximum bounds and exact rational arithmetic certify the group endpoints. The previously proved k/π+1.1601 bound covers each interior integer. The actual direct and reflected zeta remainders consume these certificates, with both height signs and the full half-integer cutoff conditions. No numerical samples or assumed decimal inequalities enter the proofs.

Table 3, the large-k bound and the constant-six consequence are now proved. Table 1–2 certification and accepted rounding corrections still keep DKQH-16/17 OPEN; E03 and general Part-II decisions remain pending. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20. Verification receipts are recorded separately in the Reproduction Manifest.

## Table 1 failures and proposed Table 2 certificates

TableLowerBounds proves a fourth-order upper estimate for the actual digamma function and a finite lower enclosure 0.577215664≤γ. Combined with rational logarithm/pi bounds, it proves that Table 1's direct entries 2.265204 at exact 2π, 1.792736 at 1000, and 1.750701 at 10¹⁰ are strictly below the actual direct maxima: sigma=1 supplies each witness. These are failures of the claimed numerical maximum bounds, not counterexamples to the zeta remainder inequality itself. The printed entries remain preserved.

AFETableTwo proves outward candidate bounds for all twenty cells at k=1,...,10, over the complete closed sigma strip. Finite exponential sums certify the floor-defined lower cutoffs. Distinct sigma ranges for the two A₀ inputs give separate direct/reflected rational certificates, propagated through the actual global maxima and then the actual two-polynomial AFE. The proposed decimals are listed in Computation Review and explicitly named proposedTableTwoDirect/proposedTableTwoReflected; they are not yet an adopted source repair.

The unchanged Table 3, large-k bound and constant-six consequence remain proved. DKQH-16/17 stay OPEN for the remaining Table 1 certificates and explicit adoption of numerical repairs. General Part-II and E03 decisions remain pending. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Global chi-factor table certificates

ChiTableBounds bounds the actual C₁ on the entire closed sigma strip by a concave cubic and an explicit sum-of-squares identity. A finite Taylor remainder certifies C₂; finite positive exponential sums bound the remaining tails. The complete C₀ product and its actual attained maximum therefore give δ₀≤0.05961930 at exact 2π, δ₀≤0.0003692901 at 1000, δ₀≤3.692588·10⁻¹¹ at 10¹⁰, and δ₀≤1.230863·10⁻¹³ at 3·10¹². The last two are unchanged printed values; the first two are proposed outward replacements, not yet adopted. No optimizer output or sampled interval enters these proofs.

The remaining Table 1 epsilon assembly and numerical-repair adoption stay OPEN under DKQH-16. Table 2 candidates, unchanged Table 3, large-k and constant-six bounds are proved as described above. Pending Part-II and E03 decisions are unchanged. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Complete proposed Table 1 AFE certificates

AFETableOne proves all sixteen proposed Table 1 cells over the entire closed sigma strip. The four thresholds retain exact 2π in the first row. The symmetric lower cutoffs are proved equal to floor(sqrt(t₀/(2π)))+1/2 and are derived from the physical height, half-integer condition and x=y; no extra symmetric-cutoff hypothesis remains. Separate actual direct, reflected and symmetric zeta-remainder theorems consume all coefficient certificates, preserve logarithmic factors and cover both signs of t.

The complete proposed Table 1 and Table 2 replacements are listed beside the preserved printed values in Computation Review. All unchanged Table 3 entries, k/π+1.1601 and the constant-six consequence are also proved. Numerical source-repair adoption and E03 remain pending before DKQH-16/17 can be accepted. The general Part-II decisions and DKQH-09–11 obligations remain separate. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Explicit shifted Part II inputs and the exact half-offset case

PartIIShiftInputs derives the shifted second derivative at closed-interval endpoints from local nonvanishing of f′, rather than assuming a derivative identity outside the interval. It constructs the provisional SecondOrderRegularity interface from explicit twice-differentiable inputs and the pending positive-frequency quotient hypotheses. The shifted product-amplitude monotonicity follows from the existing Part I repair, nonincreasing |f″| and the derivative signs. Its consumers prove the actual full weighted Poisson inequality for every permitted N, at general endpoints and half-integer endpoints.

PartIIHalfSource derives literal square/cube and B expressions when δ=1/2 for every positive y=f′(a)−N, including y=1/2 and M=0. The full weighted-sum bound, its frequency transport and its explicit-analytic-input consumer retain the actual exponential sum and Fourier main sum. The E₁ expression is the proposed sign correction; E₂ is unchanged. This adds proof coverage without adopting the pending quotient or E₁ repairs. Mapping the final accepted source regularity, the remaining Corollary 0.1 discrepancy and the nonlinear B-process still keep DKQH-09–11 OPEN. Earlier descriptions of the shift-input and exact-half-offset bridges as missing are superseded. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Stationary Taylor proof and B-process source review

StationaryTaylor proves the cubic phase remainder D|x|³/6, its derivative remainder D|x|²/2, the exponential perturbation bound πD|x|³/3 and the exact factorization of the actual shifted phase. These require existence of the first three ordinary derivatives on the genuine segment, with the third derivative bounded by D; continuity of the third derivative and infinite smoothness are not assumed. The finite Taylor proof builds the required lower-order smoothness and identifies the within-interval derivatives before applying Mathlib's Lagrange remainder. This is an input to nonlinear stationary phase, not its completed integral estimate.

BProcessReview checks the smooth quadratic f(u)=651u/200−151u²/200 on [1/2,3/2]. Its derivative runs strictly down from β=5/2 to α=99/100, with constant curvature −151/100 and zero third derivative. On the paper's interior range 1≤ν≤floor(β)−1, the reciprocal endpoint majorant in the cited stationary-phase deduction equals 302/(3π), which is strictly greater than 1.251+(2/π)log(β−α). Patel–Yang's cited argument instead restricts frequencies to α+1/2<ν<β−1/2; the paper's range does not preserve that separation. This is a proved failure of the reciprocal-majorant deduction, not a counterexample to the actual complex S₃ remainder or the full B-process inequality.

The review also proves that deleting the last stationary frequency changes the main sum by a term of exact norm 1/sqrt(|f″(x_M)|). The paper's proof uses frequencies 1 through M−1 whereas its conclusion uses 1 through M; a complete argument must account for that term or prove a different joint endpoint estimate. Neither diagnostic licenses an unapproved change to 2.686 or to the source conclusion. DKQH-11 remains OPEN for the nonlinear integral, boundary-frequency accounting and exact constant. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Central stationary-phase integral proved

StationaryPerturb proves the actual shifted central-window integral differs from its quadratic replacement by at most Dδ²/|f″(c)|, where f′(c)=ν. The hypotheses require the first three ordinary derivatives on [c−δ,c+δ], |f‴|≤D, δ>0 and f″(c)≠0. The proof consumes the finite Taylor estimates, removes the apparent integration-by-parts pole at zero, proves the derivative amplitude integrable without assuming continuity of f‴, and retains the original complex exponential integral. Three exact-type consumers check the nonlinear perturbation, actual Taylor remainder and full shifted-phase estimate.

This completes the central nonlinear replacement only. Sharp quadratic tails, finite-window placement and boundary-frequency accounting for the complete 2.686 B-process estimate remain OPEN under DKQH-11. The documented source diagnostics and pending decisions are unchanged. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20. Verification receipts distinguish this scope from earlier checkpoints.

## Sharp Fresnel tail proved

FresnelSharp applies pinned Mathlib Cauchy–Goursat on an actual rectangle to exp(iρz²). The vertical sides have exact exponential majorants; the upper side vanishes as its height tends to infinity. This gives the finite-tail bound 1/(2ρa)+1/(2ρb), then conjugation and the existing Fresnel limit give the source-normalized symmetric tail 1/(π|κ|H) for negative curvature, retaining exp(2πi(A−1/8))/sqrt(|κ|). No whole-line Bochner integral of the undamped kernel is asserted. The existing coarser tail remains valid and unchanged.

The new sharp bound and the central nonlinear integral are inputs to the remaining whole-interval replacement, boundary-frequency accounting and 2.686 estimate under DKQH-11. They do not close that gate. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Whole-interval stationary estimate with a contained window

StationaryWindow combines the actual nonlinear central integral and sharp Fresnel tail, translates back to [c−δ,c+δ], and proves the two outer first-derivative estimates from the curvature lower bound. For a≤c−δ and c+δ≤b the actual integral on [a,b] differs from exp(2πi(f(c)−νc−1/8))/sqrt(|f″(c)|) by at most Dδ²/ℓ+3/(πℓδ), where f′(c)=ν, f″≤−ℓ<0 and |f‴|≤D. Choosing δ=(3/(πD))^(1/3), with D>0, proves the exact coefficient 2·3^(2/3)D^(1/3)/(π^(2/3)ℓ). Every scale and placement condition is explicit in the three regression consumers.

This is a proved contained-window case. The arbitrary placement case, zero third-derivative scale, endpoint frequencies and Kershner 2.686 accounting still require separate arguments before DKQH-11 can be accepted. No source constant or pending repair is changed. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Arbitrary interior placement with zero third derivative

QuadraticStationary proves the sharp asymmetric quadratic estimate with separate endpoint distances, then consumes the actual Taylor theorem when f‴=0 throughout [a,b]. At every interior stationary point c, with f′(c)=ν and f″(c)<0, the actual integral remainder is bounded by (1/(2π))(1/|f′(a)−ν|+1/|f′(b)−ν|). The frequency gaps are derived from the actual derivatives; no radius or symmetry assumption is imposed. This resolves the zero-third-derivative stationary replacement case and is stronger than the corresponding reciprocal coefficient in Patel–Yang Lemma 2.2.

Arbitrary placement for nonzero third-derivative bounds, the global Kershner estimate and complete B-process endpoint accounting remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Arbitrary-placement nonlinear stationary phase proved

TaylorLipschitz derives the exact cubic and derivative Taylor errors using a Lipschitz bound on curvature, then proves the actual integral estimate under those weaker regularity inputs. CurvatureExtension constructs an explicit global phase by projecting f″ onto [a,b] and integrating twice. Lean proves equality with f and f′ on the entire original interval, equality of its second derivative with the projected curvature, preservation of curvature bounds and the global Lipschitz estimate derived from the actual third derivative. No extension-existence assumption is introduced.

StationaryExtended consumes that construction to remove the central-window placement restriction. At every interior stationary point c with f′(c)=ν, f″≤−ℓ<0 and |f‴|≤D, the actual integral error is bounded by 2·3^(2/3)D^(1/3)/(π^(2/3)ℓ)+(1/π)(1/|f′(a)−ν|+1/|f′(b)−ν|). The main term is exp(2πi(f(c)−νc−1/8))/sqrt(|f″(c)|). D=0 is included by the independently proved quadratic case. The source-scale consumer separates D=h₃λ₃ exactly, and the existence consumer derives the interior stationary point from the actual strict derivative range. All first three ordinary derivatives are required on the closed source interval; continuity of the third derivative is not assumed.

This completes the nonlinear stationary replacement input used by Patel–Yang Lemma 2.2 on that explicit endpoint-regularity domain. The previously documented frequency-range and omitted-main-term issues, the global Kershner estimate and the complete 2.686 B-process accounting remain OPEN under DKQH-11. Earlier arbitrary-placement and zero-scale obligations are superseded by these proofs. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; accepted count 8/20.

## Actual interior stationary sum proved

StationarySum sums the actual nonlinear stationary integral errors, retaining the exact reciprocal endpoint gaps. For the paper’s interior frequencies 1 through floor(f′(a))−1, it derives the frequency count from the actual derivative range and bounds that range using |f″|≤h₂ℓ. The resulting nonlinear term is exactly 2·3^(2/3)h₂D^(1/3)(b−a)/π^(2/3), with D=h₃λ₃ available through the source-scale identity. Every supplied stationary point on the closed interval is proved to lie strictly inside it for these frequencies.

This proves the nonlinear frequency-sum term and preserves the full actual endpoint reciprocal sum. It does not replace that sum by the paper’s logarithmic expression: the documented counterexample to that intermediate inequality remains valid. The global Kershner bound and complete boundary-frequency/main-term accounting remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Exact endpoint sums and valid logarithmic subdomain proved

StationaryHarmonic evaluates both finite endpoint reciprocal sums using the actual digamma recurrence and derives the full interior stationary-integral estimate with those exact digamma terms. This result covers 0<f′(b)<1, including an empty interior frequency range, and retains the actual fractional gaps. A separate consumer proves the printed 2/π logarithmic coefficient and certified 1.251 constant when f′(b)≤1/2 and f′(a)≥1. These additional restrictions are explicit helper hypotheses, not an adopted change to Corollary 0.2.

The full B-process endpoint accounting, the 2.686 constant and the unrestricted source logarithmic deduction remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Stationary family derived from the source hypotheses

StationarySource derives the signed negative-curvature bound from the source’s decreasing f′ and lower bound on |f″|, including both endpoints. It constructs actual stationary points for every positive integer frequency through floor(f′(a)), proves the precise condition for coincidence with either endpoint, and consumes this family in the interior digamma and separated logarithmic estimates. Stationary points and signed curvature are no longer independent premises in those consumers. The closed-interval ordinary derivative requirements remain explicit.

These proofs discharge the source-to-interior-sum bridge. The complete boundary-frequency estimate with 2.686 and the unrestricted source logarithmic bound remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Fresnel numerical bound and quadratic 1.343 proved

FresnelNumeric proves a global norm bound of 119/100 for every actual primitive ∫₀ˣexp(it²)dt. On 0≤x≤33/20, the squared norm is an iterated cosine integral; the eighth-order Taylor upper bound integrates to an explicit polynomial, and four exact rational Bernstein identities prove its upper bound over the entire interval. The already proved sharp Fresnel tail covers larger x, and symmetry covers negative x. Scaling and phase rotation yield 1.343/sqrt(|κ|) for every actual quadratic-phase interval with negative curvature κ, as well as the corresponding half-size bound for real projections of quadratic prefixes. No floating-point result or external certificate is a premise.

This supplies the numerical Fresnel input to a general Kershner proof. It does not yet prove 1.343 for arbitrary nonconstant curvature. The general projection comparison and the full 2.686 B-process boundary accounting remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## General Kershner constant and boundary integrals proved

CurvatureProjection proves the general positive-curvature oscillatory integral estimate. An energy inequality compares each initial positive cosine segment with the actual quadratic Fresnel prefix; an integration-by-parts comparison makes the remaining tail nonpositive. Phase rotation, reflection and a split at the actual critical point give the full complex norm bound. KershnerBound converts this to 1.343/sqrt(ℓ) for exp(2πi(f(u)−νu)). The explicit curvature extension removes any global regularity requirement, and the source's decreasing derivative and absolute curvature lower bound discharge the signed hypothesis. No numerical bound or curvature comparison is assumed.

The actual finite-sum consumer proves that removing frequencies 0 and M costs at most 2.686/sqrt(ℓ), including M=0. This completes that boundary-integral estimate. The omitted stationary main term at M and the unrestricted logarithmic deduction remain separate OPEN obligations under DKQH-11; the full B-process is not yet proved. Earlier statements that the arbitrary-curvature Kershner input is missing are superseded by these proofs. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## One-sided curvature and complete stationary frequency sum

KershnerHalf proves 0.6715/sqrt(ℓ) when the shifted derivative has one sign, derives this for the actual zero frequency from the source hypotheses, and tightens the two-boundary-integral cost to 2.0145/sqrt(ℓ). StationaryCapped combines the one-sided curvature bound with the reciprocal derivative bound. Each endpoint contributes 0.6715/sqrt(ℓ) at zero gap, and the minimum of that bound and 1/(π|gap|) otherwise. The stationary replacement now covers closed-interval critical points, including both endpoints and zero third-derivative scale.

StationaryFullSum constructs the actual full positive stationary family and compares all Fourier frequencies 0 through floor(f′(a)) with all stationary terms 1 through floor(f′(a)), retaining −1/8 and the exact curvature amplitude. The finite endpoint caps and the actual frequency count remain explicit. This is a proved intermediate bound, not an adopted replacement for Corollary 0.2: reducing those terms to the paper's exact nonlinear coefficient, logarithm and 2.686 remains OPEN under DKQH-11. The original source-proof diagnostics remain preserved. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Uniform errors for half stationary terms

AngularGeometry proves that a positive-curvature phase starting at zero with nonnegative slope has a nonnegative sine integral. It also bounds its cosine integral below by −1/sqrt(πℓ) in angular normalization. The initial positive trigonometric segment is retained before applying the tail bound; these coordinate estimates and the proved Fresnel norm bound give a kernel-checked geometric estimate.

StationaryUniform translates that geometry to the actual source phase: each one-sided integral differs from its half stationary main term by at most 0.928/sqrt(ℓ). Reflection, phase rotation, conjugation and the explicit curvature extension are proved bridges. Combining both sides gives 1.856/sqrt(ℓ) for the actual integral minus its full stationary main term, including endpoint critical points. No third-derivative estimate is required for this uniform bound. These bounds provide new inputs for the still-OPEN exact B-process aggregation; they do not change the source contract or close DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Exact one-sided nonlinear stationary estimates

StationaryHalf proves the integration-by-parts perturbation bound Dδ²/(2|κ|) for the actual positive half window, then combines the actual phase factorization with its sharp half Fresnel tail. HalfStationary extends only the needed endpoint and optimizes the radius, proving exactly half of the nonlinear coefficient plus one finite endpoint cap. The original closed-interval source derivatives supply the curvature extension, including D=0; reflection proves the other side.

StationaryEdges combines these analytic estimates with the actual 0.928 uniform half-main bounds. For either endpoint frequency, the actual full integral minus its full stationary main term is bounded by half the nonlinear coefficient, 0.928/sqrt(ℓ), and only the far-end derivative cap. This supplies the endpoint-frequency inputs to the new aggregation argument while preserving every stationary main term. The complete source logarithmic/error aggregation and discrete B-process remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Complete stationary error aggregation — 5 October 2026

StationaryLogCaps proves the far-end cap sum on the full source range f′(b)<1 and the short-width logarithmic absorption. BProcessIntegrals uses the two half nonlinear edge estimates, counts them as one full error, and retains every stationary main term through floor(f′(a)). It proves the actual Fourier sum over 0 through floor(f′(a)) minus the full stationary sum over 1 through floor(f′(a)), with exactly 2.686/sqrt(λ₂), the printed nonlinear coefficient, 2/pi·log(f′(a)−f′(b)) and 1.251. The zero- and one-frequency cases, zero third-derivative scale, critical endpoint, half-integer length and λ₃/h₃ factorization are included. The source derivative hypotheses construct the stationary family; no stationary estimate is assumed.

This completes the Fourier-to-stationary portion of Corollary 0.2 without changing its constants or restricting f′(b) to at most 1/2. The earlier false reciprocal intermediate and omitted-main-term diagnostics remain valid, but this proof bypasses them. The discrete Poisson transfer, its missing regularity premises and the separate Corollary 0.1 source discrepancies remain OPEN under DKQH-10/11. No pending source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Actual discrete B-process adapters — 5 October 2026

BProcessPoisson combines the complete stationary transform with each proved Poisson theorem. exists_b_process_partI gives the actual discrete exponential sum minus the full stationary dual sum under the source phase assumptions, with the accepted Part-I logarithmic/digamma error. exists_b_process_partII gives the actual same transformation with the proved second-order coefficients, conditional on the provisional SecondOrderRegularity hypotheses and δ≥1/2. Its finite-head coefficient remains (log(2)+1/f′(a))/pi and its square/cube coefficients remain the separately proved sums. These are explicit alternatives, not an adoption of the smaller printed Corollary 0.2 remainder.

The quadratic review phase is now proved not to satisfy SecondOrderRegularity: its positive curvature quotient increases between the two endpoints. Thus the source B-process assumptions cannot be silently fed into that provisional Part-II adapter. DKQH-10/11 and the existing scope decisions remain OPEN. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Corollary 0.1 Part-II counterexample and full-δ repair — 5 October 2026

PoissonHalfReview now refutes the entire printed Corollary 0.1 Part-II bound. Put v=u−1/2 and f(u)=u−v/1000−v²/(2·10⁹)+v³/(6·10¹⁰) on [1/2,11/2]. This is C³; f′ is positive and strictly decreasing; |f″| is positive and strictly decreasing. Its upper derivative is 999/1000, its lower derivative is 799199997/800000000, and δ=1/1000. The five actual integer samples have sum within 1/4 of 5, while the sole retained Fourier integral has norm at most 1/2. Thus the actual remainder is greater than 4. The literal printed bound, including the cited half-integer B formula and both printed E coefficients, is less than 3. Every inequality and endpoint convention is kernel checked; this is a counterexample to the full stated corollary, not merely an intermediate estimate. It does not refute Corollary 0.2, whose additional stationary error remains separate.

PoissonHalfDelta proves a proposed domain-preserving repair. For d=M+1−y>0 its half-integer endpoint factor is

`Bδ(M,y) = (|Re ψ(d) − Re ψ((d+1)/2) − log(2)| + 1/(M+1) + log(2) + 3/(2(y+1))) / y`.

The actual endpoint tails, full weighted Poisson bound, every permitted lower-frequency shift, constant-weight specialization and actual discrete B-process adapter are proved with this explicit factor for all positive d. The factor is bounded by the printed π/2 simplification when d≥1/2. These results retain the full finite-head coefficient (log(2)+1/f′(a))/pi in constant weight, the separately proved square/cube coefficients, and the provisional SecondOrderRegularity inputs. Adopting this changed Corollary 0.1 contract remains a separate owner decision; the already-pending general Part-II quotient and E₁ decisions are not silently adopted. The earlier statement that no complete Corollary 0.1 counterexample exists is superseded. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Actual logarithmic B-process application — 5 October 2026

LogBProcess discharges every extra second-order condition for f(u)=c·log(u) by consuming the existing AFE regularity theorem at σ=0. It proves the third derivative and the interval scales λ₂=c/b², h₂=b²/a² and |f‴|≤2c/a³. The actual discrete transformation has explicit stationary points c/ν, amplitude sqrt(c)/ν and phase c·log(c/ν)−c−1/8. Its error uses the proved full-δ endpoint factor; no regularity record, stationary estimate or Poisson error is assumed in this public application. This does not adopt the pending general source repairs or claim the smaller printed remainder.

StationarySharpSum also retains the numerical margin in the many-frequency argument: 2.5275/sqrt(λ₂) and the harmonic constant 2/pi replace the coarser 2.686/sqrt(λ₂) and 1.251 in that explicit subcase. These proved margins are available for checking the remaining source error terms. DKQH-11 remains OPEN for the full unchanged source domain. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Literal B-process constants for a logarithmic subdomain — 5 October 2026

LogBSource proves logarithmic_b_process_printed for f(u)=c·log(u), positive half-integer endpoints a<b, c>0, c/b<1, c/a≥2 and δ≥1/2. The conclusion contains the actual discrete sum, explicit full stationary dual sum, phase −1/8, and the literal printed B-process error: 2.686, 1.251, the printed E₁, unchanged E₂, printed half-integer B factor and the smaller finite-head terms. Every analytic condition is discharged for this actual phase.

The proof uses the sharper stationary constants and proves that their margin absorbs both the E₁ sign discrepancy and the finite-head discrepancy when the endpoint curvature is at most twice the upper derivative. Positive half-integer a implies a≥1/2, so c/a²≤2(c/a). No source repair is adopted to obtain this restricted literal theorem. The lower-frequency, δ<1/2 and general-phase source cases remain OPEN under DKQH-11. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Literal single-frequency logarithmic B-process — 5 October 2026

LogBOne proves logarithmic_b_process_printed_one with the same actual discrete/dual sums and every printed B-process constant for floor(c/a)=1 and δ≥1/2. The full stationary sum has a proved spare 2/3 budget; this absorbs the printed finite-head and E₁ discrepancies. The proof covers both small and large derivative width, and discharges every analytic condition for the actual logarithmic phase. Together with LogBSource, all c/a≥1 cases with δ≥1/2 are now proved. The zero-frequency, δ<1/2 and general-phase cases remain OPEN under DKQH-11; no pending source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Literal logarithmic B-process for every frequency count — 5 October 2026

LogBZero proves logarithmic_b_process_printed_half for every positive c, positive half-integer a<b, c/b<1 and δ≥1/2, with no restriction on floor(c/a). Its actual sum, explicit stationary dual sum, phase −1/8 and every printed remainder constant are unchanged. The zero-frequency case reuses node 71’s kusminLandau_one_period_decreasing with a proved logarithmic-increment normalization and integer-interval reindexing. The resulting bound 2/sqrt(c/b²) is dominated by the printed stationary error; the combined printed E₁/E₂ coefficient is proved nonnegative on that subcase. The public theorem joins the zero-, one- and many-frequency proofs.

This supersedes earlier missing lower-frequency statements for logarithmic phases. The δ<1/2 logarithmic range and the full general-phase Corollary 0.2 contract remain OPEN under DKQH-11. No pending source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Full positive-gap zero-frequency logarithmic source bound — 5 October 2026

LogBZeroFull proves logarithmic_b_process_printed_zero_full for floor(c/a)=0 on the entire positive δ range. It preserves every printed B-process constant and coefficient. An exact logarithmic increment adapter applies node 71’s Kusmin–Landau theorem with the smaller of the lower-derivative gap and 1−c/a. The actual sum is bounded by max(2b/c,1/(1−c/a)). A kernel-checked cubic inequality shows that the curvature term and the printed cubic singularity absorb the latter term; the combined printed E₁/E₂ coefficient is bounded below by 1/δ³. All normalization, interval reindexing and positivity conditions are proved.

The logarithmic source theorem is therefore proved whenever floor(c/a)=0 or δ≥1/2. Only positive-frequency δ<1/2 cases and the general-phase contract remain OPEN under DKQH-11. No pending Poisson/source correction is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Shifted upper cutoff and capped nearby frequency — 5 October 2026

PoissonCutoff extends the accepted Part-I bound to every positive upper cutoff M with f′(a)<M+1. Its constant-weight consumer uses the actual sum and all Fourier integrals. Moving the cutoff from floor(f′(a)) to one frequency higher isolates the nearby omitted integral, bounded by min(0.6715/sqrt(λ₂),1/(πδ)); the remaining digamma argument is 1+δ. The general-phase many-frequency B-process consumer exists_b_process_next_cutoff combines this estimate with the full stationary transform under ordinary source differentiability, decreasing positive slope and curvature bounds. It requires no provisional second-order quotient hypotheses.

This is an alternative explicit error, with a capped endpoint contribution, not a proof of the smaller printed full remainder. Comparing that error with the literal source remains OPEN under DKQH-11; the proved logarithmic domain remains floor(c/a)=0 or δ≥1/2. No pending source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Full positive-gap many-frequency logarithmic source bound — 5 October 2026

LogBGapBudget proves logarithmic_b_process_printed_small_gap by applying the general shifted-cutoff transform to the actual logarithmic phase and proving that its error is absorbed by the literal printed remainder. A rational cubic certificate controls the unused 0.1585 curvature margin, and an analytic bound log(β+2)≤0.74sqrt(β)+0.35 holds on the full β≥5/2 interval. The exact E₁/E₂ cancellation retains the cubic singularity with a rational loss at most 1/72. The source B and finite-head constants are kept explicitly throughout the comparison.

logarithmic_b_process_printed_many_full combines that proof with the earlier half-offset result: all δ are covered whenever c/a≥2. The zero-frequency full-δ case remains proved. The only remaining logarithmic subcase is floor(c/a)=1 with δ<1/2; the full general-phase Corollary 0.2 also remains OPEN under DKQH-11. No source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Complete literal logarithmic B-process specialization — 5 October 2026

LogBOneFull proves logarithmic_b_process_printed_full for all c>0, positive half-integer a<b and c/b<1, with every frequency count and every positive endpoint gap. The conclusion contains the actual integer sum, the explicit stationary dual sum with amplitude sqrt(c)/ν and phase c·log(c/ν)−c−1/8, and every literal printed coefficient: 2.686, 1.251, E₁, E₂, the half-integer B terms, the logarithmic loss and the smaller finite-head terms. No extra regularity record, Poisson bound, stationary family or gap restriction is supplied as a hypothesis.

The last single-frequency small-gap case uses a sharper 1.5995 stationary curvature coefficient, a proved half nonlinear contribution, the enlarged-cutoff Poisson estimate and rational absorption of its error. The final theorem explicitly joins zero, one and many stationary frequencies. This supersedes all earlier missing logarithmic-domain clauses. DKQH-11 remains OPEN for arbitrary phases; this is the full logarithmic specialization, not the full general Corollary 0.2. No pending source repair is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## General-phase exterior frequency with half reciprocal loss — 5 October 2026

ExteriorPhase proves that the clamped curvature extension is exactly quadratic before the left endpoint. A virtual stationary point in that actual extension gives a finite nonstationary integral bound with half the nonlinear stationary coefficient, the far endpoint cap, and 1/(2π(ν−f′(a))). Both artificial stationary main terms cancel in the proof; the extension is proved equal to the original phase on the source interval.

StationarySharpSum now exposes the exact (floor(f′(a))−1) nonlinear error count; its earlier public bound consumes this stronger estimate. ExteriorBProcess uses the available half-error margin when δ≤1/2, combines the exterior frequency with every stationary main term, and applies the accepted constant-weight Poisson estimate at the enlarged cutoff. The public exists_b_process_half_gap proves the actual general-phase discrete transformation with endpoint term 1/(2πδ), without any extra curvature-monotonicity hypothesis. Its shifted-digamma Poisson error remains explicit and has not yet been absorbed into the literal source remainder. DKQH-11 and all pending source decisions remain OPEN. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Literal B-process for arbitrary phases below upper derivative two — 5 October 2026

GeneralBSmall proves exists_source_b_process_small with every literal printed B-process constant for arbitrary source phases satisfying f′(a)<2. Both zero and one stationary frequencies, every positive δ, actual half-integer sums, the full stationary main term, phase −1/8 and the source h₃/λ₃ factorization are included. No extra curvature-monotonicity or second-order regularity record is assumed. The combined printed E₁/E₂ coefficient is proved nonnegative for every positive upper derivative.

The zero-frequency proof moves the accepted Part-I cutoff to one and bounds both actual integrals. The one-frequency proof uses the original cutoff for δ≥1/2 and the cutoff at two for δ≤1/2, with rigorous curvature and endpoint budgets. The actual source remainder absorbs these costs without a repair. The full logarithmic specialization remains proved at every upper derivative. Only arbitrary phases with f′(a)≥2 remain in the general Corollary 0.2 comparison; DKQH-11 is still OPEN, and no pending source decision is adopted. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.

## Tighter nonlinear stationary coefficient — 5 October 2026

TightStationary chooses four fifths of the earlier window radius. The exact rational identity (4/5)²+5/4=1.89 improves the nonlinear coefficient 2·3^(2/3)/π^(2/3) to 1.89·3^(2/3)/π^(2/3). Both half integrals, both edge estimates, the complete stationary sum and the actual enlarged-cutoff discrete B-process consume this improved estimate, including D=0. The earlier public source contracts remain unchanged.

This releases 5.5 percent of the printed nonlinear allowance for the remaining general-phase Poisson comparison. The shifted-digamma error remains explicit in exists_b_process_next_tight; this improved transform does not by itself prove the full printed many-frequency remainder. The arbitrary-phase range f′(a)<2 and the complete logarithmic specialization remain proved, while DKQH-11 and pending source decisions remain OPEN. Current scope: 181 retained files, 115 production and two verification modules, 226 semantic consumers; 8/20 gates complete.


## Bounded-third-derivative Fourier error — 5 October 2026

OscillatoryC3 proves two integrations by parts with an integrable, possibly discontinuous third derivative. The curvature-square integral reduces to endpoint reciprocals using only nonpositive bounded curvature. Its public norm_expMode_cubic bounds the actual 2π-normalized integral minus its complex first boundary term by (2κ+D(b−a))/(4π²ρ³), for either derivative sign separated from zero by ρ. No curvature-quotient monotonicity premise is introduced.

This supplies the nonstationary mode estimate for the remaining arbitrary-phase Poisson comparison. Infinite-tail assembly and the complete printed many-frequency comparison remain OPEN under DKQH-11. No pending source decision is adopted. Current scope: 182 retained files, 116 production and two verification modules, 231 semantic consumers; 8/20 gates complete. Verification receipts remain separately scoped in the Reproduction Manifest.


## Cubic estimates for the actual Poisson coefficients — 5 October 2026

CubicCoefficients connects the bounded-third-derivative estimate to the actual constant-weight positive and negative Poisson coefficients. The elementary first endpoint and the wave-integral boundary combine to exactly 2π times the existing secondModeEndpoint or upperModeEndpoint. The residual has denominator (n+1+f′(b))³ on the positive side and (n+M+1−f′(a))³ above the cutoff. All sign, frequency and complex normalization identities are proved.

These mode estimates preserve the existing absolutely convergent endpoint tails without using provisional Part-II quotient hypotheses. Their infinite summation and the final printed B-process comparison remain OPEN under DKQH-11. Current scope: 183 retained files, 117 production and two verification modules, 235 semantic consumers; 8/20 gates complete. No pending source decision is adopted.


## Complete cubic Poisson estimate and separated positive frequency — 5 October 2026

CubicPoisson sums the actual cubic coefficient errors and preserves both endpoint tails. constant_poisson_cubic proves the actual half-integer discrete Poisson bound with explicit reciprocal envelopes, for every positive cutoff M whose derivative gap is at least 1/2. The constant error is (log(2)+1/M)/π+1/2+log(2)/π; its curvature/length coefficient is (2κ+D(b−a))/(4π²). The remaining factors are explicit reciprocal cubes and squares at the two derivative gaps. This closes the infinite-tail assembly for this alternative error without introducing logarithmic growth in f′(a).

CubicPositive separately bounds the actual first positive coefficient by 1/π and the remaining endpoint tail by 1/(8π²) at each endpoint. Its positive_tail_cubic_split bounds the full positive coefficient series by 3/(2π) plus the cubic error series starting at 2+f′(b). This lowers the curvature coefficient needed in the remaining printed-error comparison. All source derivative and half-integer hypotheses are explicit; no provisional Part-II quotient condition is used. The literal general many-frequency B-process comparison remains OPEN under DKQH-11. Current scope: 185 retained files, 119 production and two verification modules, 242 semantic consumers; 8/20 gates complete. No pending source decision is adopted.


## Hybrid transform and printed error allowances — 5 October 2026

CubicHybrid proves constant_poisson_cubic_split for the actual finite sum, with both cubic tails and the separated first positive frequency. Its stationary_sum_next_hybrid includes every original stationary main term and the exterior frequency for every source gap, with nonlinear coefficient 1.94 and endpoint cost 1/π+1/(2πδ). The proof combines the tighter stationary count with the actual exterior integral and handles both gap ranges.

CubicBudget proves that the literal combined E₁/E₂ coefficient retains at least 25/(36δ³) after the two far cubic tails. A rational cubic certificate combines this margin with 0.1585/sqrt(λ₂) to cover 1/(2πδ). The exact printed non-curvature remainder covers the finite head and remaining constants. For 0≤D≤1, the remaining length error fits six hundredths of the nonlinear source coefficient. These are proved assembly inputs; an actual discrete consumer and the larger-D range remain OPEN under DKQH-11. Current scope: 187 retained files, 121 production and two verification modules, 249 semantic consumers; 8/20 gates complete. No pending source decision is adopted.


## Literal B-process for bounded third derivative — 5 October 2026

BProcessCubic proves exists_source_b_process_small_D for arbitrary source phases whenever h₃λ₃≤1. The theorem includes every frequency count and every positive δ, the actual half-integer discrete sum, the full stationary dual sum, phase −1/8, source scale factorization and all literal printed constants 2.686, 1.251, B, E₁ and E₂. The many-frequency proof consumes the new cubic Poisson bound, hybrid stationary transform and exact error budgets; the public all-frequency theorem joins the earlier zero/one-frequency cases. No extra curvature monotonicity, quotient condition or assumed remainder is used.

This closes the discrete consumer for that explicit subdomain. The complete logarithmic specialization and arbitrary phases with f′(a)<2 remain proved independently. DKQH-11 now remains OPEN for arbitrary phases with f′(a)≥2 and h₃λ₃>1; this restricted theorem is not presented as the entire general Corollary 0.2. Current scope: 188 retained files, 122 production and two verification modules, 252 semantic consumers; 8/20 gates complete. No pending source decision is adopted.


## Enlarged bounded-third-derivative B-process — 5 October 2026

CubicFour proves exists_source_b_process_four_D for arbitrary source phases with h₃λ₃≤4, every frequency count and every positive δ. It preserves the actual half-integer sum, the full stationary main term with phase −1/8, the source scales and every printed remainder constant. The proof splits δ at 9/20: the smaller gap retains stationary nonlinear coefficient 1.89 and spends 0.11 on the cubic tail; the complementary range uses 1.94 and 0.06. Rational root and summable-tail estimates justify both allocations inside Lean.

This supersedes the preceding restricted-domain status: DKQH-11 remains OPEN for arbitrary phases with f′(a)≥2 and h₃λ₃>4. The logarithmic specialization and all phases with f′(a)<2 remain independently proved. Current scope: 189 retained files, 123 production and two verification modules, 261 semantic consumers; 8/20 gates complete. No pending source repair is adopted.


## Complete general B-process implementation — 5 October 2026

BProcessGeneral proves exists_source_b_process_printed_full and source_b_process_printed, the literal Corollary 0.2 for every allowed source phase, frequency count and positive δ. The latter theorem covers any family of the unique stationary points. The actual half-integer discrete sum and full stationary sum retain phase −1/8, denominator sqrt(|f″|), source factors h₂,h₃,λ₂,λ₃ and every printed remainder term, including 2.686, 1.251, the logarithm and the literal B/E₁/E₂ coefficients. The scale domain is explicit: λ₂>0 and h₃,λ₃≥0; h₂≥1 and positive f′ throughout are derived.

The proof combines CubicFour for D=h₃λ₃≤4 with a new argument for D≥4. For upper slope at most 26, the actual finite sums are bounded directly using curvature and rational quadratic certificates. Above 26, LargeDBudget proves a digamma chord, a global logarithmic tangent bound, an exact Poisson-error comparison and a joint length/curvature bound. The nearest exterior Fourier mode is paid from the unused stationary allowance. No source-corollary remainder, quotient monotonicity or numerical optimizer certificate is assumed. This bypasses the diagnosed gaps in the printed proof without changing the printed conclusion or adopting any pending Part-II/Corollary-0.1 repair.

This supersedes all earlier restricted-domain B-process status reports. Implementation is complete; DKQH-11 acceptance is pending the current exhaustive audit and sequential verifiers. Current scope: 191 retained files, 125 production and two verification modules, 285 semantic consumers; 8/20 gates remain accepted until that verification finishes.


## DKQH-11 accepted — 5 October 2026

The complete literal Corollary 0.2 is verified in BProcessGeneral. Exact-type regressions preserve every source hypothesis, actual sum, phase, scale and constant; the stationary-point family is constructed and proved unique. The exhaustive audit checks 2349 project theorems, including generated/private declarations, with 1437 explicit consumers and only standard logical axioms. Both sequential BATs passed with zero Lean diagnostics. DKQH-11 is DONE, and 9/20 gates are accepted. The diagnosed errors in the printed proof remain preserved; the new proof establishes the unchanged conclusion. This supersedes every earlier B-process OPEN/restricted-domain status. Other source decisions remain pending.


## Object conventions and integration acceptance review — 5 October 2026

ObjectAdapters proves sharpZetaSum_eq_integer_source, afeRemainder_eq_integer_source, actual_wave_principal_power and integer_source_half_cutoff. These connect the actual integer-indexed source sums, their principal powers and both AFE polynomials directly to the implemented remainder. The unit term is included, the lower endpoint is open and the upper endpoint closed, and the cutoff transfer preserves the actual sum. Existing PoissonShift proves integer-sample phase invariance, the complete N-frequency reindexing and δ=1−fract(f′(a)); EulerMaclaurin proves arbitrary-endpoint and half-integer boundary identities. ChiReflection proves the correctly oriented functional equation, actual remainder reflection and both height signs. No numerical error bound is used to define a remainder.

The independent dependency review rehashed all 35 files in local_reuse_inventory.json, covering 407 recorded declarations, with zero mismatches. The selected root path dependency, Lean 4.30, Mathlib/PNT+ revisions and every inherited package match the frozen graph. Dependencies/README.md records the exact reused interfaces, minimal Fresnel adaptation, source hashes, available license notices and normalization changes. All 126 production modules are classified and imported; all public declarations and their complete axiom dependencies are covered. No upstream proof or package pin is changed.

DKQH-02 and DKQH-18 are ready for acceptance after the current 192-file verification finishes. Current scope: 192 retained files, 126 production modules, two verification modules, 290 semantic consumers; 9/20 gates are accepted. This review is separate from the unresolved Part-II, Corollary-0.1, AFE2 branch and table decisions.


## DKQH-02 and DKQH-18 accepted — 5 October 2026

The object-convention and dependency reviews above passed the 192-file sequential verification. DKQH-02 and DKQH-18 are DONE: all actual-source adapters have exact-type consumers and permitted transitive dependencies; all 126 production modules are classified and imported within the unchanged pinned foundation graph. The focused build, 13 isolated validator fixtures and both BATs passed with zero Lean diagnostics. The audit covers 2359 project theorems, 1447 explicit consumers and 290 semantic regressions; 16 linters checked 1611 declarations plus 895 generated declarations. Full receipts and hashes are in the Reproduction Manifest.

The accepted total is 11/20. DKQH-01, DKQH-09, DKQH-10, DKQH-14 through DKQH-17, DKQH-19 and DKQH-20 remain OPEN. The remaining source decisions concern the Part-II E₁ formula and quotient hypotheses, the Corollary-0.1 Part-II repair, the AFE2 branch assignment and outward Table 1–2 replacements. Their proved alternatives and preserved source diagnostics are recorded in Errata and Computation Review. The earlier Part-I approval does not adopt these separate changes; the final accepted-contract audit and whole-paper release follow those decisions. No pending repair, whole-paper completion or external acceptance is claimed.
