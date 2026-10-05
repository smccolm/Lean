# Frozen source and intended mathematical contract

**ACTIVE GOAL — activated 5 October 2026. 7/20 proof gates complete.** DKQH-03 through DKQH-05, DKQH-07, DKQH-08, DKQH-12 and DKQH-13 are complete; thirteen gates remain OPEN. Source review and the remaining analytic proofs are in progress.

The immutable edition remains arXiv:2609.00537v1. Original PDF, TeX, ancillary code and the 205-label index remain frozen. E05 now contradicts the literal Part-I scope; the owner accepted the additional monotonicity hypotheses in Errata on 5 October 2026. The corrected Part-I theorem is now complete for every allowed N and general/half-integer endpoints; Part II remains open.

## Objects and notation

Use Mathlib's actual `riemannZeta`, `Complex.Gamma` and `Complex.digamma`. For positive integer n, use principal complex powers with real-positive base; `e(u)=exp(2πiu)`. A source sum `a<n≤b` ranges over integers; a zeta partial sum uses positive integers and includes 1. Half-integer means `∃ k : ℤ, x=k+1/2`. The AFE assumptions force x,y positive. Every O* display means a literal absolute-value/norm inequality with coefficient one; it is not asymptotic notation.

Define the source χ factor as `χ(s)=2^s π^(s−1) Γ(1−s) sin(πs/2)`. Its valid functional equation is `ζ(s)=χ(s)ζ(1−s)` on the appropriate nonexceptional domain. The paper's reversed sentence in §2.5 is E02. At the AFE heights, `s≠1`; nevertheless prove all division and gamma-domain side conditions rather than relying on totalized operations.

The actual AFE2 remainder is

`E(σ,t,x,y) = ζ(σ+it) − Σ(1≤n≤x) n^(−σ−it) − χ(σ+it) Σ(1≤m≤y) m^(σ+it−1)`.

It must not be an arbitrary function supplied together with an assumed error bound.

## P8 — Theorem 8, weighted truncated Poisson

Primary label `thm-VDC`, PDF pp. 12–14. For `a<b`, positive continuous strictly decreasing f′, positive decreasing C¹ weight g, and integer `0≤N<f′(b)`, set `δ=1−(f′(a)−floor(f′(a)))` and

`R_N(a,b)=Σ(N≤ν≤floor(f′(a))) ∫[a,b] g(u)e(f(u)−νu) du`.

Prove `|Σ(a<n≤b) g(n)e(f(n))−R_N(a,b)|≤T_N(a,b)` with **every term** of `def-TNab` and its half-integer form `def-TNab-integer+1/2`. Part II adds the printed C² and derivative positivity/decrease assumptions and replaces the error by `def-TNab-partII` and `def-TNab-integer+1/2-partII`. Auxiliary `G`, `H`, `H_1`, `B`, `E_1`, `E_2` remain the actual source expressions, not free constants.

The source writes g(x) under a sum indexed by n: intended g(n) is E01. General-N phase shifting, the endpoint sawtooth convention, and the constant-weight non-strict boundary of the derivative assumptions must be resolved explicitly (E05–E06). Proving only N=0 or only half-integer endpoints is an incomplete P8.

## PB — Corollaries 0.1, 0.2 and 8.1

`cor-VDC` supplies the two g=1 half-integer bounds; `cor-thmVDC-partII` specializes δ=1/2. `Explicit_B_estimate` is the stationary dual-sum estimate with positive decreasing f′, `0<f′(b)<1`, three derivatives and the stated λ₂,h₂,λ₃,h₃ bounds. The phase is `f(xν)−νxν−1/8`, `f′(xν)=ν`, amplitude `|f″(xν)|^(−1/2)`. Keep `2.686/√λ₂`, the cubic-derivative term, `2/π log(f′(a)−f′(b))`, and the entire D_f expression including `1.251`. Implicit positivity of scale parameters needs an explicit valid formal domain.

## A1 — Theorem 9 and Corollary 0.3

`thm-AFE1`, PDF p.22. Intended positive-index contract, subject to E01:

`0<σ≤1`, `t≥t₀>0`, `c>1/(2π)`, `ct∈ℤ+1/2`, and

`|ζ(σ+it)−Σ(1≤n≤ct)n^(−σ−it)| ≤ m(c)(ct)^(−σ)`.

Let `u=1/(2πc)`. The exact source function is

`m(c)=c+(1+1/t₀)/π · (log(1+u)+γ−ψ(1−u)−1/[2(1+u)]−1/2)`.

The printed theorem excludes 1, whereas the proof includes it. Do not freeze that error as a required false goal. Review the proof's `x>1` restriction against the displayed general domain before closing A1 (E07).

For all real `t≥t₀≥14`, `cor:all_t` concludes the analogous sharp cutoff at t with `c₀ t^(−σ)`. With `N=floor(t₀)`, the exact `eq:def-c0` is the maximum of

`m((N+1/2)/t₀)`, `m((N+3/2)/(N+1))`, and `m(1−1/[2(N+1)])/(1−1/[2(N+1)])`.

Certify `c₀≤1.2552` at `t₀=14.13472` and `c₀≤1.2127` at `t₀=3·10^12`. The prose later says 14.13473; keep the advertised smaller threshold and prove it, or record a substantive correction. No hypothesis about verified zeta zeros is needed for either numerical parameter.

## A2 — Theorem 10, both error branches

`thm-AFE2`, PDF p.25: `1/2≤σ≤1`, `|t|≥t₀≥2π`, `x,y∈ℤ+1/2`, `x,y≥h≥3/2`, `2πxy=|t|`.

The proposed proof-consistent branch functions, **pending E03 resolution**, are

`E_direct(σ,h,t₀)=A₀(σ,h,t₀)+C₀(σ,t₀)B₀(σ,t₀)` and

`E_reflect(σ,h,t₀)=A₀(1−σ,h,t₀)C₀(σ,t₀)+B₀(1−σ,t₀)`.

For x≥y, the intended bound is

`|E|≤(log y/π+E_direct) (|t|/(2π))^(1/2−σ) y^(σ−1)`.

For x<y, it is

`|E|≤(C₀(σ,t₀)log x/π+E_reflect) x^(−σ)`.

The display `def-E0-all-x-y` reverses these E₀ assignments; the end of the proof and `AFE2.py` use the assignments above. Preserve the distinction. The source also writes signed t in fractional real powers while allowing negative t: use a proved positive-height reduction and conjugation bridge, not Lean's totalized real power of a negative base (E04).

Use **all** terms of `def-A0` (5.22), `def-B0` (5.23), `def-C0` (2.17), `eq:Ci` and `x₀=max(h,√(t₀/(2π)))`. These expressions are pinned by source hash and label, avoiding an error-prone second transcription of several multi-line formulas. Their actual definitions and equality bridges must appear in the later Lean contract.

## Numeric consequences and scope

`cor-AFE2` takes maxima over `σ∈[1/2,1]`; preserve dependence on h,t₀ and x/y branch. `cor-k-AFE2` has integer `1≤k≤50`, `h_k=floor(exp(k−1))+1/2`, `H_k=exp(k)` and `h_k≤min(x,y)≤H_k`. Its constants derive from `k/π+ε₀` or `k(1+δ₀)/π+ε₀` with the appropriate branch. Table 1, Tables 2–3, `eq:ek-largeK` and `eq:AFE2-simple` are finite certification obligations. Exact source decimals and thresholds are retained; a rounded-down approximation is not automatically a valid upper bound (E08).

The author script's k=51..150 output, improvements to Patel–Yang's final subconvexity constant, elimination of half-integer AFE2 cutoffs, elimination of all logarithmic loss, RH itself, new zero-density bounds and a full Simonič/Riemann–Siegel formalization are outside this contract. They may be separate extensions only after the stated outputs are complete and separately scoped.

## H1/H11 — exact harmonic and digamma consumers

The Lemma-1 contract uses the literal natural-number tails `ν>N` and `ν>0`, with δ=N+1−y derived from N and y. `SemanticRegression.lemma_one_first_tail`, `lemma_one_second_tail`, `lemma_one_third_tail`, `lemma_one_first_plus`, `lemma_one_second_plus` and `lemma_one_third_plus` retain every displayed coefficient, power and qₖ polynomial. All sums have proved convergence; reindexing is an equality, not an assumed convention. The negative-shift results extend to N=0, while containing the whole printed positive-integer N domain.

`SemanticRegression.lemma_eleven_negative` and `lemma_eleven_positive` consume the actual alternating series with their source signs, denominators and constants. `corrected_alternating_identity` retains the missing `-2 log 2`; `not_printed_alternating_plus_identity` proves the omitted-term identity false for every y>0. This local algebra repair leaves both advertised Lemma-11 inequalities unchanged.

`real_digamma_eq_deriv_Gamma_div` identifies the actual real Γ′/Γ with the complex digamma real part used in the bounds. Mathlib supplies Γ duplication and the special values at 1 and 1/2; audited consumers prove digamma duplication and the positive-axis recurrence. The real-series limit consumes pinned PNT+ `Complex.hasSum_digamma` and Mathlib’s harmonic/Euler-constant limit. Integral chord and telescoping comparisons provide the explicit bounds without numerical assumptions. These proofs do not consume or assume any Poisson/AFE remainder estimate.

## Implemented finite exponential-sum contract

The six lemma_two consumers in SemanticRegression contain the unfolded sums from def-Sxy. The geometric identity uses the integer floor; a proved noninteger-frequency adapter establishes the nonzero sine denominator. Both piecewise estimates include empty sums below one. Integer frequencies return the natural cutoff and its actual harmonic number. At k+1/2 the actual S₁ is the negative real alternating prefix, so its norm differs from log 2 by at most 1/y. The deterministic majorant selected for later Poisson use is log 2 + 1/y; the O-star expression is not treated as an unspecified real number. No unordered HasSum of the conditionally convergent alternating harmonic series is asserted: its ordered partial sums are proved to converge. The mixed reciprocal series used to identify the limit is absolutely convergent.

## Implemented oscillatory-tail contract

The seven lemma_three semantic consumers preserve the literal positive/tail natural-number indices, actual exp(-2πiνx), both mixed denominators, and the source domain 1≤y<N+1. The underlying generic proofs cover the stronger range 0<y<N+1. Integer frequencies are not passed to the sine-denominator formulas. The half-integer bounds use the exact real digamma difference, log 2, first omitted-frequency correction and coefficient 3/2; the comparison of the digamma majorant with π/2 is itself proved, not merely a weaker final norm inequality. The real digamma notation here denotes the already-proved real part of Complex.digamma = Γ′/Γ convention; no replacement special function is introduced. Both mixed series are absolutely convergent before any reindexing. These are Lemma 3 and Appendix A.4 conclusions; the source's optional split into conditionally convergent reciprocal tails is replaced by finite Abel summation on the actual absolutely convergent series.

## Corrected Poisson integral inputs

NonstationaryPhase directly consumes the completed foundation's nonstationary-phase theorem. It proves the actual shifted-phase derivatives and quotient monotonicity for both frequency tails, including the propagation of the accepted frequency-one quotient condition to every ν≥1. The actual derivative of g(x)exp(2πif(x)) is proved, and the two complete differentiated-amplitude integral bounds retain (|g′(a)|+2πg(a)f′(a))/(π|ν∓f′(a)|). Continuous-derivative hypotheses imply the C¹ condition used by the existing theorem. Nonnegative/zero amplitudes are allowed. Three explicit source consumers check the derivative and both bounds. This was the nonstationary-input checkpoint; the later N=0 assembly below supersedes its remaining-obligation list.

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

WeightedIntegrals defines the actual finite J(a,b,m), proves local integrability for Re(s)<1 and performs both integrations by parts including the zero endpoint. LowerIntegralEstimate sums these identities before taking norms and proves the complete first inequality of Lemma 5, preserving both height signs, the physical scale, both half-integer cutoffs and every printed constant. UpperIntegralEstimate proves conditional improper convergence and the complete second inequality of Lemma 5, with constant 2/π and log(y)+1. DKQH-06 remains OPEN for the remaining stationary-point and branch-phase obligations. The current inventory is 107 retained files, forty-one production modules and two verification modules; the accepted count remains 7/20. The last full sequential receipts cover the preceding 102-file Lemmas 4–5 checkpoint; the Reproduction Manifest records exact scope, paths and hashes.

WeightedIntegralPhase discharges the actual power/logarithmic-phase quotient monotonicity for both height signs, applies Lemma 4 on positive truncated intervals, and passes to zero by proved continuity of the integrable primitive. Its source-scale consumer bounds the literal integral of u^(2−s) exp(2πimu) by x^(2−σ)/(π(y−m)), deriving the cutoff condition from 2πxy=|t|. The complete first Lemma-5 sum is now proved in LowerIntegralEstimate and consumed literally by lemma_five_lower_sum_source. The complete upper-tail bound and convergence are now proved in UpperIntegralEstimate and checked by lemma_five_upper_sum_source.

Lemma 5 upper-tail source correspondence: J(N,∞,m) is defined as the limit of the actual finite interval integrals, and convergence is proved for 0<σ<1 and m>0. The source consumer states existence and the literal integral limit explicitly. The printed condition involving the bound index m is read as N>t/(πm) for every positive mode included in the sum; the convenient stronger uniform cutoff N>t/π is proved separately. N>0 is explicit, as required by the positive integration domain. The printed decreasing-quotient assertion need not hold for negative t; the proof instead bounds the actual unit-amplitude primitive for both signs and transfers that bound to u^(−σ) by integration by parts. No additional monotonicity assumption or change in the claimed inequality is used. The half-integer and physical-scale assumptions are unnecessary for this second bound. The finite first bound preserves them and every printed coefficient.

The minimal node-63 Fresnel adaptation now proves the actual symmetric quadratic-integral limit, its principal branch exp(−πi/4), and the quantitative finite-window error. StationaryPoints derives the unique point in the actual decreasing derivative range, proves the shifted phase derivative vanishes, identifies the logarithmic J-phase critical point and its height-sign restriction, and consumes the Fresnel limit to obtain exp(2πi(f(xν)−νxν−1/8))/sqrt(|f″(xν)|). Three independent source consumers check point selection, the finite-window estimate and the phase/amplitude limit. These prove the remaining mathematical interfaces of DKQH-06; acceptance awaits audit and sequential verification. DKQH-11 still requires the nonlinear replacement estimate and all printed B-process error constants. Attribution and exact source hashes are in Dependencies and local_reuse_inventory.json.
