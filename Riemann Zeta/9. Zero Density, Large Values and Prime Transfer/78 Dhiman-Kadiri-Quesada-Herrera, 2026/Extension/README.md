# Active isolated Lean extension

Activated 5 October 2026. The package is `DhimanKadiriQuesadaHerrera2026`, using the unchanged root Lean 4.30 and dependency graph through a local path dependency. Its external build directory avoids Windows path-length pressure.

`Objects` defines the actual sharp sums, source chi factor and AFE remainder. `SourceReview` proves source diagnostics. `PoissonCounterexample` proves that the original Part-I hypotheses do not imply its bound. `PowerWeights` proves the owner-approved additional monotonicity conditions for the actual AFE power weights and logarithmic phase, including σ = 0. `HarmonicDigamma` proves the nonalternating Lemma-1 estimates from the existing digamma series. `SemanticRegression` fixes their unfolded types, and `Audit` checks every imported project theorem transitively, including private/generated declarations, plus registered public consumers and default namespace linters.

DKQH-02/03/04/05/06/07/08/11/12/13/18 are complete: 11/20 accepted gates, with nine OPEN. Run the foundation and paper BATs sequentially. A helper proof or green development build does not establish the paper's analytic estimates.

AlternatingHarmonic proves Appendix Lemma 11, digamma duplication and the real Gamma logarithmic-derivative bridge. It retains the corrected intermediate identity and disproves the false printed one.

## Lemma 2 implementation checkpoint

FiniteExponentialSums now proves the actual geometric identity, both branches of the generic S₀ and tilde-S₁ bounds, the exact integer-frequency values, and the half-integer two-sided error with radius 1/y. Its finite Abel argument gives the stronger generic bound 1/|sin(πx)| and explicitly implies the printed bound. Six unfolded SemanticRegression consumers preserve the actual complex exponential, positive indices, floor, denominator and half-integer constant. DKQH-04 is DONE after the exact-source audit and sequential verifiers passed.

## Lemma 3 implementation checkpoint

ExponentialTails proves both actual oscillatory series absolutely convergent and establishes the generic Z₀/Z₁ bounds with the printed constants. The finite Abel bound is applied directly to the mixed reciprocal weights, avoiding separate unordered sums of conditionally convergent terms. At half-integers, exact complex-to-real adapters consume Lemma 11; differentiation of Mathlib's Gamma reflection formula and a proved monotone paired series give the explicit π/2 refinement for δ≥1/2. Seven unfolded source consumers and every public tail theorem are included in the passing focused audit (217 discovered theorems, 159 registered consumers, 16 linters, zero diagnostics). DKQH-05 is DONE after the sequential verifiers passed.

## Corrected Poisson integral inputs

NonstationaryPhase directly consumes the completed foundation's nonstationary-phase theorem. It proves the actual shifted-phase derivatives and quotient monotonicity for both frequency tails, including the propagation of the accepted frequency-one quotient condition to every ν≥1. The actual derivative of g(x)exp(2πif(x)) is proved, and the two complete differentiated-amplitude integral bounds retain (|g′(a)|+2πg(a)f′(a))/(π|ν∓f′(a)|). Continuous-derivative hypotheses imply the C¹ condition used by the existing theorem. Nonnegative/zero amplitudes are allowed. Three explicit source consumers check the derivative and both bounds. This was the nonstationary-input checkpoint; the later N=0 assembly below supersedes its remaining-obligation list.

## Corrected Part I at N = 0

AbelSawtooth proves the actual logarithmic Abel kernel, its paired Fourier expansion, uniform domination and the integral limit. PoissonFourier discharges absolute convergence of both integrated series from the accepted hypotheses and derives their explicit digamma/logarithmic bounds. EulerMaclaurin reuses pinned PNT+ and proves the integer translation needed for every real a≤b, with the literal (a,b] sum. PoissonPartI assembles the finite frequency integrations by parts and proves corrected_poisson_partI_zero, corrected_poisson_partI_zero_noninteger and corrected_poisson_partI_zero_half_integer. These preserve the actual weighted sum, Fourier main term, all N=0 logarithmic/digamma corrections, complex endpoint term and half-integer log(2) refinement. No Fourier identity, convergence result or remainder estimate is a supplied hypothesis. PartIRegularity contains only explicit differentiability, sign and monotonicity conditions, including the owner-approved repair.

The general-endpoint majorant uses the exact harmonic value at integer endpoints and the printed tilde-S₁ elsewhere; the actual complex boundary and its norm G are separate. These documented notation/domain repairs preserve the noninteger and half-integer formulas. Two unfolded source regressions and all public declarations are registered for the exhaustive audit. At the N=0 checkpoint the package had thirteen production modules and two verification modules, all imported and classified. That checkpoint left the fully shifted general-N statement and its final acceptance checks open; that historical checkpoint had 3/20 gates complete. Part II and all AFEs were still OPEN at that stage.

## Fully shifted Part I accepted implementation

PoissonShift proves the complete corrected Part I theorem for every natural N<f′(b). Its explicit hypothesis record is built from the printed strict phase monotonicity and positive weight together with the two owner-approved conditions; the core theorem also allows nonnegative weights. The proof transports every condition to f−Nx, proves equality at all integer samples (including negative integers), reindexes the actual Fourier range to N≤ν≤floor(f′(a)), and identifies δ=1−fract(f′(a)). The error uses floor(f′(a))−N consistently in both logarithmic and reciprocal terms, and its actual complex boundary uses the shifted phase. These are the fully shifted E06 corrections, not a claim that the derivative or general boundary is invariant.

Public endpoints are corrected_poisson_partI, corrected_poisson_partI_noninteger and corrected_poisson_partI_half_integer. Two unfolded general-N regressions complement the two N=0 consumers and preserve every constant and endpoint term. No result equivalent to a remainder bound is assumed. At the DKQH-08 checkpoint the inventory was 80 files, fourteen production modules and two verification modules. DKQH-08 was accepted after its exact-source review, focused audit and sequential foundation/paper BATs passed. That acceptance checkpoint had 4/20 gates complete.

The active package now also imports PoissonApplications, ZetaTruncation and AFEFirstKind. All seventeen production modules are classified; the two verification modules remain explicit targets. Theorem 9 has passed sequential acceptance checks.

AFEFirstMonotonicity and AFEFirstRealCutoff implement the exact analytic transfer. AFEDigammaNumerics and AFEFirstConstants provide the two advertised decimal certificates. At the AFE1 certification checkpoint the classification was twenty-one production modules and two verification modules; DKQH-13 is DONE after sequential verification; 6/20 gates are complete.

Current reflection/Lemma-7 development: 89 retained files, twenty-three production modules and two verification modules. Both new modules are classified and root-imported; 6/20 gates remain accepted.

The preceding digamma checkpoint had 90 retained files and twenty-four production modules; the later Lemma-6 section records the current inventory.

## DKQH-07 acceptance: full Lemmas 6–7 — 5 October 2026

GammaHorizontal proves the logarithmic Gamma derivative and explicit horizontal comparison on the closed real-part interval [0,1/2], including zero. GammaAnchors derives the exact norms at 0+it and 1/2+it from Gamma reflection, recurrence and conjugation. GammaStrip combines them with the proved digamma inequality to bound the actual Gamma modulus using the distance to the nearer endpoint.

ChiConstants defines the literal printed C₀–C₃, proves the exact factorization C₀=C₂(1+exp(−πt₀))(1+C₁/t₀), and proves uniform absorption of both exponential corrections. ChiBound.norm_chi_le_chiC0 concludes the source inequality for every 1/2≤σ≤1 and |t|≥t₀≥1/π. Its proof consumes the actual Gamma product and principal-power identity, preserves the height scale, and transfers negative heights by proved conjugation. SemanticRegression.lemma_six_source unfolds the chi product and all four printed formulas. No numerical sample, Stirling remainder assumption or additional source hypothesis is used.

The current inventory is 95 retained files, twenty-nine production modules and two verification modules. Every new production module is classified and root-imported; all public theorems are registered. DKQH-07 is DONE after exact-source review, exhaustive audit and sequential foundation/paper verification. The accepted total is 7/20. The Reproduction Manifest records both log paths and hashes. Part II, stationary phase and the AFE2 estimates remain open.

## Weighted-integral development after DKQH-07 acceptance

FirstDerivativeTest proves source Lemma 4 with constant 2, both monotonicity directions and the supremum over the actual interval. The decreasing case directly consumes the existing node-71 theorem through NonstationaryPhase; reflection proves the increasing case. The maximum is proved to occur at an endpoint. WeightedIntegralSums proves the exact finite quadratic/reciprocal bound with its 1/(8y²) correction and the weighted alternating boundary estimate. These have exact-source consumers and registered public declarations.

WeightedIntegrals defines the actual finite J(a,b,m), proves local integrability for Re(s)<1 and performs both integrations by parts including the zero endpoint. LowerIntegralEstimate sums these identities before taking norms and proves the complete first inequality of Lemma 5, preserving both height signs, the physical scale, both half-integer cutoffs and every printed constant. UpperIntegralEstimate proves conditional improper convergence and the complete second inequality of Lemma 5, with constant 2/π and log(y)+1. DKQH-06 is DONE after the stationary-point and phase proofs and their sequential verification. The current inventory is 181 retained files, ninety-seven production modules and two verification modules; the accepted count is 8/20. The last full sequential receipts cover the preceding 119-file finite-inequality checkpoint; the Reproduction Manifest records exact scope, paths and hashes.

WeightedIntegralPhase discharges the actual power/logarithmic-phase quotient monotonicity for both height signs, applies Lemma 4 on positive truncated intervals, and passes to zero by proved continuity of the integrable primitive. Its source-scale consumer bounds the literal integral of u^(2−s) exp(2πimu) by x^(2−σ)/(π(y−m)), deriving the cutoff condition from 2πxy=|t|. The complete first Lemma-5 sum is now proved in LowerIntegralEstimate and consumed literally by lemma_five_lower_sum_source. The complete upper-tail bound and convergence are now proved in UpperIntegralEstimate and checked by lemma_five_upper_sum_source.

The minimal node-63 Fresnel adaptation now proves the actual symmetric quadratic-integral limit, its principal branch exp(−πi/4), and the quantitative finite-window error. StationaryPoints derives the unique point in the actual decreasing derivative range, proves the shifted phase derivative vanishes, identifies the logarithmic J-phase critical point and its height-sign restriction, and consumes the Fresnel limit to obtain exp(2πi(f(xν)−νxν−1/8))/sqrt(|f″(xν)|). Three independent source consumers check point selection, the finite-window estimate and the phase/amplitude limit. These complete DKQH-06 after the exact-source checks, exhaustive audit and sequential foundation/paper verification. DKQH-11 still requires the nonlinear replacement estimate and all printed B-process error constants. Attribution and exact source hashes are in Dependencies and local_reuse_inventory.json.

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
