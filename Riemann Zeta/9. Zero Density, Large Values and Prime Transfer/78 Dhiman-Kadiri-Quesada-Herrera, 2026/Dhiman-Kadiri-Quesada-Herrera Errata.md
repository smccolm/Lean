# Source discrepancies, computation hazards and unresolved questions

Survey date: 5 October 2026. These are **local source-review findings**, not an author-issued erratum. No later edition or author correction was found. Preserve original source bytes and this evidence. SourceReview now contains the initial exact diagnostic regressions; the main Poisson and AFE results remain OPEN. Each item belongs to DKQH-01 and the downstream gates stated below.

| ID | Evidence in frozen v1 | Assessment / required resolution |
|---|---|---|
| E01 | `vanderCorputB` writes g(x) in the n-indexed sum. Theorem 9 (`thm-AFE1`, p.22) sums `1<n≤ct`; its proof starts `1≤n≤x`, as does Corollary 0.3. | Confirmed internal notation/index discrepancies. Use actual g(n); investigate and document inclusion of the missing unit term. The two sums differ by exactly 1 whenever ct≥1. A shrinking O(t^(−σ)) estimate for one is not the same theorem for the other. DKQH-02/08/12. |
| E02 | §2.5 before `def:chi` says `ζ(1−s)=χ(s)ζ(s)` with the standard χ(s). The introduction and reflected proof instead use `ζ(s)=χ(s)ζ(1−s)`. | Confirmed orientation inconsistency; the latter agrees with the defined gamma/sine factor. Prove the valid-domain Mathlib bridge; do not import the former sentence as a premise. DKQH-07/15. |
| E03 | Equation (5.2), label `def-E0-all-x-y`, assigns A₀(1−σ)C₀+B₀(1−σ) to x≥y and A₀(σ)+C₀B₀(σ) to x<y. `def-E0x>y`, the final reflected case, the adjacent remark and the script's call-site branches assign them the other way. | Confirmed statement/proof/code mismatch. Source Contract records the proof-consistent candidate, not an accepted proof of the printed (5.2). Re-derive both branches and preserve any counterexample if literal bounds fail. DKQH-14/15/16. |
| E04 | Theorem 10 and Corollaries 0.4–0.5 allow negative t using |t| in hypotheses, but write `(t/(2π))^(1/2−σ)` in bounds. Lemma 7 uses e^(−πt) and a fixed complex phase factor for a two-sign height domain. | Sign/branch issue. Establish positive-height formulas first and derive negative heights by conjugation with the correct phase, not literal substitution into fractional real powers. DKQH-02/07/15. |
| E05 | Theorem 8 Part II demands positive |g′| and g″, yet Corollary 0.1 sets g=1, making both zero. The generic Part-I statement controls |g′(a)| without explicitly stating a monotonicity bound for |g′|; proof uses derivative estimates. | Part I now has a kernel-checked polynomial-weight counterexample; see the activation review below. The owner accepted the additional monotonicity hypotheses. Audit exactly where monotonicity is needed; prove constant-weight case directly or a justified nonnegative extension. Do not assume strict positivity for zero derivatives. DKQH-08/09/10. |
| E06 | Remark after Theorem 8 says general N follows by f→f−Nx. Printed formulas mix f′(a), f′(a)−N and floor(f′(a)); H,H₁ contain phase derivatives. General endpoints enter G and Fourier sawtooth terms. | Quantitative and endpoint audit required. Track the shifted derivative in every auxiliary expression and the integer equality e(Nn)=1; validate all floor and δ terms. Do not declare N=0 alone to be full Theorem 8. DKQH-08/09. |
| E07 | AFE1 proof begins 1<x<M although theorem permits any positive half-integer ct. Corollary 0.3 advertises t₀=14.13472, whereas later proof/example text uses 14.13473. Reflected AFE2 at σ=1 uses a dual σ=0 endpoint. | Domain/threshold questions requiring genuine small-cutoff and endpoint arguments. No silent added x>1 or σ<1 restriction. Preserve the smaller advertised t₀ or label a correction. DKQH-12/13/15. |
| E08 | `AFE2.py`: `find_max` optimizes (0,1), while the theorem maximizes [1/2,1]; first t₀ is 6.2832, not exact 2π; floats are converted to Decimal; finite-difference/root logic does not globally certify maxima; six-place printing uses nearest rounding. At k=2 the unmodified output is 2.13226549 while Table 2 displays 2.132265. | Confirmed computational methodology/rounding gaps. The latter example shows a printed decimal is below the program's own approximate output; it does not by itself prove the mathematical inequality false. A replay is not outward certification. Prove global/endpoint coverage and use exact rational upper bounds. Preserve the published display and document any repaired constant. DKQH-13/16/17/19. |
| E09 | Corollary 0.2 uses λ₂,λ₃,h₂,h₃ without fully spelling out positive domains; comparison remark after Theorem 10 changes log variables/branches and writes approximate constants as displayed inequalities. The proof of the dual branch has further swapped-argument notation. | Audit against actual proof identities before encoding. Comparative or asymptotic prose cannot replace a rigorous uniform theorem. Record each concrete resolution and affected consumer. DKQH-11/14/15/17. |

Visual check: the archived PDF has 37 pages. Theorem 9 on printed p.22 and Theorem 10 on p.25 were rendered and inspected; the index and E₀ discrepancies occur in the PDF itself, not merely arXiv HTML extraction. TeX lines/labels give reproducible textual anchors.

## Change policy

For each resolution record the literal source, mathematical diagnosis, exact corrected statement (if any), why it is faithful, affected acceptance tests, and later kernel regression. Distinguish confirmed inconsistency from a conjectured repair and from a proved counterexample. Do not erase false source displays, copy node-63 repair claims, call an untested repair “author-approved,” or mark an affected gate DONE on the strength of a bibliography entry. No author contact is authorized by this setup.

## Activation review — 5 October 2026

The arXiv history and both author pages were rechecked on activation; only v1 is listed and the work remains listed as a preprint/current research. The frozen source ledger passes. Rendered PDF pages 12, 22 and 25 agree with the TeX on the orientation, missing summand and swapped branches.

E01 now has exact Lean diagnostics in `SourceReview`: the two actual finite sums differ by one whenever the cutoff is at least one. Consequently, bounds on both actual zeta residuals must have sum at least one. This justifies preserving the inclusive sum as the intended object; it does not prove the corrected AFE estimate.

E02 has a kernel-checked counterexample at `s=-2`: the printed right side is zero because `zeta(-2)=0`, whereas its left side is `zeta(3)`, which is nonzero. The source sentence is false even away from poles. The corrected orientation is now proved for every nonreal s by zeta_eq_chi_mul_zeta_one_sub; the original counterexample remains preserved.

### E05: analytic counterexample to Part I with its printed hypotheses

This counterexample is now kernel-checked in `PoissonCounterexample.lean`, including the literal integer/frequency indices, all endpoint terms, smoothness and monotonicity hypotheses, digamma bound and strict violation of the printed inequality. It uses the intended summand `g(n)`; fixing the obvious `g(x)` typo does not repair this issue.

Set `a=1/2`, `b=3/2`, `N=0`, `epsilon=1/10000`, `u=x-1/2`,

`g(x)=101/100-u^3`, and `f(x)=epsilon*(u-u^2/4)`.

Both functions are smooth. On `[a,b]`, `g` is positive and strictly decreasing, with `g(a)=101/100`, `g(b)=1/100`, and `g'(a)=0`. The derivative `f'(x)=epsilon*(1-u/2)` is positive, continuous and strictly decreasing, and `0=N<f'(b)=epsilon/2`. Thus the printed Part-I hypotheses hold. The frequency cutoff is zero, and `delta=1-epsilon`; the finite boundary sum is empty and `G(a,b)=0` because both endpoints are half-integers.

Let `S=g(1)*exp(2*pi*i*f(1))` and `R=integral_a^b g(x)*exp(2*pi*i*f(x)) dx`. The zero-phase discrepancy is exactly

`g(1)-integral_a^b g(x) dx = 1/8`.

The elementary inequality `|exp(i*v)-1|<=|v|`, together with `0<=f(x)<=epsilon`, `0<g(x)<=101/100`, the unit interval length and `pi<4`, gives

`|(S-R)-1/8| < 16*(101/100)*epsilon = 101/62500`.

Hence `|S-R| > 1/8-101/62500 > 3/25`.

The general-endpoint bound (3.2), specialized to these half-integer endpoints using its actual empty boundary sum, is

`T=(101/100)/pi * (log(1+epsilon)+gamma-psi(1-epsilon)-1/2-1/(2*(1+epsilon)))`.

The convergent digamma series gives

`-psi(1-epsilon)=gamma+sum_{n>=1} epsilon/(n*(n-epsilon)) <= gamma+2*epsilon/(1-epsilon)`.

Here `sum_{n>=1} 1/n^2<=2` follows from the integral comparison, and `n-epsilon >= (1-epsilon)*n`. Using `gamma<2/3`, `log(1+epsilon)<epsilon`, and `1/(1+epsilon)>1-epsilon`, the parenthesis is less than

`1/3+3/20000+2/9999 < 17/50`.

Since `pi>3`, this proves `T<1717/15000<3/25`, contradicting `|S-R|<=T`. This argument uses rational inequalities and standard analytic identities, not optimizer output. A separate high-precision numerical evaluation may cross-check it but is not its justification. The coarser special-endpoint display does not rescue the simultaneously asserted sharper general bound.

The proof's failing step is explicit: its estimate for `I_{g'}(-nu)` uses only `|g'(a)|`, which vanishes in this example even though `g'` does not vanish inside the interval. The claimed monotonicity of the derivative quotient is not implied by Part I.

### Owner-accepted material Part-I repair — 5 October 2026

Retain the intended `g(n)` sum and the same error expression, but add that `|g'|` and `|g'|/(1+f'-N)` are nonincreasing. Use the fully shifted phase `f-N*x` throughout the formula and proof (E06). These conditions supply the missing derivative-quotient monotonicity for both frequency tails. Nonnegative/zero amplitudes require the corresponding limiting or direct integral argument; strict positivity must not exclude constant weights.

The owner explicitly accepted these additional hypotheses on 5 October 2026. They change the general theorem's scope. They are satisfied by the intended AFE weights `g(x)=x^(-sigma)` and logarithmic phase for `sigma>=0` on positive intervals: for `N=0`, the relevant quotient is a constant times `x^(-sigma)/(x+t/(2*pi))`. The actual AFE power weights now satisfy both added hypotheses by `afe_weights_satisfy_accepted_partI_hypotheses` in PowerWeights, including sigma=0. The weighted-Poisson and AFE estimates themselves remain proof obligations. This accepted repair is not recorded as an unchanged or completed Theorem 8, and it does not settle Part II or any other source discrepancy.

### E09: additional local algebra and Fourier discrepancies

The Appendix A.2 derivation following `alt_second_sum` drops `-2 log 2`. Subtracting the preceding displayed identities gives, for y > 0, the alternating mixed sum `(ψ(y+1) - ψ((y+1)/2) - 2 log 2)/y`, not the printed expression without the logarithmic term. At y=1 the intended value is `1 - 2 log 2`, whereas the printed digamma expression is 1. The advertised absolute upper bound will be checked independently using the corrected identity; no changed constant is assumed. This is a local algebra correction within DKQH-03.

The half-integer S₁ proof substitutes `+log 2` for the alternating harmonic series with first term -1; the series is `-log 2`. Its norm estimate can still follow after correcting the sign. In `fourier`, the sine expression has the wrong sign for the displayed negative sawtooth, and the exponential expression omits `1/ν`; the exponential difference with `1/(2πiν)` has the required sign away from integers. Integer values and convergence under the integral require their own proofs. Frozen source bytes remain unchanged; these observations do not certify the Poisson theorem.

The omitted `-2 log 2` diagnosis is now kernel-checked for every y>0 by `not_printed_alternating_plus_identity`. The corrected identity and both literal Lemma-11 bounds are proved with unchanged constants in `AlternatingHarmonic`; their exact-index consumers appear in SemanticRegression. This resolves the harmonic-series portion of E09, while its other proof/branch issues remain open.

The prose preceding Lemma 2 also cites S₁(x,y) ≤ log(1+|y|), although S₁ is complex. Even interpreted as a norm bound this fails: x=1/2, y=1 gives S₁=-1, hence norm 1 > log 2. FiniteExponentialSums.not_prose_log_bound proves this exact counterexample. It does not affect the actual bounds stated in Lemma 2. The half-integer sign repair is implemented through the actual alternating prefix and yields the unchanged two-sided norm error.

### Poisson assembly notation and integer endpoints (5 October 2026)

The display eqn-exp uses G(a,b) as a complex summand after bigO1 defines it as a nonnegative norm. The formal identity retains the actual complex boundary, and only the inequality replaces it by its norm. This is the algebraic correction dictated by the preceding Euler–Maclaurin display.

Lemma 2 defines its sine-denominator majorant for noninteger x, while Theorem 8 allows general real endpoints. At an integer endpoint the exact finite harmonic sum is used, as already proved by finiteS1_integer; division by sin(πx)=0 in Lean is not a valid bound. The completed endpoint convention uses that harmonic value at integers and the unchanged tilde-S₁ expression elsewhere. The unchanged noninteger formula and half-integer specialization remain separate public obligations. These endpoint/notation repairs do not add analytic hypotheses or alter the owner-approved monotonicity repair.

E06 Part-I implementation now proves the fully shifted formula: every occurrence of the upper relative frequency is floor(f′(a))−N; δ remains 1−fract(f′(a)); the endpoint norm is computed using f−Nx. The exact integer sample equality and finite-frequency bijection are proved, so the original source sum and main Fourier range remain unchanged. No claim of general-endpoint G invariance is made. Part-II H/H₁/B/E terms remain open.

## Theorem 9 source correspondence — 5 October 2026

The source-intended n≥1 correction in E01 is now implemented by afe_first_kind, preserving the frozen printed n>1 statement and its exact omitted-unit diagnostic. Its real Γ′/Γ constant is identified by afeFirstConstant_eq_source and fully unfolded in SemanticRegression.theorem_nine_source. No stronger truncation conclusion is assumed: corrected Part I is applied to the actual weights, the inherited Euler–Maclaurin identity yields the regularized-sum limit, and the pole term is bounded separately.

The E07 AFE1 small-cutoff question is resolved by a proof on every a>0 and by afe_first_kind_small_cutoff at ct=1/2. The printed proof's x>1 restriction is unnecessary and is not added to the theorem. E07 remains open for the real-cutoff decimal threshold and the dual AFE2 σ=0 endpoint. This implementation does not settle those independent obligations.

The E07 Corollary-0.3 threshold discrepancy is now resolved at the smaller advertised 14.13472, with unchanged 1.2552. The 3·10^12 instance has a separate unchanged 1.2127 certificate. The AFE1 portion of E08 is covered by complete analytic monotonicity and kernel-checked rational certificates, independently of the ancillary program. E07/E08 remain open for their AFE2 endpoint and table obligations.

### E02/E04: exact chi reflection and signed-height Gamma factor

ChiReflection proves the valid functional equation ζ(s)=χ(s)ζ(1−s), χ(s)χ(1−s)=1 for every nonreal s, conjugation of the literal chi product and sharp sums, the exact reflected remainder with exchanged x/y, and equality of remainder norms at both height signs. It directly consumes the existing node-71 zeta conjugation theorem and covers the σ=1/dual σ=0 identity without a strict-strip restriction. It also proves |χ|=1 on the critical line. These are algebraic/branch bridges; the AFE2 analytic bound is still open.

ChiGammaFactor proves the principal negative-imaginary power, the exact identity Γ(1−s)(2π/i)^(s−1)(1−exp(iπs))=χ(s), and the actual relative error exp(iπs)/(1−exp(iπs)). A uniform denominator bound gives the printed Lemma-7 estimate for |Im s|≥t₀>0, including negative heights. The printed e^(−πt) is large but valid when t<0; it is not silently replaced by e^(−π|t|) with the same branch. The conjugated theorem uses 2π/(−i) and proves the decaying e^(−π|t|) bound at negative heights. Five unfolded regressions cover the corrected functional equation, literal remainder reflection/conjugation, printed Lemma 7 and conjugate branch.

The current inventory is 89 retained files, twenty-three production modules and two verification modules. All new public theorems and consumers are registered. At that checkpoint DKQH-07 remained OPEN for Lemma 6 and the accepted count was 6/20; the later Lemma-6 acceptance closes it. DKQH-15 remains OPEN for the actual reflected AFE bound. The subsequent reflection/digamma sequential checkpoint verifies this scope; the earlier focused audit recorded 591 exhaustive theorem dependencies and 367 registered consumers with zero diagnostics.

Lemma 5 upper-tail source correspondence: J(N,∞,m) is defined as the limit of the actual finite interval integrals, and convergence is proved for 0<σ<1 and m>0. The source consumer states existence and the literal integral limit explicitly. The printed condition involving the bound index m is read as N>t/(πm) for every positive mode included in the sum; the convenient stronger uniform cutoff N>t/π is proved separately. N>0 is explicit, as required by the positive integration domain. The printed decreasing-quotient assertion need not hold for negative t; the proof instead bounds the actual unit-amplitude primitive for both signs and transfers that bound to u^(−σ) by integration by parts. No additional monotonicity assumption or change in the claimed inequality is used. The half-integer and physical-scale assumptions are unnecessary for this second bound. The finite first bound preserves them and every printed coefficient.

## Part-II E₁ arithmetic proposal — owner decision pending

PartIISignReview preserves the literal coefficient from auxilliary_error1. Writing A for the three reciprocal-δ terms, B=log(floor(y)+1)−1/(floor(y)+1)−Re ψ(δ), and C=log(y+1)+γ−(1+2y)/(2(1+y)), the printed coefficient is A−(B+C)/y. Adding the two separately proved bounds gives A−(B−C)/y. Their exact difference is 2C/y. Lean proves that at y=δ=1 the two actual square-denominator tails sum to exactly 1, the printed coefficient is 3−2log(2)−2γ<1, and the assembled majorant is 3/2. The candidate majorant bounds both actual tails for every y>0.

This is a counterexample to the claimed arithmetic majorant, not to the entire Poisson conclusion. An explicit scope question requests adoption of the sign correction because it changes the quantitative Part-II contract. Until the owner answers, the corrected source contract is not adopted. The separate positive-frequency monotonicity gap remains open and no new Part-II hypotheses have been approved. Frozen source bytes are preserved.


Second-integration boundary normalization: the source displays final-bnd-|I_h(-nu)| and bnd1-|I_h(+nu)| omit i from the endpoint factor. The derivative of exp(2πi(f(u)±νu)) is 2πi(f′(u)±ν) times that exponential, so the exact boundary coefficient is 1/(2πi). OscillatoryParts proves this identity and the resulting remainder bound. Taking the norm of the separated endpoint sum retains the same 1/(2π) coefficient. This is an explicit local complex-normalization repair; it does not resolve the distinct E₁ arithmetic or general monotonicity issues, and the frozen source is unchanged.

## Part-II positive-frequency inference: concrete diagnostic

PartIIMonotonicity proves a smooth polynomial example on [0,1]: f(u)=2u−u²/20+u³/300 and g(u)=10−u+u²/20−u³/6000. The printed positive/decreasing conditions hold strictly, and the already accepted Part-I conditions also hold. Nevertheless |g″|/(1+f′)² increases between the endpoints: its values are 1/90 and 110/9409. The complete hypothesis conjunction and failed quotient inference are kernel-checked; SemanticRegression unfolds both polynomials. This refutes the intermediate monotonicity assertion preceding bnd-int-plus-h1, not the full Part-II inequality.

A concrete candidate repair is to require, for h=g′ and h=g(f′−N), both |h′|/(ν+f′−N)² and |h f″|/(ν+f′−N)³ to be nonincreasing for every positive integer ν. These are four analytic input conditions, not the Poisson conclusion. AFESecondWeights already proves them for the actual N=0 AFE weights and phase, including σ=0; OscillatoryParts and AFESecondModes consume them in the second-integration estimate. No additional general Part-II hypotheses have been adopted. The scope decision and the separate E₁ sign decision remain distinct. DKQH-01 and DKQH-09 remain OPEN; total 8/20 DONE.

SecondCoeffBounds proves the unchanged E₂ by exact addition of the separately proved negative/positive cube coefficients; its literal source consumer retains every δ, digamma and rational correction. The E₁ coefficient remains a pending proposal. The actual AFE finite Poisson bound instead displays both square coefficients separately and derives all analytic conditions, including σ=0; it does not silently adopt a corrected general Part-II contract.


## Closed-strip AFE and reflected quantitative estimate

AFESecondClosed extends the assembled estimate continuously to 0≤σ≤1. It proves continuity of the actual sharp polynomials, χ and nonreal ζ remainder, substitutes the exact H/H₁ formulas, and applies the strict-strip theorem on the closure. No convergence of the individual zero-endpoint improper integrals is assumed at σ=0 or σ=1. Conjugation gives afe_closed_strip_abs_bound with positive |t| throughout the error. afe_closed_strip_reflected_bound consumes the actual functional equation and the direct bound at 1−σ with exchanged cutoffs; afe_closed_strip_min_bound proves both estimates simultaneously.

The E07 dual-endpoint proof obligation is therefore resolved for this explicit assembled bound. E04's height-sign bridge is also quantitative. Theorem 10's stated constants, parameter-uniform A₀/B₀ simplifications and equation-(5.2) branch decision remain separate obligations under DKQH-14/15; these gates remain OPEN. No pending general Part-II correction is adopted. Earlier checkpoint lists of missing endpoint/reflection assembly are superseded by this proof. Current scope: 122 retained files, 56 production and two verification modules, 77 semantic consumers; accepted count 8/20. Verification receipts are recorded in the Reproduction Manifest.


## Theorem-10 proof-consistent branches proved; E03 adoption pending

AFESecondUniform proves afe_second_uniform_direct, afe_second_uniform_reflected and their piecewise assembly afe_second_uniform_branches. They concern the actual ζ remainder and both sharp polynomials, with 1/2≤σ≤1, |t|≥t₀≥2π, half-integer x,y≥h≥3/2, and 2πxy=|t|. Every term of A₀, B₀ and the already proved C₀ is retained. The larger cutoff is proved to exceed x₀=max(h,sqrt(t₀/(2π))); the complete B numerator is proved decreasing analytically on the entire normalized interval z≥1. Source consumers unfold both polynomials and every A₀/B₀ term. The proofs include the diagonal, σ=1/dual σ=0, both height signs and exact logarithmic coefficients.

The proved assignment is E_direct=A₀(σ,h,t₀)+C₀(σ,t₀)B₀(σ,t₀) for x≥y and E_reflect=A₀(1−σ,h,t₀)C₀(σ,t₀)+B₀(1−σ,t₀) for x<y. This agrees with the derivation and ancillary call sites; the printed equation (5.2) reverses these E₀ assignments. The frozen printed version is preserved. Adopting the proof-consistent quantitative contract requires the explicit E03 scope decision before DKQH-14/15 can be marked DONE; neither the earlier Part-I approval nor the separate pending Part-II proposals supplies that decision. The existing whole-paper count remains 8/20. Current scope: 126 retained files, 60 production and two verification modules, 84 semantic consumers. Reproduction evidence distinguishes this implementation from source-contract acceptance.

## Constant-weight Part-II source correspondence still under review

The kernel-checked specialization in PartIIConstant derives (log(2)+1/f′(a))/π from the sum of the two finite endpoint terms. The frozen eq:cor-VDC-partII instead writes half this amount. It also cites def:B_f(Z+1/2), whose preceding Corollary 8.1 assumes δ=1/2, without adding that restriction. The existing half-integer endpoint proof applies for δ≥1/2. These discrepancies do not yet constitute a counterexample to the entire printed corollary. The provisional proved bound retains the full finite-head coefficient and the explicit δ≥1/2 condition; neither change has been adopted as the public source contract. The separate E₁ and quotient decisions remain pending.

## Table 3 certified on every displayed range

AFETableThree proves both exact analytic epsilon coefficients lie below the eight unchanged source bounds, for every integer 11≤k≤50 and the entire closed sigma strip. Finite rational logarithm and Euler-constant enclosures, finite exponential series, global maximum bounds and exact rational arithmetic certify the group endpoints. The previously proved k/π+1.1601 bound covers each interior integer. The actual direct and reflected zeta remainders consume these certificates, with both height signs and the full half-integer cutoff conditions. No numerical samples or assumed decimal inequalities enter the proofs.

Table 3, the large-k bound and the constant-six consequence are now proved. Table 1–2 certification and accepted rounding corrections still keep DKQH-16/17 OPEN; E03 and general Part-II decisions remain pending. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20. Verification receipts are recorded separately in the Reproduction Manifest.

## Table 1 failures and proposed Table 2 certificates

TableLowerBounds proves a fourth-order upper estimate for the actual digamma function and a finite lower enclosure 0.577215664≤γ. Combined with rational logarithm/pi bounds, it proves that Table 1's direct entries 2.265204 at exact 2π, 1.792736 at 1000, and 1.750701 at 10¹⁰ are strictly below the actual direct maxima: sigma=1 supplies each witness. These are failures of the claimed numerical maximum bounds, not counterexamples to the zeta remainder inequality itself. The printed entries remain preserved.

AFETableTwo proves outward candidate bounds for all twenty cells at k=1,...,10, over the complete closed sigma strip. Finite exponential sums certify the floor-defined lower cutoffs. Distinct sigma ranges for the two A₀ inputs give separate direct/reflected rational certificates, propagated through the actual global maxima and then the actual two-polynomial AFE. The proposed decimals are listed in Computation Review and explicitly named proposedTableTwoDirect/proposedTableTwoReflected; they are not yet an adopted source repair.

The unchanged Table 3, large-k bound and constant-six consequence remain proved. DKQH-16/17 stay OPEN for the remaining Table 1 certificates and explicit adoption of numerical repairs. General Part-II and E03 decisions remain pending. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.

## Global chi-factor table certificates

ChiTableBounds bounds the actual C₁ on the entire closed sigma strip by a concave cubic and an explicit sum-of-squares identity. A finite Taylor remainder certifies C₂; finite positive exponential sums bound the remaining tails. The complete C₀ product and its actual attained maximum therefore give δ₀≤0.05961930 at exact 2π, δ₀≤0.0003692901 at 1000, δ₀≤3.692588·10⁻¹¹ at 10¹⁰, and δ₀≤1.230863·10⁻¹³ at 3·10¹². The last two are unchanged printed values; the first two are proposed outward replacements, not yet adopted. No optimizer output or sampled interval enters these proofs.

The remaining Table 1 epsilon assembly and numerical-repair adoption stay OPEN under DKQH-16. Table 2 candidates, unchanged Table 3, large-k and constant-six bounds are proved as described above. Pending Part-II and E03 decisions are unchanged. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.

## Complete proposed Table 1 AFE certificates

AFETableOne proves all sixteen proposed Table 1 cells over the entire closed sigma strip. The four thresholds retain exact 2π in the first row. The symmetric lower cutoffs are proved equal to floor(sqrt(t₀/(2π)))+1/2 and are derived from the physical height, half-integer condition and x=y; no extra symmetric-cutoff hypothesis remains. Separate actual direct, reflected and symmetric zeta-remainder theorems consume all coefficient certificates, preserve logarithmic factors and cover both signs of t.

The complete proposed Table 1 and Table 2 replacements are listed beside the preserved printed values in Computation Review. All unchanged Table 3 entries, k/π+1.1601 and the constant-six consequence are also proved. Numerical source-repair adoption and E03 remain pending before DKQH-16/17 can be accepted. The general Part-II decisions and DKQH-09–11 obligations remain separate. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.

## Explicit shifted Part II inputs and the exact half-offset case

PartIIShiftInputs derives the shifted second derivative at closed-interval endpoints from local nonvanishing of f′, rather than assuming a derivative identity outside the interval. It constructs the provisional SecondOrderRegularity interface from explicit twice-differentiable inputs and the pending positive-frequency quotient hypotheses. The shifted product-amplitude monotonicity follows from the existing Part I repair, nonincreasing |f″| and the derivative signs. Its consumers prove the actual full weighted Poisson inequality for every permitted N, at general endpoints and half-integer endpoints.

PartIIHalfSource derives literal square/cube and B expressions when δ=1/2 for every positive y=f′(a)−N, including y=1/2 and M=0. The full weighted-sum bound, its frequency transport and its explicit-analytic-input consumer retain the actual exponential sum and Fourier main sum. The E₁ expression is the proposed sign correction; E₂ is unchanged. This adds proof coverage without adopting the pending quotient or E₁ repairs. Mapping the final accepted source regularity, the remaining Corollary 0.1 discrepancy and the nonlinear B-process still keep DKQH-09–11 OPEN. Earlier descriptions of the shift-input and exact-half-offset bridges as missing are superseded. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.

## Stationary Taylor proof and B-process source review

StationaryTaylor proves the cubic phase remainder D|x|³/6, its derivative remainder D|x|²/2, the exponential perturbation bound πD|x|³/3 and the exact factorization of the actual shifted phase. These require existence of the first three ordinary derivatives on the genuine segment, with the third derivative bounded by D; continuity of the third derivative and infinite smoothness are not assumed. The finite Taylor proof builds the required lower-order smoothness and identifies the within-interval derivatives before applying Mathlib's Lagrange remainder. This is an input to nonlinear stationary phase, not its completed integral estimate.

BProcessReview checks the smooth quadratic f(u)=651u/200−151u²/200 on [1/2,3/2]. Its derivative runs strictly down from β=5/2 to α=99/100, with constant curvature −151/100 and zero third derivative. On the paper's interior range 1≤ν≤floor(β)−1, the reciprocal endpoint majorant in the cited stationary-phase deduction equals 302/(3π), which is strictly greater than 1.251+(2/π)log(β−α). Patel–Yang's cited argument instead restricts frequencies to α+1/2<ν<β−1/2; the paper's range does not preserve that separation. This is a proved failure of the reciprocal-majorant deduction, not a counterexample to the actual complex S₃ remainder or the full B-process inequality.

The review also proves that deleting the last stationary frequency changes the main sum by a term of exact norm 1/sqrt(|f″(x_M)|). The paper's proof uses frequencies 1 through M−1 whereas its conclusion uses 1 through M; a complete argument must account for that term or prove a different joint endpoint estimate. Neither diagnostic licenses an unapproved change to 2.686 or to the source conclusion. DKQH-11 remains OPEN for the nonlinear integral, boundary-frequency accounting and exact constant. Current scope: 142 retained files, 76 production and two verification modules, 129 semantic consumers; accepted count 8/20.
