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
