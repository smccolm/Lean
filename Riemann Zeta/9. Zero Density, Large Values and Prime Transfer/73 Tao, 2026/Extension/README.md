# Tao2026 Lean package

This isolated package contains the active node-73 formalization. The production
root currently imports source-faithful arithmetic-anatomy, interval, literal
counting, and asymptotic-language definitions. It is pinned to Lean `v4.30.0`
and Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The package proves Proposition 2.3(i),(iii), the exact one-term `B¹` and `VB¹`
counts, the full `VB¹` zeta-ratio asymptotic, Lemma 3.2, the complete signed
and uniform Lemma 2.10, and the complete `x^(2/5+o(1))` Corollary 2.11. It
also proves the complete Theorem 1.8 finite and asymptotic assembly conditional
only on Theorem 2.5: an injective certificate/length/offset encoding, explicit
subpolynomial length and coefficient budgets, and the uniform relation count
give the nontrivial-value `x^(2/5+o(1))` bound and hence the literal zeta-ratio
endpoint. It
also compiles the exact Theorem 2.5 summation/integral contract and proves the
arithmetic interface for its Lemma 3.1 consumer: the exact forbidden
fractional rectangle contradicts very badness, every supported weight has
zero prime sum, and specialized Theorem 2.5 yields the required integral
upper bound. An explicit nonzero, nonnegative sine/flat-exponential cutoff is
proved `C∞`, `ℤ²`-periodic, and supported in the rectangle. The contradiction
growth hypothesis supplies the exact source parameter exponent with `K=1`.
The cutoff has a positive uniform inner-rectangle minimum, its integral is
real and nonnegative, and its norm lower bound is reduced to the measure of
the explicit inner good set, with exact reciprocal-set membership. The
two source substitutions and their Jacobians are exact. The retained
quadratic band has unit-period mass `43/50`, and a uniform periodic-slice
argument gives quadratic reciprocal-set measure at least `H/32` under
`N/H²≥1/2`. A finite disjoint unit-cell covering, endpoint trimming, and slow
variation insert the first coordinate and give inner prime-scale measure at
least `H/400` for `H≥200`. The needed arithmetic scale is now proved
unconditionally and eventually: a PNT prime-counting bound plus exact
binomial-factorization and binomial-growth inequalities supplies a prime `p>H`
throughout the quadratic failure window `2N<H²`. The resulting eventual
`N/H²≥1/2` and `H/400` theorems remove unrestricted Sylvester--Schur from the
Lemma 3.1 dependency chain. The fixed lower-cutoff and Theorem 2.5 constants
are coordinated uniformly, and the full eventual shortness contradiction is
proved conditional on `TaoTheorem25SpecializedConclusion`. The exact corrected
`TaoLemma31Conclusion` adds the positive-start `H<N` clause and follows from
both the specialized and full Theorem 2.5 contracts. The Theorem 2.5 smoothness
hypothesis uses `∞` (the genuine `C∞` index), since `⊤` denotes analyticity in
this Mathlib version. The package also proves the
all-orders reciprocal-phase derivative identities used by the cited
Vinogradov argument, as well as the exact four-term arithmetic-function
Vaughan identity in convolution, nested finite-divisor, and
reciprocal-phase-weighted forms. All three convolution terms in that weighted
identity are now reindexed exactly as finite product-box sums with the literal
restriction `m*n ∈ I`; the nested terms use their first-two-factor
convolution as the outer coefficient. Its Type II layer also contains the exact
finite double-correlation expansion, transformed `X_{n,n'}` phase, outer-sum
rearrangement, and coefficient-explicit Cauchy--Schwarz bound. The diagonal is
evaluated exactly, split from the off-diagonal correlations, and bounded by
`#K·#S·L²`; the remaining analytic input is isolated in explicit
off-diagonal `X_{n,n'}` norms. A uniform off-diagonal bound is summed over the
exact ordered-pair envelope `#S(#S-1)`. The transformed linear and higher
reciprocal parameters are proved nonzero
off the diagonal when their original coefficients are nonzero, supplying the
critical-deletion hypotheses for every `X_{n,n'}`.
Their absolute sizes are now controlled exactly: the higher-power numerator
uses `|n'^j-n^j| ≤ |n'-n|·j·B^(j-1)`, while positive lower support bounds
control both denominators. At product scale `KR` these combine into the
source factor `|n'-n|/R`, with higher-term loss `j(B/R)^(j-1)` and hence
`j·2^(j-1)` on dyadic support. The literal product-restricted inner sums have
also been rearranged into correlations on
`K ∩ (1/n)I ∩ (1/n')I`. The literal expression is split into its restricted
diagonal and off-diagonal pieces, its diagonal is bounded, and a uniform
off-diagonal bound yields the final real squared-inner-sum inequality. For
interval `I` and a quotient outer block, this support is one explicit
`Finset.Ico` with ceiling-divided endpoints and length at most the outer block;
the canonical Vaughan correlation rewrites literally as `reciprocalPhaseSum`.
The remaining correlation decay can now be regrouped exactly by
`Nat.dist`: each distance fiber has at most two elements, giving a sharp
factor-two reduction of every nonnegative kernel sum to a one-dimensional
distance sum. The source real-power kernel is nonnegative, equals one at zero,
and is antitone under its natural parameter hypotheses.
Its discrete initial sum is bounded by one plus the matching real interval
integral. The affine-rpow antiderivative, its derivative, the exact integral
evaluation, and the resulting closed-form finite-sum bound are proved. Under
the explicit endpoint condition `1 ≤ R * F^(-c)`, the endpoint is absorbed to
give the pure source-scale bound
`(1+2^(1-c)/(1-c)) * R * F^(-c)`; combining this with the distance fibers gives
the corresponding finite-support correlation estimate with factor two. The
unconditional factor-two estimate retaining `1 + O(R * F^(-c))` is proved as
well, together with the lower bound `1 ≤ ∑d kernel(d)` showing why that
endpoint cannot be discarded without an additional hypothesis.
For the actual off-diagonal support `S.erase n`, the zero-distance fiber is
proved empty. Its positive-distance sum therefore has a pure
`R * F^(-c)` bound without the endpoint condition, and this stronger result
is propagated through the complete squared-inner-sum reduction, actual
short-block specialization, and exact Vaughan double blocks. The pointwise source-shaped correlation majorant
`Q * (A * kernel(|n-n'|) + E)` is now summed over the exact ordered
off-diagonal support and substituted into the product-restricted
squared-inner-sum reduction, without replacing the kernel by a uniform bound.
Specializations to one quotient block and to the exact outer/inner double
blocks prove their distance and positive-index side conditions directly from
the shorter-than-dyadic construction.
Every quotient block has cardinality at most its length `q`; substituting both
outer and inner bounds gives an endpoint-free source-facing squared-sum
estimate in `qouter` and `qinner` alone.
The exact high-frequency arithmetic is compiled separately: for a base
`ℓ≥1`, the hypotheses `ℓ^d≤F` and `b+t≤dc` yield
`ℓ^b F^(-c)≤ℓ^(-t)`, with direct specializations to `ℓ=log P` and the source's
strict inequality. For the complementary high-scale estimate, the source
growth bound `log F≤C(log P)^(3/2-ε)` now yields the exact stretched exponent
`C⁻²(log P)^(2ε)`, and the resulting exponential absorbs arbitrary real
powers of `log P` eventually. The literal choices
`α=(log P)^(4A)`, `q=(log P)^(-3A)` also discharge the coefficient conditions
for every derivative order in `Finset.Icc 1 R`; the full interval derivative
window and Vinogradov's numerical `10^-3` side condition are compiled from the
primitive source growth bound. The production `Vinogradov` module now uses the
literal cutoff `R=10⌈log F/log X⌉+1`; the cutoff together with the phase-degree
shift fits below `log P` eventually for `j≤(log P)^(1/2)`, and the resulting
source-cutoff window is assembled on every regular interval. A conditional
global theorem consumes only a local inequality from that window and supplies
the regular-component multiplier and explicit critical-deletion error. The
source's absolute-constant bound, including `X≥2`, `F≥X^4`, the literal cutoff,
the `10^-3` condition, smoothness on the summation interval, and the `2^-18`
exponent, is isolated as `VinogradovExponentialSumEstimate`; its
reciprocal-phase consumer is proved.  The first internal stage of the pinned
proof is now formalized as well: the literal Taylor degree
`10⌈log F/log X⌉`, its Lagrange remainder, factorial cancellation under the
  source-normalized top-derivative bound, the exact `2π` character-replacement
  cost, and the resulting finite-sum error at the literal derivative cutoff are
  all proved directly from the proposition's hypotheses. The source product
  multiset is encoded by pairs, preserving repeated products and proving its
  cardinality `V²`; the shifted Taylor errors are bounded by one uniform
  envelope. An exact averaging/cancellation theorem now transfers any
  `V²`-normalized estimate for the Taylor-polynomial pair sum back to the
  original exponential sum, without a lower bound on the interval length. For
  the canonical `V=⌊X^(1/4)⌋`, the envelope is reduced to `√X` plus the source's
  normalized top-derivative remainder. Both factors in that remainder are now
  proved at most one, and `√X+2π` is absorbed into nine copies of the target
  scale. The interval pair sum is further decomposed into complete pointwise
  product sums plus an exact boundary strip bounded by `V⁴`. Removing the
  constant Taylor phase identifies every complete product sum with the generic
  coefficient-only bilinear polynomial sum. Its exact trivial `V²` bound closes
  the branch where the normalized target is at least one. Consequently
  `VinogradovBilinearPolynomialNontrivialEstimate` is the smallest residual IK
  statement; a proved instance implies `VinogradovExponentialSumEstimate`
  automatically, with eighteen total copies added to the bilinear constant.
  The nontrivial branch now also proves that the explicit degree block
  `[(4/3)(log F/log X),(7/4)(log F/log X)]` contains at least `R/128` indices
  and that every one meets the source medium-coefficient window with
  `c₀=1/128`, including all floor-rounding losses. The remaining input is the
  ensuing polynomial mean-value estimate. `Tao2026.VinogradovMeanValue` now
  proves both finite Hölder steps, the identities `∑ν=V^ℓ` and
  `∑ν²=J_{ℓ,R}(V)`, the equal-power-sum solution interpretation, and the exact
  unnormalized equation-(16) bound for the original bilinear polynomial sum.
  Its signed difference support has total multiplicity `(V^ℓ)²` and is proved
  coordinatewise contained in `|d_j|≤ℓV^(j+1)`. Exact conjugate-pair expansion,
  regrouping by this support, and `μ(d)≤J_{ℓ,R}(V)` establish equation (18).
  Both variables are then enlarged to the full symmetric box, whose double
  phase expression is factored exactly into one-dimensional coordinate sums.
  The geometric-series reduction, capped reciprocal-distance kernel, separated
  nearest-integer fibers, fiber count, and resulting quantitative integral-test
  bound for each coordinate are now compiled. Both medium-window endpoints
  now yield a coefficient-free logarithmic coordinate saving, normalized by
  the square of its side length; these savings are assembled across all
  coordinates while nonmedium coordinates use the sharp trivial bound. The
  scalar estimate, exact medium-degree reindexing, quadratic degree-sum bound,
  and initial source product saving `V^(-R^2/307200)` now compile, and the explicit
  growth hypothesis is discharged from the original nontrivial-scale
  assumptions. The native frozen Wooley VMVT and the exact equality between
  its Ford moment and the local equation-(17) count now compile as well. The
  squared side-length product is collected as
  `(3ℓ)^(2R) V^(R(R+1))`; the critical identity reduces the entire positive
  `V` exponent to `4ℓ²`, and the abstract critical assembly now gives
  `|B|^(2ℓ²) ≤ C² A V^(4ℓ²+2ε-δ)`. The separate production module
  `Tao2026.VinogradovSharp` now proves, with every low ceiling case explicit,
  that the block `[(9/8)s,(7/4)s]` has weighted mass at least `R²/193` and lies
  in the genuine `c₀=1/4` window. A ninth-order exponential envelope absorbs
  only `1/1024` per degree, giving `V^(-255R²/197632)`. Taking native VMVT
  `ε=δ/128`, extracting the exact critical root, comparing the resulting
  exponent with `4·2⁻¹⁸/s²`, and converting the floor-rounded `V` saving to two
  copies of the exact source exponential decay all compile.
  `Tao2026.VinogradovWooleyCoefficient` now keeps the native concentration
  prime, constant, and starting depth literal and derives the exact critical
  coefficient `C·(p^(B₀+1)κ_R)^ε`; a uniform rooted bound for that expression
  implies the existing VMVT coefficient contract. The native proof supplies
  every datum except this uniform inequality. `Tao2026.VinogradovFord` also
  proves the explicit supercritical multiplier `3R+⌊R/5⌋`, Ford loss
  `3R²/2800`, and `57R³` universal-base coefficient exponent. The resulting
  larger moment root cannot preserve the source's `2⁻¹⁸` decay, so the next
  frontier remains the quantitative rooted bound for the critical p-adic data.
  `Tao2026.VinogradovFiniteDegree` now absorbs every native critical coefficient
  below an arbitrary cutoff into one finite real envelope. Its concrete
  specialization at `1000` proves that rooted control only for `R ≥ 1000`
  implies the existing global coefficient contract and hence the nontrivial
  bilinear estimate. The coefficient is defined optimally as the supremum of
  the normalized mean-value counts. It is itself a valid VMVT witness, and
  every other witness bounds it, so the tail contract is equivalent to uniform
  boundedness of this displayed rooted coefficient sequence.
  `Tao2026.VinogradovOptimalWooley` proves that retained p-adic concentration
  data bound this optimum by the exact Section-12 coefficient, identifying the
  scalar and p-adic descriptions of the remaining frontier. The concentration
  prime is now chosen by Bertrand with `R<p≤2R`, leaving only quantitative
  control of the concentration constant and starting depth. The coordinate-box
  part of the critical root is independently trapped between `1` and `3`, so
  the residual is equivalently coefficient-only, up to an absolute factor.
  The coefficient root is exactly `C_R^(1/κ_R²)`, making its uniform bound by
  `A` equivalent to the correctly scaled growth condition `C_R≤A^(κ_R²)`.
  The remaining bounded-prime p-adic hypothesis is therefore the one explicit
  inequality `C·(p^(B₀+1)κ_R)^ε≤A^(κ_R²)`, with a compiled final consumer.
The mixed Type II theorem now uses the intrinsic low-branch error
`(1/K)^(1/1024)` from `F'≤K^4`, eliminating the retained global block error and
its former upper source-scale hypothesis. The high-branch consumer is proved
for the exact product-restricted quotient interval, conditional on the named
Vinogradov proposition and its already-isolated parameter hypotheses.
The raw component and deletion multiplicities are now bounded by `log P`, and
the entire normalized envelope is eventually at most `3(log P)^(-T)` whenever
`T+2≤3A`. This is also compiled in the exact hybrid callback shape
`Q(4·kernel+3(log P)^(-T))`; membership in a canonical Vaughan inner block
automatically supplies the pair-scale upper bound with multiplier `5`. The
canonical intrinsic-error double-block theorem now consumes this callback
directly, with no abstract high-pair premise. The substantive exponential-sum
proposition and the remaining outer Type I/II/Fourier assembly remain.
Its Type I layer includes variable inner supports, exact parameter rescaling, and the
coefficient-envelope triangle reduction. The
critical derivative expression now has exact two-point power-difference
separation, quotient diameter, one-interval cover, and Lebesgue-measure
bounds. The source-scale specialization gives length at most `16Xq` for each
derivative order and controls finite unions. The discrete deletion count,
including its exact `#orders·(16Xq+1)` lattice-point bound, is also proved.
Finite Abel summation is now explicit as well: uniformly bounded unweighted
prefix sums control the logarithmically weighted interval sum with the exact
loss `2 log b`, closing the formal reduction from the first Type I form to the
source's alternate logarithmic Type I form. In the reverse direction,
uniform prime-log prefix bounds control the unweighted prime phase sum with
the explicit factor `1/log a`, formalizing the source's prime-weight removal.
The low-frequency phase input now includes the explicit derivative bound
`|f'| ≤ (j+1)F/X`, the resulting additive-character total variation bound
`2π(j+1)F`, and the complex Abel reduction of the weighted Mangoldt
discrepancy to uniform initial-subinterval `Λ-1` bounds. The frozen `WeakPNT`
now supplies a proved uniform `o(P)` dyadic discrepancy and therefore an
`o(P)` phase comparison whenever `F` has a fixed bound; the source's stronger
polylogarithmic-scale saving is still open.
The source's finite Fourier step is also formalized exactly: integer modes
rescale the reciprocal-phase parameters, both finite prime sums and integrals
commute with a finite mode sum, and mode errors aggregate against the
coefficient `ℓ¹` norm. The public Theorem 2.5 contract uses `W : ℝ² → ℂ` and
the source's sum over derivative orders in `‖W‖_{C³}`. Integrability follows
internally from the source interval assumptions, while the retained square
frequency box is counted exactly by `(2R+1)²`.
Continuous weights are also proved integrable on the source interval, and a
uniform approximation `‖W-V‖∞≤δ` transfers with explicit prime-sum cost
`(2P+1)δ` and integral cost `Pδ/log P`. The source cubic coefficient envelope
is summable on `ℤ²`; the square boxes exhaust all frequencies, their outer
`ℓ¹` tails vanish, and the associated finite polynomials converge uniformly
to the infinite series. `TorusFourier` descends a continuous periodic plane
weight to Mathlib's unit two-torus, identifies the torus characters with
`fourierMode2D`, and proves that the same partial sums converge uniformly to
the original `W` once the cubic coefficient estimate is available. Thus the
remaining Fourier obligation is to derive that envelope from `W`'s third
derivatives. Its one-dimensional core is complete: the exact periodic
integration-by-parts formula is iterated three times and bounded by the
uniform norm of the third derivative. `FourierSlices` factors the actual
two-torus coefficient in both Fubini orders, identifies its real slices with
unit-interval coefficients, and obtains cubic decay in either nonzero
coordinate. `FourierRadial` combines these estimates and the zero mode into
the radial envelope with constant `27`, proves smooth periodicity bounds the
derivative ranges on the compact fundamental square, constructs the pure
coordinate derivative chains, and derives the unconditional `taoC3Norm`
coefficient estimate from the public smooth-periodic hypotheses.
Nested finite truncations are already controlled uniformly by the exact
discarded coefficient `ℓ¹` norm and transferred to the full discrepancy.
The source's `j=1` case is exactly absorbed into the `j=2, M=0` phase, both
pointwise and for unweighted and prime-log finite sums.
The finite quotient-block core of the shorter-than-dyadic decomposition is
proved, with an exact sum regrouping, ceiling block-count bound, and strict
within-block diameter. A coefficient sequence supported on the original
interval is decomposed pointwise, and in every finite weighted sum, into its
short-block restrictions; those restrictions preserve uniform norm bounds.
The bounded product form of every Vaughan convolution term is then decomposed
exactly into outer blocks, and into double blocks when both coefficients must
be localized, without dropping `m*n ∈ I`. The endpoint-free Type II kernel
bound is carried through these exact double blocks and their explicit lengths.
`VaughanCoefficients` reassociates the identity into the source's actual Type I
and Type II pairs, proves their cutoff/tail supports, and derives the absolute
coefficient envelopes `1`, `log P`, `1`, `log P` from `|μ|≤1` and
`Λ*ζ=log`. The canonical family over `[1,B]`, with
`L=(log₂ B+1)^101`, has exactly `(log₂ B+1)^102` indices and covers every
positive coefficient index. Every weighted coefficient sum and the final
Type I/II Vaughan expression decompose exactly over this family while
retaining `m*n∈I`. The real-log comparison and the extra subdivision power
absorb ceiling rounding, giving every nonzero block coefficient the source's
literal relative support width `(1+log(B)^(-100))M`; small scales are handled
as singleton blocks. For `P≤B`, logarithm monotonicity gives the paper's
literal `(1+log(P)^(-100))M` width. The analytic cancellation theorem remains open.
`WeylDifferencing` supplies its first unconditional finite layer: exact
shifted-pair fibers, the `H`-fold averaging identity, the corresponding
Cauchy--Schwarz inequality, and an exact regrouping of window squares by
`n+h=n'+h'`. The two shift orders become truncated forward correlations or
their conjugates, yielding a real and divided finite van der Corput bound.
The strict lag range, exact zero-lag split, uniform recursive rule, source
`reciprocalPhaseSum` translation, appended-lag recursion, and smooth
real-difference derivative bridge are proved as well. The terminal affine
geometric sum is evaluated exactly and bounded in nonresonant form by
`min(N, 2 / ‖e(alpha)-1‖)`; exact sine evaluation and a canonical rounding
argument strengthen this to `min(N, 1/(2 dist(alpha,ℤ)))`. The iterated
engine now propagates a uniform terminal estimate through any finite number
of rounds by an explicit nested square-root majorant, with a four-step
source-facing specialization. A one-step real finite difference is exactly an
interval integral of its derivative, and both absolute upper and signed lower
derivative-separation bounds are proved. For globally smooth phases they
iterate with the exact product of all lags. The iteration is also localized to
the positive ray and exact evaluation interval, then specialized to the source
reciprocal phase with explicit raw upper and regular-set lower bounds. Constant
sign for the lower bound is derived from continuity. The derivative of a
terminal iterated phase is now the matching difference of the next original
derivative, with a uniform critical-regular two-sided window frozen at `X` and
`2X`; four lags consume the fifth source derivative. The frozen
Kusmin--Landau estimate is adapted exactly from radians to `exp(2πix)`, and
mean-value plus second-derivative sign bridges convert absolute terminal
derivative windows into monotone increments. A source-facing theorem therefore
proves the nonlinear critical-regular terminal exponential-sum estimate under
explicit expanded-interval regularity and upper-one-period hypotheses. Exact
lag-sum and lag-product bounds now make it uniform over every admissible lag
list and truncated initial length on one expanded regular interval, and it is
fed directly through the recursive majorant. The literal four-round theorem
uses derivative orders five and six and one worst-case `H^4` upper-smallness
condition. The exact `weylTreeMajorant` now retains each accumulated lag list
and boundary-truncated length, and the source leaf profile
`min(L, 1/(prod(lags)*scale))` feeds it directly. Its innermost lag sum is
bounded by the exact harmonic factor `harmonic H`, with the resulting
one-level square-root estimate proved. The theorem
`weylTreeMajorant_lagProduct_le_closed` now collapses every outer lag sum to
explicit scalar length and scale recurrences; their generalized harmonic
factors are bounded by `H`. The four-round reciprocal-phase wrapper is closed,
and its fourfold iterated scale root satisfies the exact sixteenth-power
identity. The resulting coarse scale recurrence has exact four-round
sixteenth power `(QH)^15`; after including the terminal inverse scale this is
`(QH)^15/scale`, and the corresponding source wrapper is proved.
The length recurrence is split into four explicit nonnegative terms with exact
sixteenth powers `D^8`, `E^8D^4`, `E^12D^2`, and `E^14D`. Exact step-factor
arithmetic yields the associated powered denominator bounds with exponents
`8,4,2,1`. All four diagonal bounds and the scale bound are extracted as
sixteenth roots and rewritten exactly as real `1/16` powers in a source-facing
five-term majorant with no hidden recurrence. The canonical floor-rounded range
`floor((2U)^(-1/4))` is proved to discharge the exact upper-smallness condition
and is installed in root and rpow source wrappers. Expanded critical starts are
counted by `orders.card*(16Xq+4H+2)`; the complement is split exactly into
per-order integer interval hulls. Their endpoint cut set has size at most
`2*orders.card`, so the regular component multiplier is `2*orders.card+1`,
independent of `Xq`; full real margins are regular off the hulls, and a global
source wrapper combines sharp Weyl bounds on long components with trivial
bounds on short ones while retaining the additive expanded-deletion error.
Successive Cauchy--Schwarz bounds preserve the exact generalized harmonic
gain: the sharp terminal coefficient has sixteenth power at most
`(6L)^15 * harmonic(H)^4 / (H+1)^4`, with a source-readable `1 + log H`
wrapper. The global theorem now accepts any
upper-small range, and the adaptive choice
`min(L, floor((2U)^(-1/4)))` automatically fits the component envelope while
preserving upper-smallness. Its two branches are combined by
`(H+1)^(-4) <= 2U+(L+1)^(-4)`, and the resulting effective global theorem
chooses the critical width as the `1/128` power of the complete error scale.
The latter is exactly
`240(5+j)^5 F/X^5 + (L+1)^(-4) + 1/F` and has a proved source-shaped upper
bound with the derivative-order factor explicit.
The genuinely optimized range `min(floor(L*q), canonicalRange)` is now also
installed globally. Its two short-piece occurrences are replaced by the
proved bounds `L*q` and `4L*q+1`, and its logarithm is bounded by `log L`.
The optimized denominator bound `1/(H+1)^4 <= 2U+1/(Lq)^4` is also propagated
through the terminal root, leaving only explicit `log L`, `U`, `q`, and lower
derivative scale there. The four diagonal roots are subsequently compressed to
`72Lq`, while the terminal root is bounded by
`100((5+j)^5+1)(1+log L)Xq`; the complete optimized majorant therefore has the
fixed-power bound with constant `172`. This is installed in the global
component theorem and in a source-normalized wrapper replacing `q` by the
explicit `1/128` power of the three-term error. A final endpoint-absorbed
wrapper is one explicit coefficient times `X` and that source power.
An exact short/long dichotomy now removes the interval-length term for
`F≤X^4`, giving the arbitrary-subinterval two-term width
`(F/X^5+1/F)^(1/1024)`. For `N=M`, the transformed Type II scale controls
natural distance, so this width is dominated by an explicit kernel-plus-error
term and propagated through the endpoint-free Vaughan double-block
squared-sum theorem. The pair-dependent `F'/K^5` premise is now replaced by
the explicit uniform `typeIIShortIntervalScaleError`, computed from the inner
block's left endpoint and length. In the quadratic wrapper, outer-block
geometry also discharges the endpoint and power-evaluation conditions.
The transformed-scale bound follows from the displayed block error being at
most `1/K`; in the quadratic case this is now derived on large inner bands
from `10F≤K^4(log Bcap)^100`. The logarithmic block-width theorem first gives
`10qF≤K^4R`, and the reciprocal-phase scale estimate then derives the former
monomial inequality `5q|N|≤K^5R^2` internally. The kernel
and Weyl layers now accept arbitrary positive block
endpoints and are specialized to the exact named dyadic Vaughan blocks. The
effective-error family is reduced to one explicit scalar bound, and the
logarithmic Vaughan width proves `5q≤K`, which supplies the expansion margin
on every band above the subdivision budget. The canonical dyadic theorem
therefore exposes the large-inner-band condition and
`10F≤K^4(log Bcap)^100`, rather than an abstract block-error or derived monomial
hypothesis. It also derives the complete effective-error condition from the
source-faithful near/far split: scaled distance at most three is absorbed by
the kernel's `1/4` lower bound, while farther pairs have reciprocal transformed
scale at most `2/3` and use a `1/4` upper-scale budget. That budget follows
from the pair-local `F'/K^5≤1/K`, and `2≤log Bcap` automatically makes the common subdivision
budget large enough. If the inner dyadic band is below that budget,
`sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_singleton`
proves the block is purely diagonal. The generic and canonical
`..._norm_sq_le_weylVinogradov_quadratic_additiveError` theorems now execute
the analytic split pair by pair: they prove every far pair with `F'≤K^4` by
four-step Weyl, retain its `E^(1/1024)` error, and expose only the complementary
`K^4<F'` correlation estimate with an independent nonnegative error `V`. The source
inequalities needed to turn the retained block-error term into logarithmic
saving, and the high-scale Vinogradov estimate itself, are not yet claimed.
The prime/Mangoldt conversion is exact: the prime-logarithm phase sum and
higher-prime-power tail are split in `PrimePowerReduction`, and unit modulus
reduces the tail to the frozen explicit local prime-power bound.
The `FactorialCoefficientBounds` module proves Tao's complete Lemma 4.1:
type-`F₃` intervals satisfy `H<N`, contain no prime, and their witnessing
factorial index satisfies `a ≤ C H log N` for one uniform positive constant.
Its proof includes the exact upper-half Chebyshev-theta inequality and closes
the finite PNT-exceptional range.
`FactorialShortIntervals` then proves the common arithmetic reduction for
Lemma 4.2 at `P=H log²N`, including even valuation, unique-element square
divisibility, and complete exclusion of primes in Tao's large-`P` branch.
`FactorialEquidistribution` proves the exact final-arc-to-interval-divisor
bridge, the resulting zero prime sum on `(P,2P)`, and the direct specialized
Theorem 2.5 integral upper bound. It defines both a shrinking supported bump
and a quantitatively normalized smooth-transition weight which is exactly one
on Tao's inner plateau arc. Smoothness, periodicity, nonnegativity, support,
the exact `1/(60 log²N)` unit-period mass, long-interval mass, reciprocal
change of variables, logarithmic-weight comparison, prime-integral norm lower
bound, and the final lower/upper sandwich are proved. The uniform polynomial
`C³` estimate is proved with the coarse sufficient bound `O(log^12 N)`, and
the final large-`P` logarithmic contradiction is complete. The exact
`21/40` Baker--Harman--Pintz proposition interface yields `4P≤N` eventually,
so the high-`P` branch closes conditional on that interface and Theorem 2.5.
The same module transfers the existing stretched-log parameter calculation
from `H` to `P≥H`, so its final upper-bound wrapper has no user-supplied
Vinogradov range hypothesis.
For the low-`P` branch it also defines the two-coordinate product cutoff,
proves smoothness, periodicity, support, exact prime-sum vanishing, a uniform
`O(log^12 N)` `C³` estimate, and the resulting Theorem 2.5 integral upper
bound. `FactorialLowGeometry` proves both exact substitutions, endpoint
trimming, occupied-unit-cell insertion for the shrinking first band, the
prime-set lower bound `H/1920`, and the fixed quadratic-bump integral lower
bound. Its logarithmic contradiction closes the low-`P` branch and joins it
with the high-`P` branch. Thus Lemma 4.2 is complete conditional on Theorem
2.5 and Proposition 2.3(ii). `PrimeIntervals` now also proves that the pinned
source-shaped BHP backward interval theorem implies the exact uniform natural-
endpoint Proposition 2.3(ii), including forward-endpoint conversion and finite-
range absorption. The analytic proof of the source BHP theorem itself remains.
`FactorialExtraction` proves Lemma 4.3 in explicit finite form. Every interval
element has its canonical decomposition `c n²`, with `c` positive, squarefree,
and supported on primes at most `P=max(a,H)`. The product of all coefficients
divides `∏_{p≤P}p^(H/p+1)`; Chebyshev estimates and two-half averaging select
ordered elements with coefficients at most
`exp(3 log 4 (2+log P+P/H))`, yielding the required relation
`c₁n₁²+h=c₂n₂²` with `0<h<H`.
`FactorialCounting` begins the exact Theorem 1.9 assembly without identifying
endpoint values with interval witnesses. It chooses a structured Lemma 4.3
certificate for every nontrivial interval, proves that the certificate,
interval length, and selected-element offset recover the interval, and embeds
each arbitrary-budget subfamily into an explicit finite code range. Its final
finite estimate is `A·C²·G³` times one uniform Lemma 2.10 relation budget; the
small-index-or-bounded-length predicate and its complement are also proved to
partition all witnesses exactly.
`FactorialSmoothCounting` refines the bounded-length side using the literal
Mathlib smooth-number finset. It proves that the ordered coefficient range has
cardinality exactly `psiNat x P ^ 2`, places every chosen Lemma 4.3 certificate
with `max a H ≤ P` in that range, and obtains the exact endpoint bound
`A·psiNat(x,P)²·G³` times the uniform Lemma 2.10 budget. Proposition 2.1(ii)'s
full analytic estimate remains open, but this branch needs only its
`P=O(log x)` consequence. `SmoothNumberBounds` proves that consequence
directly by iterating Mathlib's square-times-squarefree decomposition and
using the Chebyshev prime-counting bound. Lemma 4.1 then places every actual
fixed-bounded-length interval in the concrete logarithmic smooth family, and
`factorialBoundedLengthEndpointCount_powerUpperBound_zero` closes that source
subfamily unconditionally.
`FactorialSmallIndexCounting` closes the other easy source regime at the fixed
threshold `a ≤ H log(x+2)/100`. It proves exact parameter and coefficient
budgets from Lemma 4.3, bounds each selected coefficient by
`x^(1/10+o(1))`, and feeds these budgets into the injective interval code.
Consequently the literal small-index endpoint family is
`x^(1/4+o(1))` after Lemma 4.2. Only the complementary large-sieve regime
remains in the upper bound for Theorem 1.9.
`FactorialLargeSieve` now formalizes the exact finite interface for that last
regime. For every upper-half prime `a/2<p≤a`, divisibility of the interval
product puts the start `N mod p` in the image of `h↦-h` for `1≤h≤H`; this set
has at most `H` elements, so at least `p-H` classes are removed. Each fixed
`(a,H)` interval fiber injects into the literal survivor set, and all fibers
reassemble with only an `A·G` loss under global index and gap budgets. Lemmas
4.1 and 4.2 provide such subpolynomial budgets. The source-side large-sieve
arithmetic is also compiled: the upper-half primes are pairwise coprime, every
selected product is at most `a^k`, PNT gives at least `a/(4 log a)` moduli,
deleting `k` terms loses at most half when `2k≤#Q`, and the remaining
removed/allowed weight is at least `a log(x+2)/(3200 log a)`. The surrogate
weight `(p-H)/H` is proved below the literal complement/allowed cardinality
ratio. `LargeSieve` proves native cyclic DFT Parseval and the one- and
two-modulus Montgomery uncertainty inequalities. `LargeSieveTensor` proves
the arbitrary finite tensor inequality, constructs the iterated additive CRT
equivalence for pairwise-coprime moduli, and applies the tensor inequality to
finitely supported natural-number sequences with simultaneous residue
restrictions. Tensor characters are now reindexed injectively as ordinary
cyclic DFT frequencies modulo the product, with exact equality of Fourier
energies. Parseval and an exact residue-fiber count prove the matching upper
bound for any one product denominator and hence a finite survivor-cardinality
inequality. `LargeSieveGlobal` now proves the finite Schur Gram-form estimate,
the exact analysis/synthesis and synthesis/Gram identities, and Bombieri
duality for arbitrary finite complex vector families, including direct
transfer from any synthesis-energy bound. `LargeSieveCircle` identifies the
circle-character Gram matrix exactly with its Dirichlet kernel and computes
the diagonal. Its Fejér layer embeds every length-`L` synthesis coordinate
exactly `L` times into shift differences of length `2L`, identifies their Gram
matrix with the nonnegative squared Dirichlet kernel, and reduces the circle
large-sieve inequality without loss to Fejér row and column bounds. The new
`LargeSieveSeparated` layer proves the separated-circle Fejér row-sum estimate
by centered representatives and radial bins, and hence an explicit
large-sieve inequality with constant `8L` for arbitrary finite frequencies
separated by `1/L`. `LargeSieveRational`, `LargeSieveSelections`, and
`LargeSieveAggregation` then identify the CRT numerator, prove cross-denominator
distinctness from an exclusive modulus, establish `1/L` separation for every
tensor frequency from every fixed-cardinality selection, and sum the tensor
lower bounds against one global upper bound. This gives the finite Corollary
2.8 survivor inequality `(∑ S, ρ(S)) * #survivors ≤ 8L` without a
subset-count loss. `LargeSieveDenominator` proves the fixed-cardinality
elementary-symmetric lower bound using the exact binomial cardinality and
`choose n k ≥ (n/(2k))^k`. `FactorialLargeSieveCor29` packages the literal
residue complements, proves their exact tensor-ratio product, transports the
natural survivor set to `Fin (x+1)`, and derives the source-scale fixed-fiber
Corollary 2.9 estimate. The remaining large-sieve work is the maximal-`k`
asymptotic closure of the nontrivial Theorem 1.9 upper count.
The compiled Lemma 4.2 contract is propagated to Theorem 1.10 through the
explicit natural gap budget `⌈exp((log x)^(3/4))⌉`, proved both to bound every
factorial-square triple tail and to be `x^o(1)`. Thus its remaining inputs are
Theorem 1.9, Erdős--Selfridge, Theorem 2.5, and the analytic BHP theorem.
None of Theorems 1.7--1.10 is complete or claimed. Imports from
node 74 enter only through the exact immutable snapshot under `Dependencies/`.
