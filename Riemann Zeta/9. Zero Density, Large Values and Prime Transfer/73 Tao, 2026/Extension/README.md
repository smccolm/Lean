# Tao2026 Lean package

This isolated package contains the active node-73 formalization. The production
root currently imports source-faithful arithmetic-anatomy, interval, literal
counting, and asymptotic-language definitions. It is pinned to Lean `v4.30.0`
and Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The package proves Proposition 2.3(i),(iii), the exact one-term `B¹` and `VB¹`
counts, the full `VB¹` zeta-ratio asymptotic, Lemma 3.2, the complete signed
and uniform Lemma 2.10, and the complete `x^(2/5+o(1))` Corollary 2.11. It
also proves the complete Theorem 1.8 finite and asymptotic assembly
unconditionally: the source-faithful IK argument proves the specialized
Theorem 2.5 input, while an injective certificate/length/offset encoding, explicit
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
 for every start once `H` is sufficiently large, hence throughout the quadratic
 failure window `2N<H²`. Start monotonicity and the explicit threshold `H^H+1`
 further reduce unrestricted Sylvester--Schur to a finite rectangle. Checked
 modules prove every row below `101`, an effective all-start tail from `121`,
 and all twenty intervening rows. Thus unrestricted Sylvester--Schur is now
 proved. The resulting eventual
`N/H²≥1/2` and `H/400` theorems remove unrestricted Sylvester--Schur from the
Lemma 3.1 dependency chain, and the common start cutoff also removes it from
the asymptotic Theorem 1.7 chain. The fixed lower-cutoff and Theorem 2.5 constants
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
proposition remains. The exact convolution bridge now rewrites each literal
product-restricted Vaughan Type II double block as the corresponding outer
sum, applies Cauchy--Schwarz, enlarges the bounded support to the canonical
block, and inserts the actual beta/gamma coefficient bounds `1` and
`log(2B)`. Consequently the conditional source Vinogradov estimate reaches
the norm square of the literal double block. A separate exact triangle theorem
bounds the full product convolution by the sum of the square roots of its
double-block majorants. The remaining assembly work is the all-block source
regime split, asymptotic Type I/II summation, and Fourier closure.
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
`A·psiNat(x,P)²·G³` times the uniform Lemma 2.10 budget. This branch needs only
the `P=O(log x)` consequence of Proposition 2.1(ii). `SmoothNumberBounds`
proves that consequence
directly by iterating Mathlib's square-times-squarefree decomposition and
using the Chebyshev prime-counting bound. Lemma 4.1 then places every actual
fixed-bounded-length interval in the concrete logarithmic smooth family, and
`factorialBoundedLengthEndpointCount_powerUpperBound_zero` closes that source
subfamily unconditionally.
`SmoothNumberRankin` starts the stronger Proposition 2.1 route. It proves
summability and the exact finite-prime Euler product for the Dirichlet series
of positive smooth naturals, transports Mathlib's strict cutoff to Tao's
inclusive `p≤y` convention, and proves the finite bound
`psiNat X y ≤ X^sigma ∏_{p≤y}(1-p^(-sigma))⁻¹` for `X≥1` and `sigma>0`.
Every factor is further converted to an exponential geometric tail and the
denominators are uniformly controlled by the prime-two factor. The resulting
source theorem exposes the exact saddle exponent
`-(1-sigma)log X + (1-2^(-sigma))⁻¹∑_{p≤y}p^(-sigma)`.
`SmoothNumberPrimeSum` performs the next exact layer: finite Abel summation
rewrites the weighted prime sum as its `pi(y)y^(-sigma)` endpoint plus
nonnegative backward differences against `pi(n)`. Mathlib's explicit
Chebyshev theorem then gives a fully unconditional finite majorant, which is
substituted back into the Rankin exponent. The square-root remainder in the
explicit theorem is absorbed to give the clean global majorant
`(2 log 4+2)n/log n`. A proved Bernoulli estimate gives
`n^(-sigma)-(n+1)^(-sigma)≤sigma*n^(-sigma)/n`. After exact cancellation,
only the canonical finite power-log sum `∑ n^(-sigma)/log n` remains.
A second Bernoulli/telescoping proof bounds this sum unconditionally using the
uniform denominator `log 2`, producing a fully explicit sum-free Rankin
estimate. A sharper source-scale range split replaces this coarse denominator
by a growing logarithm. That split is proved at
an arbitrary `2≤k≤y`: the lower range has scale `k^(1-sigma)/log 2`, while
the upper range gains `log k`. Two explicit cutoff comparisons normalize the
result to a growing `log y` denominator and feed it back into Rankin. The
concrete divisor `R=(log y)^(1/(1-sigma))` is now proved to satisfy
`R^(1-sigma)=log y`; flooring `y/R` preserves the power comparison. Moreover,
for `y≥4`, the single separation `2R≤sqrt y` supplies the cutoff lower bound
and the logarithmic comparison with `L=2`. This yields compiled canonical
power-log, weighted-prime, and source-facing Rankin estimates. It remains to
specialize the separation in the polylogarithmic regime. The standard
variables `u=log X/log y` and `sigma=1-log u/log y` are now defined, their
range conditions are explicit, and the exact identities
`y^(1-sigma)=u` and `-(1-sigma)log X=-u log u` are proved. In the critical
`y=z^(alpha+o(1))` regime the square-root separation is too strong, so that
branch uses a finer multi-scale power-log bound. The required finite argument
now compiles: on each `[a,b)` it retains the difference of the two endpoint
`(1-sigma)` powers divided by `(1-sigma)log a`; consecutive intervals along
any monotone cutoff chain reassemble exactly, and their local majorants sum
termwise. The saturated dyadic chain `min y 2^(i+1)` reaches `y` after exactly
`clog 2 y - 1` active blocks. Freezing each block at its left endpoint and
using its cardinality removes the artificial `(1-sigma)â»Â¹`, leaving the
explicit exponential-harmonic sum `∑_{j≤m}2^(j delta)/j`. An arbitrary
cutoff lemma and its midpoint specialization now bound this by a harmonic
prefix plus a geometric tail, and `2^delta-1≥delta log 2` exposes the sharp
terminal denominator `m delta`; the resulting closed midpoint estimate is
fed back into the original power-log sum. The named dyadic majorants are also
propagated through the weighted-prime sum and source-facing Rankin exponent.
Exact depth/logarithm comparisons convert the terminal part further to
`2(2y)^delta/(delta log y)` and then, for the actual saddle, to
`2*2^delta*u/log u`. The midpoint exponential is now bounded by the square
root of the terminal source scale, giving a prefix
`sqrt(2^delta*u) * (1+log(floor(m/2)))`. An explicit finite absorption wrapper
proves the complete scalar estimate `5u/log u` under
`2(1+log(floor(m/2)))log u <= sqrt u`. Both exact source regimes now discharge
the needed quadratic depth envelope and optimize the full positive Rankin
contribution. The compiled depth comparison
`1+log(floor(m/2)) <= 1+log(log(2y)/log 2)` and the general inequality
`log u <= 4u^(1/4)` reduce the generic obligation to the explicit
continuous-scale condition `8(1+log(log(2y)/log 2)) <= u^(1/4)`.
The exact critical source contract is now `IsTaoCriticalSmoothRegime X y α`,
meaning `log X/log x -> 1` and `log y/log z(x) -> α` with `α` fixed. The
identities `log z` and `log x/log z = u₀` are proved, as are `u₀ -> infinity`,
`u/u₀ -> 1/α`, and `u -> infinity` for every fixed `α>0`. The source-scale
decay `log z/u₀² -> 0` transfers to `log(2y)/u² -> 0`, proving the quadratic
dyadic-depth envelope. Lean also derives `X,y >= 2`, `u>1`, `u<y`, and hence
`sigma>=0` eventually. Consequently the critical contract alone now feeds the
generic consumer and yields the complete scalar estimate `5u/log u`. The
optimized finite `Psi` bridge is now also compiled: the positive dyadic error
is `o(log z)`, while `u log u/log z -> 1/α`. Hence for every fixed `ε>0`,
`Psi(X,y) <= X/z^(1/α-ε)` eventually. `SmoothNumberLowerBound` fixes the
integer side of that branch: `k=Nat.log y X` obeys `k/u₀->1/α`,
`log k/log₂x->1/2`, and `k log k/log z->1/α`; moreover the frozen PNT yields
`log pi(y)/log z->α` and eventually `2k<=pi(y)`. The compiled
`HasCriticalSmoothLowerSaddle X y E` consumer turns
`X*exp(-(u*log u+E))<=Psi(X,y)` and `E/log z->0` directly into the sharp
critical lower estimate.  Lean also proves this condition for every fixed
CEP-sized error `E=C*u*log(log u)`, proves `log u/log y->0`, and enters the
fixed source-uniform range `u<=y^(1/2)`. The exact finite combinatorial base
includes all exponent vectors of total degree at most `k`: stars and bars
gives `choose(k+pi(y),pi(y))`, unique factorization makes the product map
injective, and `y^k<=X` embeds the whole family into `Psi(X,y)`.  The source
counting function also satisfies the exact largest-prime recurrence
`Psi(X,y)=1+sum_{p<=min(X,y)}Psi(X/p,p)` for `X>=1`, proved by a bijection with
largest-prime/smooth-cofactor pairs.  `SmoothNumberHildebrand` adds the exact
weighted bridge: smooth multiples of `p^a` are counted by `Psi(X/p^a,y)`, the
total `p`-adic multiplicity is their prime-power sum, and summing
`log n=sum_p v_p(n)log p` gives the finite Chebyshev--Hildebrand identity and
its exact nonnegative boundary-defect decomposition.  Discarding higher prime
powers gives the recursive inequality
`sum_{p<=y} log(p)Psi(X/p,y)<=Psi(X,y)log X`. The first full finite iteration
is compiled: for every
`d` with `y^d<=X`,
`theta(y)^d<=Psi(X,y)(log X)^d`, hence
`(theta(y)/log X)^d<=Psi(X,y)` when `X>=2`.
`SmoothNumberCriticalLower` retains the fractional endpoint with the
canonical residual `b=floor(X/y^d)`: it proves `1<=b<y`, `y^d*b<=X`, the
refined product bound `theta(b)theta(y)^d<=Psi(X,y)log(X)^(d+1)`, and a uniform
thresholded endpoint factor.  The pinned PNT supplies one fixed threshold
above which `theta(b)>=b/2`; below it the omitted residual is bounded.  The
complete loss ledger is also formalized: the finite inequality
`X/(B*2^d*(log X)^(d+1))<=Psi(X,y)` has normalized logarithmic denominator
`2/alpha`, yielding `X/z^(2/alpha+epsilon)<=Psi(X,y)`.  Thus this elementary
Hildebrand route is certified to lose a factor of two in the critical
exponent.  The sharp consumer is nevertheless complete: a lower packet with
loss `u*log u+E`, where `E/log z->0`, yields the required
`X/z^(1/alpha+epsilon)` estimate. The finite CEP packet itself is
source-faithful: `SmoothNumberCEPIntervals` encodes the exact open--closed
bands and proves them pairwise disjoint, `SmoothNumberCEPWeights` defines
`k=floor(log(u)^2 log(log u))`, the geometric `alpha_j`, and proves (3.7),
and `SmoothNumberCEPSource` specializes the collision-free (3.11) and
cofactor-density (3.10) bridge to `floor(alpha_j*u)` prime choices per band.
`SmoothNumberCEPSize` proves the exact reverse geometric moment, aggregates
the flooring loss, and gives every generated multiplier the finite lower
exponent from (3.6)--(3.8). `SmoothNumberCEPPrimeMass` identifies each exact
band cardinality with the corresponding difference of `Nat.primeCounting` at
the floored endpoints, reduces reciprocal mass to that literal endpoint
estimate, and propagates it through (3.11)--(3.10).
`SmoothNumberCEPBootstrap` proves the exact
saddle identity `X^(1/(log X/log y))=y`, hence identifies the canonical
natural packet cutoff with `y` and feeds the canonical packet directly into
`psiNat X y` without a rounding loss. `SmoothNumberCEPCoarse` then replaces
the shrinking source bands by fixed dyadic PNT blocks. It proves reciprocal
mass at least `1/(16 log 2 log u)`, uses multiplicity
`floor(u-2u/log u)`, bounds the cofactor depth by `10u/log u`, and bounds the
complete secondary loss by `60u log(log u)`. This constructs
`HasCriticalSmoothLowerSaddle X y (criticalSmoothLowerCEPError 60 X y)` and
proves the unconditional sharp theorem
`IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat`. Thus all
four quantified upper/lower halves of Proposition 2.1 are compiled and
audited. The exact shrinking-band route remains as an optional source-faithful
alternative; its shrinking-band estimate is not a blocker. Downstream
multiplicative instantiation over the fixed prime block `z<p<3z` is now
compiled in `BadOneTermAsymptotics`: the exact `B¹` identity and reciprocal
prime mass prove `x/z^(2+ε) <= badOneTermCount x` eventually. The matching
upper bound partitions the exact prime sum at `sqrt z` and `z²`, covers the
middle by a finite exponent grid, and absorbs the fixed grid cardinality.
Consequently `badOneTermCount_quotientPowerScale` proves Lemma 1.6(i).
`SmoothNumberStability` now uses the literal floored cutoff `floor(cX)`,
proves its ratio/logarithmic limits and preservation of the critical regime,
and isolates Granville (3.24)'s quotient limit from its formal `IsTheta`
consequence. `TaoLemma16iiConclusion` is the exact target for Lemma 1.6(ii),
with both automatic monotone directions proved. `BadOneTermRegularVariation`
derives the full contract from the sharp critical dilation limit by iterating
the half-ratio through powers of two and bracketing every floored fixed
dilation. `SmoothNumberSaddlePoint` now constructs the exact
positive saddle solving `sum_{p<=y} log(p)/(p^sigma-1)=log X`, proves
existence and uniqueness, defines the positive second sum `phiTwo`, proves
`phiOne'=-phiTwo`, and gives the exact mean-value sensitivity identity under
changes of `X`. `SmoothNumberSaddleRegimes` bounds `phiOne(y,1)` by an
explicit Abel--Chebyshev majorant and `phiOne(y,1-epsilon)` by prime counting;
it proves that the exact saddle tends to `1` in every critical regime. The
second saddle sum is at least `log(2) log(X)` at the saddle and therefore
diverges; the exact secant estimate and regime preservation show that fixed
dilations change the saddle by `o(1/log y)`. The remaining gap is the uniform
saddle-point asymptotic itself. `SmoothNumberSaddlePhase` defines its exact
logarithmic Euler-product phase and Gaussian main term, proves the two phase
derivatives, recovers the Euler product by exponentiation, evaluates Rankin's
bound at the saddle, and proves the saddle is the unique positive global
minimum. The exact old/new minimum-phase squeeze then proves that dilation
changes this minimum by `log(c)`. Uniform prime-local curvature estimates
show that the `phiTwo` quotient tends to `1`, so the quotient of the complete
Gaussian main terms tends to `c`; only the uniform comparison with `Psi`
remains. That comparison is represented exactly by
`TaoCriticalSmoothSaddleAsymptoticConclusion`, which is proved to imply both
the quotient-limit and `IsTheta` stability contracts.
The exact polylogarithmic source contract is `IsTaoPolylogSmoothRegime X y A`,
meaning `log X/log x -> 1` and `log y/log₂x -> A` for fixed `A>1`. Its natural
scale `log x/log₂x` is represented by `taoPolylogUZero`; Lean proves
`u/taoPolylogUZero -> 1/A`, `sigma -> 1-1/A`, the quadratic dyadic-depth
envelope, and the full scalar estimate. The leading saving satisfies
`u log u/log x -> 1/A`, while the complete positive dyadic error is
`o(log x)`. Consequently `Psi(X,y) <= X/x^(1/A-ε)` eventually for every fixed
`ε>0`. `SmoothNumberLowerBound` proves the matching lower estimate.  Its exact
depth `k=Nat.log y X` satisfies `y^k<=X` and differs from the real Rankin ratio
by less than one.  The frozen PNT gives `log pi(y)/log₂x->A`, while
`log k/log₂x->1`, so eventually `2k<=pi(y)`.  Products of fixed-size prime
subsets are injective, smooth, and bounded, and the integral binomial entropy
bound yields `x^(1-1/A-ε)<=Psi(X,y)` eventually. Multiplicative stability
remains open in this regime.
`FactorialSmallIndexCounting` closes the other easy source regime at the fixed
threshold `a ≤ H log(x+2)/100`. It proves exact parameter and coefficient
budgets from Lemma 4.3, bounds each selected coefficient by
`x^(1/10+o(1))`, and feeds these budgets into the injective interval code.
Consequently the literal small-index endpoint family is
`x^(1/4+o(1))` after Lemma 4.2. The complementary large-sieve regime is
closed below.
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
Corollary 2.9 estimate. `FactorialLargeSieveMaximal` chooses
`k=⌊log(x+1)/(2 log a)⌋`, verifies the product and selection conditions,
proves a uniform square-root fixed-fiber estimate, reassembles only nonempty
fibers, and absorbs both subpolynomial parameter budgets. Thus the
nontrivial Theorem 1.9 upper count follows from Lemma 4.2.
`FactorialOneTermAsymptotics` proves exponential growth of `s(a!)`, covers
the literal one-term values by `O(log x)·⌊√x⌋` representations, and combines
the upper and square-family lower bounds. The full `TaoTheorem19Conclusion`
is therefore compiled from Lemma 4.2, and hence from Theorem 2.5 plus
Proposition 2.3(ii) or the pinned BHP source contract.
The compiled Lemma 4.2 contract is propagated to Theorem 1.10 through the
explicit natural gap budget `⌈exp((log x)^(3/4))⌉`, proved both to bound every
factorial-square triple tail and to be `x^o(1)`. Unrestricted
Sylvester--Schur and the Hanson primorial theorem now discharge the required
Erdős--Selfridge square specialization internally. Thus its remaining inputs
are directly Theorem 2.5 and the analytic BHP theorem; Theorem 1.9 is supplied
internally by the new closure above.
`BadIntervals` now starts the independent Theorem 1.7 branch with the exact
arithmetic core of Tao's Lemma 6.1. It proves `H≤N` for every non-singleton
bad interval without an external hypothesis and proves unconditionally that
every interval element is nonprime. From the explicitly isolated
Sylvester--Schur contract it then obtains the largest prime `p₀>H`, a literal
interval witness `p₀²m` with smooth cofactor, and `p₀`-smoothness of every
interval element. The admissible dyadic witness yields the exact rounded
bounds `N<x≤4N+1` and `p₀²m≤2x`.
`NormalizedBadIntervals` proves the corrected exact core of Lemma 6.2. The
largest power of two below `(H+3)/2` satisfies `2≤H'≤H<4H'`; one of the two
subintervals with endpoint `p₀²m` is contained in the parent and remains bad
with the same largest prime. Its exact inherited scale is `x≤4N'+1` and
`N'+H'≤2x`. The module intentionally does not claim that the child meets the
identical `[x/2,x]` window, because containment does not preserve that
condition without an additional argument.
`BadIntervalMaximal` packages both interval families as finite index sets and
finite unions. It proves that every point in the admissible union belongs to a
four-length enlargement whose intersection with the normalized union has
exact lattice density at least `1/10`. A greedy maximal-length selection gives
pairwise disjoint intervals whose threefold enlargements cover the original
family, proving the finite one-dimensional weak-`(1,1)` inequality and the
final bound `#admissibleUnion≤30·#normalizedUnion`.
`TypicalBadIntervals` gives exact cutoff-parametrized versions of Definitions
6.3--6.4. It encodes the ordered 1000-prime factorization, smooth remainder,
literal typical/non-typical split, `p₀<squareThreshold`, and the source bound
`m'≤2x/(p₀²p₁⋯p₁₀₀₀)`. `NonTypicalBadIntervals` closes the finite part of the
large-square failure branch in Proposition 6.5: every affected short interval
lies in an explicit neighborhood union bounded by
`(2L+1)∑_{D≤d≤2x}⌊2x/d²⌋`. A telescoping reciprocal-square estimate closes
this further to `(2L+1)(2x)/(D-1)`. `BadIntervalSourceScales` substitutes
`L=⌈(log x)^20⌉₊` and `D=⌈z(x)^3⌉₊`, proves the needed growth and logarithmic
absorption, and derives `#exceptional≤24x/z(x)^(5/2)` eventually. Thus the
actual finite union of short normalized intervals failing condition (ii) is
covered and satisfies the weak source alternative with explicit `δ=1/2`;
`BadIntervalLongSieve` starts condition (i) at the exact source residue level.
It proves the `H` forbidden start classes are distinct modulo every prime
`p₀<p≤2p₀`, derives their avoidance from normalized-interval smoothness, and
feeds the resulting literal restrictions through the existing tensor
Corollary 2.9. The actual fixed-`(p₀,H)` interval union satisfies the compiled
weighted large-sieve bound. Its ambient-start maximal degree and eventual PNT
range are compiled. `BadIntervalCofactorSieve` implements the literal source
cofactor budget `2x/p₀²`: both endpoint orientations are transported to `H`
distinct affine restrictions on `m`, smoothness supplies their avoidance, and
their exact tensor ratios feed the global sieve. The two survivor interval
covers recombine into a fixed-fiber source bound with explicit factor `16`,
specialized to the floor-defined degree and eventual PNT range. Source-range
optimization now extracts `H/(8k log(2p₀))` as an exact lower bound for the
sieve base and proves the paper's `H^(0.9k)` fixed-fiber inequality from
`8k log(2p₀)≤H^(1/10)`. Exact floor maximality further gives
`2x<(2p₀)^(2k+4)` and `log(2x)/log(2p₀)<2k+4`; the quarter-bound is compiled
with its necessary finite hypothesis `k≥4`. Under the stronger denominator
absorption `8k log(2p₀)≤H^(3/50)`, the leading `H` is removed and the fiber is
bounded by `16(⌊2x/p₀²⌋+1)H^(-0.9(k-1))`, then by the canonical exponential
degree-decay term. The literal long cutoff discharges the denominator
comparison eventually. The complementary `k<4` branch forces
`2x<(2p₀)^10`; the unsieved cofactor cover yields `4096x^(9/10)` for the whole
fiber. `BadIntervalLongSaddle` performs the exact prime-scale AM--GM step. The
literal long cutoff supplies `(9/2)log x log₂x` in the saddle numerator, so the
canonical `k≥4` fixed fiber is eventually at most
`128x/(p₀z(x)^6)`. The corrected full source range `k≥2` uses the valid
eighth-comparison and a `22/25` absorption, retaining the uniform bound
`128x/(p₀z(x)^4)`. Under the exact source upper scale `p₀^20≤x^3`, nonempty
fibers supply the square inequality and the long range supplies the degree,
PNT, and large-budget hypotheses automatically. `BadIntervalLongSum` performs
the finite dyadic-length and moderate-prime aggregation, majorizes the prime
sum by the harmonic number, absorbs both logarithmic losses into `z(x)`, and
proves the actual long moderate-prime failure-union bound `x/z(x)^3`
eventually. `BadIntervalLargePrimeSum` treats Tao's earlier large-`p₀` branch
under the ceiling-rounded `H<x^(7/50)` cutoff. Its unsieved `8Hx/p₀²` fiber
bound and reciprocal-square tail prove `#union≤x^(199/200)` eventually, with
exact bridges from `H^50<x^7` and `p₀^20>x^3`.
`BadIntervalSmoothBranches` treats the easy small-`p₀` branch: the actual
normalized interval union with `p₀≤y` embeds in the `y`-smooth numbers up to
`2x`. The floored cutoff `⌊z(x)^β⌋` is proved to lie in the critical regime,
so the union is eventually at most `2x/z(x)^(1/β-ε)`; the concrete choice
`β=2/5`, `ε=1/10` yields `2x/z(x)^(12/5)`.
The module additionally covers every fixed later `(p₀,H)` fiber by its two
smooth-cofactor endpoint orientations and proves
`#fiber≤2H Ψ(⌊2x/p₀²⌋,p₀)`. The actual short union is aggregated over its
dyadic lengths and a concrete 60-cell prime-exponent grid. For
`z(2x)^(6/5)<p₀≤z(2x)^3`, the smooth-number exponents retain a fixed margin
above two; all grid, length, and dilation losses are absorbed in the final
bound `#union≤x/z(x)^(2+1/800)`.
The exact slow-variation limit `log z(2x)/log z(x)→1` now transfers the
literal source range `z(x)^(5/4)<p₀≤⌈z(x)^3⌉` into that grid, so the
same bound holds for this actual source-defined short interval union.
`BadIntervalLargeLength`
closes the complementary `H≥x^(7/50)` prime-gap branch: `41/300` is a fixed
spare exponent above `2/15`, one greedy disjoint family controls all lengths,
the corresponding real endpoint blocks lie in Tao's literal Proposition
2.3(iii) set at scale `2x`, and the actual union has a fixed power saving.
The constructive arithmetic core of the deficient-large-factor branch is
also proved: at least 1000 multiplicity-counted large prime factors produce
the ordered `TypicalPrimeAnatomy` and smooth remainder exactly. A canonical
filtered factorization also gives `m=p₁⋯pⱼ m'` with `j<1000`, bounded
large factors, and lower-cutoff-smooth `m'` for every surviving condition-(iii)
failure. These packets now generate an explicit finite product/remainder
cover, and the actual deficient interval union is reduced to
`4L ∑_{p₀} ∑_a Ψ((2x/p₀²)/a,y)`, with `a` ranging over products of fewer
than 1000 primes between `y` and `p₀`. An explicit finite list universe expands
this further into a sum over the individual multiplicity-retaining factor
lists. The uniform critical estimate at `y=⌊z(x)^(9/10)⌋` keeps the exact
weight `1/(p₀²∏q)`; the outer reciprocal-square tail, elementary harmonic
bound, and fixed polylogarithmic absorption then prove the actual deficient
central union bound `#union≤x/z(x)^(2+1/200)` eventually on
`z(x)^(9/10)<p₀≤z(x)^(11/10)`. A fine 600-cell mesh and exact source-to-
cofactor cutoff transfer additionally prove
`#union≤x/z(x)^(2+1/1000)` on the actual fixed outside-central windows
`z(x)^(2/5)<p₀≤z(x)^(9/10)` and
`z(x)^(11/10)<p₀≤z(x)^(5/4)`. `BadIntervalProposition65` then assembles the
actual concrete non-typical family into eight named failure unions, converts
the fixed-power branches using `log z/log x→0`, and absorbs the finite sum to
obtain `#union≤x/z(x)^(2+1/4000)` eventually.
`BadIntervalSlowCutoff` supplies the moving version. For `d=n+10`, exact
lower-floor and upper-ceiling cutoffs at exponents `1-2/d` and `1+2/d` are
covered by moving low/high meshes and the full deficient interval. The fixed
row bound is `#union≤x/z(x)^(2+1/(128d²))`. A countable diagonal then selects
`q(x)→∞`, proves both rounded cutoff logarithms have ratio one to `log z(x)`,
and obtains `#union≤x/z(x)^2` eventually for the selected actual non-typical
family. The source-facing Proposition 6.5 cutoff diagonal is therefore
compiled and axiom-audited.
`BadIntervalSlowCutoffLogSaving` retains the stronger row margin and pays for
Lemma 1.6(i)'s lower estimate, so the same selector gives, for every fixed
`epsilon>0`, `#union≤badOneTermCount(x)/log(x)^(1-epsilon)` eventually.
`BadIntervalRandomModel` then instantiates Proposition 6.6's random prime
tuple as a genuine finite product probability measure. Every coordinate is
uniform on the exact prime band `[Pⱼ,2Pⱼ)`, its pushforward mass and support
are proved, and all 1001 projections are mutually independent. The exact
source tuple product, divisibility indicators, typical event, and its
probability are ready for the anti-sieve moment estimates.
`BadIntervalAntiSieve` closes the exceptional `p∣l` branch pointwise: its
weight is at most `H log H`, hence eventually `H log z(x)` throughout the
source length range, so the large event is empty and its probability is zero.
`BadIntervalSmallPrimeMoment` defines the exact small-prime cutoff
`⌊z(x)^(1/100)⌋`, the `p∤l` pairs, and the source fiftieth moment. Its final
theorem expands that expectation exactly over ordered 50-tuples as logarithmic
weights times joint divisibility probabilities, exposing the next character-
sum obligation without hiding it behind an assumption. It also defines the
tuple lcm and proves the exact CRT precursor: the joint event is either empty
or precisely one primitive residue-class fiber modulo that lcm.
`BadIntervalLargePrimeMoment` supplies the parallel large-prime probability
layer: the literal unweighted sum over `1≤l<H`, exact mean/second-moment and
double-covariance variance identities, and the diagonal/same-prime reduction.
Under `H≤lowerPrime`, distinct shifts with one common prime have empty joint
event and nonpositive covariance, leaving only the mean and distinct-prime
covariances for the analytic Propositions 6.7--6.8 estimates.
`BadIntervalLargePrimeCharacter` supplies the next exact step: single events
are primitive fibers modulo `p`, distinct-prime joint events are primitive
fibers modulo `pp'`, and both probabilities inherit the compiled
all-character 1000th-moment bound at those exact moduli.
`BadIntervalLargePrimeExceptional` bounds exceptional prime conductors by the
aggregate character count with exponent `2/125`. The common-factor aggregate,
uniform self-improving cardinal theorem, and selector diagonalization preserve
one constant while the fixed prime varies. `BadIntervalLargePrimePairs` then
  gives the corresponding uniform `pp'` exceptional-partner bound needed by
  Proposition 6.8, conditional only on explicit Burgess.
  `BadIntervalPrincipalCharacter` isolates the principal character before the
  1000-coordinate AM--GM step. Its expectation is exactly the tuple-product
  coprimality probability, and the one-prime and two-prime deficits are bounded
  by explicit coordinate-collision union bounds. A fixed prime divides at most
  one member of a dyadic prime band, so every coordinate costs at most the
  reciprocal of the exact band cardinality. The remaining improved-probability
  error is the nonprincipal character moment.
  `BadIntervalLargePrimeNonprincipal` closes this term for prime moduli. It
  identifies all nonprincipal characters modulo `p` as primitive, unions the
  exceptional conductors over the 1000 ordinary coordinate scales, proves the
  union loses at most a fixed factor 1000, and bounds the surviving moment by
  `φ(p) * ∑ P_j^(-8)`. The resulting theorem directly bounds the probability
  deviation from `1/φ(p)` by that error plus the collision term.
  `BadIntervalLargePrimeProductNonprincipal` proves the exact product-modulus
  conductor reduction under the stated coprime-band condition. The fixed
  conductor fibers are bounded by their unexceptional errors, the totient
  divisor identity sums these to `pp'`, and the result feeds the direct
  deviation from `1/φ(pp')`. Removing band separation at the possible sampled
  points `p,p'` is completed by `BadIntervalLargePrimeProductCollision`. It
  proves that the ambient and primitive averages differ by at most `4/card`,
  regroups primitive counterparts without a coprimality hypothesis, and carries
  the correction through the 1000th power. The final product deviation theorem
  is therefore unconditional in the band position.
  `BadIntervalLargePrimeCrude` supplies the first direct-counting primitive:
  every residue class modulo positive `q` contains at most `⌊2Z/q⌋+1` members
  of a dyadic prime band, with the normalized cardinal inequality exposed for
  the forthcoming frozen-coordinate probability argument.
  `BadIntervalPrimeTupleUniform` proves the complementary measure-theoretic
  bridge: the Cartesian support has mass one, all supported tuples have the
  same inverse-product atom, and arbitrary event probabilities are exact
  supported-cardinality ratios.
  `BadIntervalPrimeTupleFiber` completes the finite coordinate-freezing
  bridge. Its frozen support has exactly the full-support cardinality divided
  by the missing band, so uniform fibers give `M/card`; pairwise residue
  rigidity gives `(⌊2P/q⌋+1)/card`. It also factors the literal source
  product by any ordinary coordinate. A coprime/noncoprime split plus the
  existing collision-union estimates then proves unconditional single- and
  joint-event crude bounds, with one and two collision sums respectively.
  `BadIntervalPrimeTupleMultiFiber` generalizes freezing to arbitrary finite
  coordinate sets, with exact cancellation by the product of their band
  cardinalities and a general product-residue/multiplicity estimate. Prime
  factorization bounds two-coordinate product fibers by `2` and
  three-coordinate fibers by `6`. Thus the literal finite forms of
  Propositions 6.7(i) and 6.8(i) have numerators
  `2(⌊4P₁P₂/p⌋+1)` and `6(⌊8P₁P₂P₃/(pp')⌋+1)`, respectively; their event
  hypotheses automatically imply the needed cofactor coprimality.
  `BadIntervalLargePrimeCrudeNormalize` absorbs the terminal floor `+1` and
  cancels the selected coordinate scales under
  `P_j≤L·#taoDyadicPrimeBand(P_j)`. It yields the exact source-shaped estimates
  `16L²/p` and `96L³/(pp')`; the next module supplies the common PNT scale.
  `BadIntervalLargePrimeCrudeSource` supplies that instantiation for the exact
  source family contract `log(P_j)/log(z)→1` with divergent coordinate scales.
  Uniformly over all 1001 coordinates it proves
  `P_j≤4log(z)#taoDyadicPrimeBand(P_j)` and band nonemptiness, and concludes
  `256log²(z)/p` and `6144log³(z)/(pp')` eventually. Dyadic aggregation remains.
  `BadIntervalLargePrimeProbabilityBounds` transfers the improved prime and
  product-modulus character estimates to the literal single and joint events.
  It gives the absolute marginal deviation, handles empty-event upper bounds,
  and derives the explicit distinct-prime covariance error after exact
  totient-main-term cancellation. Dyadic aggregation remains.
  `BadIntervalLargePrimeAggregation` performs the exact finite partition on
  the literal anti-sieve index set. Improved single and pair terms are summed
  separately from exceptional terms carrying explicit crude majorants, then
  combined with the diagonal variance reduction. Analytic cardinality and
  source-scale summation remain.
  `BadIntervalLargePrimeExceptionalPartition` proves that the product
  predicate has only three conductor cases, `p`, `p'`, and `pp'`. A bad pair
  is therefore covered by the two exceptional-prime sets or the common-factor
  exceptional-partner union, whose 1000-scale cardinality is bounded exactly.
  `BadIntervalLargePrimeBlockSum` supplies the finite dyadic first-moment
  estimate: exact band identification, the reciprocal-totient main sum with
  eventual `4/log R` PNT bound, and the separate uniform improved-error and
  exceptional-cardinality times crude-error contributions.
  `BadIntervalLargePrimeCovarianceBlockSum` gives the exact two-band analogue
  for ordered distinct-prime covariances. It preserves the literal
  `(H-1)^2` shift multiplicity and separates the whole band-product times a
  uniform improved error from the exceptional ordered-pair cardinality times
  a supplied crude joint bound. Burgess cardinality insertion and dyadic
  scale summation remain.
  `BadIntervalLargePrimeExceptionalPairCard` converts its exceptional-pair
  parameter into the exact three-family count from the source: bad first
  endpoints, bad second endpoints, and common-factor exceptional partners.
  `BadIntervalLargePrimeErrorNormalize` exposes the three coordinate
  aggregates in the literal errors, while `BadIntervalLargePrimeErrorSource`
  uses the simultaneous `P_j=z^(1+o(1))` contract and PNT to bound them and
  obtain explicit one-prime, joint, and covariance source envelopes.
  `BadIntervalLargePrimeErrorPower` absorbs all fixed logarithmic powers,
  packages the source-range dyadic selector, and proves both envelope and
  literal-error bounds of the exact forms `3R^-1.001` and
  `C R^-1.001 S^-1` (joint and ordered covariance). Burgess insertion and
  dyadic scale summation remain. `BadIntervalLargePrimeAdaptiveExceptional`
  supplies the endpoint part of that insertion with the necessary threshold
  `max(P_j^-0.008,R^-0.01)`: the uniform exceptional squared moment and finite
  Chebyshev give one `O(R^0.02)` bound after unioning all 1000 coordinates.
  This avoids the invalid conversion of the fixed `O(P_j^0.016)` count at
  the smallest admissible modulus bands. The cofactor embedding now preserves
  the full squared moment exactly, its Burgess bound is pointwise uniform in
  the fixed prime and cofactor set, and the same argument gives
  `O(S^0.02)` adaptive partners. `BadIntervalLargePrimeAdaptiveError`
  supplies the missing consumer interface: outside those sets the exact
  1000th moments feed the one- and two-prime residue fibers, the additional
  tail is explicitly `1000R^-10`, and adaptive one-prime, joint, and ordered
  covariance errors retain the required source powers.
  `BadIntervalLargePrimeAdaptivePartition` proves the exact mixed pair
  partition needed by the counted families, using scale `R` for conductor
  `p` and scale `S` for conductors `p'` and `pp'`; its mixed product moment
  and literal joint-probability bound compile, and the corresponding joint
  and covariance errors retain ordered `R^-1.001 S^-1` decay.
  `BadIntervalLargePrimeAdaptiveBlockSum` now supplies the exact adaptive
  one-band and two-band consumers and reduces its exceptional pair finset to
  the two endpoint counts plus adaptive partner fibers. Burgess-cardinality
  insertion is completed by `BadIntervalLargePrimeAdaptiveSource`, including
  the exact pair-count shape
  `R^0.02·#band(S)+#band(R)·S^0.02` and the normalized improved errors in both
  block sums. `BadIntervalLargePrimeAdaptiveGeometry` supplies uniform crude
  specialization and proves the source conductor/partner ranges automatically;
  `BadIntervalLargePrimeAdaptiveComplete` inserts these facts into both full
  blocks. `BadIntervalLargePrimeDyadicScales` partitions the literal source
  prime range into disjoint dyadic slices with at most `4 log z` scales, and
  `BadIntervalLargePrimeAdaptiveUniform` uniformizes the Burgess constants and
  sums them. The resulting literal bounds are mean `≤2000000H`, distinct-prime
  covariance sum `≤H`, and variance `≤2000001H`, conditional on explicit
  Burgess.
  `BadIntervalCharacterExpansion` proves the exact normalized all-character
orthogonality identity for such fibers and integrates it on the tuple measure.
Mutual independence factors the full character expectation into its 1001
coordinate expectations; these are computed exactly as normalized finite
dyadic prime-character averages. Norm-one bounds remove the residual and
distinguished squared coordinate, and a finite weak AM--GM theorem gives the
literal source reduction to the sum, over all characters and the remaining
1000 coordinates, of 1000th powers of those prime averages. The tuple modulus
satisfies the exact estimate `lcm≤2^50 φ(lcm)`, so the fiber coefficient becomes
`2^50/lcm`; this is inserted into the complete fiftieth-moment sum, reordered
by coordinate, and pigeonholed with the literal factor `1000`.
`PrimeCharacterSums` fixes `s_Z(χ)`, the exceptional threshold
`Z^(-1/125)=Z^(-0.008)`, and the finite exceptional/unexceptional partition of
primitive nonprincipal characters. It proves the exact unexceptional bound
`φ(q)Z^(-8)` and reduces the exceptional 1000th moment to the squared moment
used by Lemma 5.1. Scale separation proves every averaged prime coprime to the
tuple modulus, justifying exact replacement by primitive counterparts. The
principal character contributes `1`; fixed-conductor fibers inject into the
primitive nonprincipal characters, and the complete ambient moment is bounded
by a divisor sum of exceptional squares and `φ(d)Z^(-8)` errors. Lemma 5.1's
consumer is inserted termwise into the ordered tuple sum and then into the
complete fiftieth moment after coordinate pigeonholing. Proving the resulting
explicit finite sum now continues in `SmallPrimeMertens`: the lcm is exactly
the product of the distinct selected-prime support, support multiplicities sum
to 50, and the tuple coefficient splits into one `log p/p` factor per support
prime and repeated logarithms of exact total exponent `50-#support`. The
proved bound `weightedPrimeLogSum Y ≤ log 4 * (2 + log Y)` gives an explicit
pointwise estimate, while every fixed ordered prime tuple has at most `H^50`
admissible shift tuples and a generic fiberwise theorem removes those shifts.
Exact support regrouping, a `50^50` support-fiber bound, and the proved
elementary-symmetric inequality now sum every ordered-prime equality pattern,
yielding an explicit `H^50 O(log(cutoff)^50)` coefficient bound. An exact
three-way conductor split isolates the exceptional squared moments; the
principal term obeys the Mertens bound and the `φ(d)P^-8` term is closed via
the totient-divisor identity and Chebyshev theta. `ExceptionalCharacterBHM`
proves the exact finite weighted Bombieri--Halász--Montgomery inequality used
as Lemma 5.3, reduces its Schur hypotheses to one Hermitian Gram-row bound,
recovers the prime sum from the weighted prime indicator, splits that row into
its diagonal and `J-1` off-diagonal terms, divides by the exact prime-band
cardinality to recover `s_Z`, and proves the exact threshold Markov inequality
`J Z^(-2/125) ≤ ∑|s_Z|²`. The Burgess estimate and the
construction/bound for the fundamental-lemma sieve weights remain before
Lemma 5.1 and its exceptional-term application can close.
`FundamentalSieveWeights` records the literal truncated divisor sum from Lemma
5.4. It proves `ν(p)=1` throughout the dyadic prime band above the level, the
exact identity `Σ_{1≤n≤X}ν(n)=Σ_{d≤R}⌊X/d⌋λ_d`, and the elementary coefficient
`ℓ¹` bound. It also proves the exact error bound
`|Σν-XΣλ_d/d|≤R` and transfers any coefficient main-mass bound to
`Σν≤XB+R`. Only the fundamental-lemma coefficient construction, squarefree
support, nonnegativity, and logarithmic main-mass estimate remain on the sieve
side.
`SelbergPrimeWeights` now provides a fully proved real-valued alternative from
the frozen Selberg-sieve library. Its upper-Möbius coefficients are supported
at level `R`, give a globally nonnegative divisor weight equal to one on primes
above `R`, and have main mass at most `2/log R`. The coefficient estimate
`3^ω(d)` yields the explicit total-mass bound
`2X/log R+R(1+log R)^3`. This suffices for the intended power separation, but
is explicitly not identified with Tao's `{−1,0,1}` Rosser weights.
`ExceptionalCharacterSelberg` carries that concrete weight through the full
finite BHM reduction. It proves the exact divisor expansion, reindexes the
restricted sums as ordinary prefixes, uses multiplicativity and norm-one
control to remove the divisor factor, closes the diagonal, and produces the
normalized second-moment estimate with only a uniform unshifted Burgess
prefix bound remaining.
`ExceptionalCharacterFamilies` supplies the dependent primitive `q₁q₂`
family behind that bound. It proves the exact common-factor lcm formula, the
pair level's squarefreeness and `Z^3.09` bound, and the equality between the
raw conjugated correlation and a single quotient Dirichlet-character value,
including the nonunit cases. `ExceptionalCharacterBurgess` then narrows the
terminal hypothesis to the actual sieve prefixes `⌊(2Z-1)/d⌋` and exposes the
source-shaped proposition-valued cubefree Burgess statement with saving
`0.0163`, fixed cutoff, and range `q≤H^3.1`. It also defines cube-free
literally, proves squarefree periods satisfy it, and encodes the cited `r=7`
estimate as `A H^(6/7)q^(2/49+ε')`. The fixed choice
`ε'=1/2000000` is proved to imply the decimal target throughout the required
range. Exact Möbius inversion then expresses every changed-level prefix as a
divisor sum of primitive prefixes; the frozen divisor-epsilon theorem absorbs
the divisor-count loss after splitting epsilon in half. Thus only the
primitive cube-free estimate at `ε'=1/4000000` remains analytic. Complete
periods are now proved to vanish, arbitrary prefixes are reduced exactly
modulo `q`, and the trivial `|S(H)|≤H` estimate is compiled. Consequently the
analytic input is needed only on the core range `q^(2/7+7ε')<H<q`,
equivalently `q^(2/49+ε')<H^(1/7)`.
The PDF and TeX source of arXiv `2511.17778v2` are pinned as auxiliary
architecture. `BurgessMoment` implements the first reduction: it expands the
shifted complete `2r`-moment into ordered tuple correlations, rewrites each as
a complete quotient-character sum, proves the diagonal coding bound
`#degenerate≤r^(2r)B^r`, and obtains
`moment≤r^(2r)B^r q+B^(2r)W`, including the exact `r=7` fourteenth-moment
specialization. The nondegenerate composite Weil input and finite gcd-tuple
counting were the remaining stages of this analytic core. The source
coefficient boundary is now literal: `burgessTupleDifferenceProduct` is
`A_j=∏_{i≠j}(b_i-b_j)`, and exact fiber-cardinality summation proves every
nondegenerate tuple has some `A_j≠0`. `burgessTupleGcdWeight` is the relaxed
sum over `gcd(|A_j|,q)`, while
`TaoPrimitiveCubefreeBurgessCompleteWeilBound` states the remaining factor
`(4r)^ω(q)√q`. The checked general and `r=7` theorems reduce the complete
moment directly to that predicate and the visible gcd-weight sum.
The finite gcd-tuple stage is now proved. The initial-interval identity counts
multiples of every divisor to bound `∑gcd(n,q)` by `Hτ(q)`; a two-sided
centered estimate, gcd submultiplicativity for `A_j`, and exact
independent-coordinate factorization yield
`∑_uv burgessTupleGcdWeight q uv≤2rB(2Bτ(q))^(2r-1)`. The general and `r=7`
moment theorems consume this result, leaving only the composite Weil
predicate as the analytic input in the moment stage.
At `r=7`, the factors `28^ω(q)` and `τ(q)^13` are now absorbed by the frozen
prime-factor and divisor epsilon bounds. Thus for every `ε>0`, that predicate
alone yields a positive `C_ε` and
`moment≤7^14B^7q+C_εB^14q^(1/2+ε)`.
`BurgessWeilCRT` proves the exact coprime-product reduction for the remaining
Weil predicate. It constructs the canonical left/right CRT characters,
factors every tuple correlation, proves multiplicativity of the composite
factor and of each fixed coefficient-gcd contribution, and assembles local
bounds with one common witness into the relaxed global gcd-weight estimate.
It also proves the exact changed-level product identity and uses conductor
factorization to show that a primitive global character has primitive left
and right CRT characters. `BurgessWeilIteration` closes cube-free iteration:
a least-prime-factor split gives coprime `p^k n` with
`k∈{1,2}` and smaller `n`; strong induction preserves a common nonzero
coefficient and derives the full relaxed composite predicate. Only the local
fixed-coefficient estimates modulo `p` and `p^2` remain. The local
coefficient-divisible branches are now discharged: when `p ∣ |A_j|`, the
trivial complete-correlation bound is already dominated by the required gcd
factor at both levels. The remaining nontrivial boundary is split into
separately stated prime and prime-square predicates with `gcd(|A_j|,p)=1`,
and their exact recombination through the prime-power predicate to the
composite bound is proved.
`BurgessWeilPrimeSquare` closes the second predicate by an exact fiber
decomposition modulo `p^2`. Singular base fibers vanish and occupy at most
`2r` bases. The restriction of a primitive character to the principal units
`1+pt` is constructed as a nontrivial additive character. For the reduced
numerator and denominator polynomials `F,G`, exact first-order product
identities give phase `(F'/F-G'/G)t` and cancel all nonstationary fibers.
Coprimality of `A_j` proves `F'G-FG'` nonzero at a tagged simple root, and its
at most `2r` roots support the sum. This proves the target local `4rp` bound;
only the primitive prime-modulus Weil estimate remains.
`BurgessWeilPrime` sharpens that final estimate to
`TaoPrimeLinearQuotientWeilBound`. It rewrites the prime correlation exactly
as a complete multiplicative-character sum for two tagged products of linear
factors, proves the selected reduced root unique from `gcd(|A_j|,p)=1`, and
proves primitive prime-level characters nontrivial. The checked implication
from its `4r√p` conclusion reaches the prime local predicate and, through the
finished prime-square and CRT machinery, the full cube-free composite
predicate. The normalized finite-field Weil theorem itself remains open.
`BurgessWeilPrimePolynomial` supplies the remaining elementary algebra around
that theorem. The quotient sum is exactly the character sum of the numerator
times the denominator to exponent `orderOf χ-1`. At the uniquely tagged
root its multiplicity is `1` or `orderOf χ-1`, so the polynomial is not an
order-th power. It splits and has at most `2r` distinct roots.
`BurgessWeilPrimeLowRoots` proves the one-root sum is zero and converts the
two-root sum exactly to a Jacobi sum, whose norm is at most `√p`. The sole open
input is now `TaoPrimeSplitPolynomialWeilBoundThreeRootsOrMore`: the standard
split-polynomial bound restricted to at least three distinct roots.
`BurgessWeilPrimeActiveRoots` separates roots whose multiplicities vanish
modulo `orderOf χ`. They contribute one away from their own zeros, and the
deleted zero locations have total norm cost at most their cardinality. This
cost is absorbed by the original target, so the actual residual is
`TaoPrimeSplitPolynomialWeilBoundThreeActiveRootsOrMore`: at least three active
root multiplicities.
`BurgessWeilPrimeThreeRoots` proves the exactly-three case for the cleared
Burgess polynomial. Its exact degree `r * orderOf χ` forces the active
multiplicity sum to be divisible by the character order. A fractional-linear
reindexing sends one root to infinity and reduces the sum to a two-root Jacobi
sum with one deleted point, yielding `√p+1`; the target absorbs this and all
inactive corrections. The sole prime input actually needed by Burgess is now
`TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore`.
`BurgessWeilPrimeLargeCharacteristic` proves the trivial complete-sum bound
`p` and absorbs it into `2D√p` for `p ≤ 4D²`. The residual four-active-root
input may therefore also assume the strict inequality `4D² < p`.
`BurgessWeilPrimeFourRoots` performs the exact four-root Möbius reduction.
One root is sent to infinity, the denominator characters cancel by total
degree divisibility, and the remaining expression is a canonical three-point
hypergeometric sum minus one deleted value. A `2√p` bound for that canonical
sum formally gives the full exactly-four-active-root polynomial estimate.
Thus the generic large-characteristic residual is restricted to at least five
active roots, with the canonical hypergeometric estimate exposed separately.
`BurgessWeilPrimeSourceResidual` tightens the production contract to the
literal family `primeLinearOrderPolynomial p r χ b`. The bridge establishes
all structural hypotheses internally, disposes of small characteristic and
active-root counts below five, and uses the canonical four-root estimate only
when `p > 64`. These two source-specific analytic inputs still imply the full
cube-free composite endpoint.
The canonical four-root predicate is stated only for powers of the ambient
Burgess character. Each of its three exponents is reduced modulo and bounded
strictly below `orderOf χ`; a checked transport theorem recovers arbitrary
active-root multiplicities exactly.
Scaling by the first nonzero marked point is also formalized exactly. It puts
the finite roots in Legendre form `0,1,t` and reduces the analytic contract to
one parameter `t ≠ 0,1`, up to a character-valued constant of norm at most
one.
`ExceptionalCharacterScales`
defines the canonical `R=⌊Z^0.0001⌋`, proves every requested prefix eventually
lies above the cutoff and uniformly meets the period range, and uses Bertrand
to discharge band nonemptiness. Therefore the family BHM estimate now awaits
only the analytic Burgess target. `ExceptionalCharacterNormalization` proves
that the exact half-open band cardinality is `π′(2Z)-π′(Z)`, is asymptotic to
`Z/log Z`, and is eventually at least `Z/(2 log Z)`.
`ExceptionalCharacterAbsorption` proves the Selberg main and floor-error terms
are `O(Z/log Z)` and uses
`0.016+0.0001+(1-0.0163)=1-0.0002` to make the off-diagonal term
`o(Z/log Z)` whenever `J≤A Z^0.016`. The normalized moment constant is
therefore independent of `A`. Truncating an arbitrary family at
`⌊A Z^0.016⌋` and applying the exceptional threshold closes Tao's
self-improving bootstrap. Conditional only on explicit Burgess, the final
theorem gives both `J≪Z^0.016` and the bounded squared moment. Only the
analytic Burgess proof remains in Lemma 5.1.
`ExceptionalCharacterFixedLevel` then specializes the heterogeneous theorem
to the literal fixed-conductor exceptional finsets by taking `q₂=1`. It proves
exact cardinality and squared-sum transport and records the source's full
`O(λ⁻²)` tail statement, conditional only on explicit Burgess.
`ExceptionalCharacterAggregate` proves the needed cross-conductor uniqueness:
primitive characters with equal lcm lifts have equal levels and are equal
after transport. It then maps the dependent sigma of all exceptional
characters over an arbitrary admissible finite conductor set into one
automatically separated `q₁=1` family. Total cardinality and the full double
squared-moment sum are exact, so explicit Burgess supplies one uniform bound
for the whole conductor set rather than a non-uniform bound conductor by
conductor.
`SmallPrimeExceptionalConductors` instantiates the finite conductor universe
from the actual tuple expansion. Tuple moduli and all their divisor conductors
are squarefree, and the entire union lies below the explicit `cutoff^50`
bound. The rounded inequality `cutoff^50<⌊z^(9/10)⌋` and its monotone
Burgess-range consequence are proved eventually. The maximal finite set of
all admissible squarefree conductors supplies one eventual moment constant
for every admissible subset and all 1001 selectors. Pointwise insertion and
the exact logarithmic-lcm Mertens coefficient absorb
`taoSmallPrimeExceptionalConductorSum` into the principal majorant. The scale
bound also gives `P_j⁻⁸ cutoff⁵⁰≤1`, which absorbs the explicit totient error.
Thus the entire literal small-prime fiftieth moment is bounded by a fixed
multiple of the principal majorant conditional only on Burgess.
`BadIntervalProbabilityNormalization` supplies the exact probabilistic
closure. Integrability of the fiftieth power and finite Markov give the
small-prime source tail at threshold `H log(z)^2/(8 log₂(x))`; the exact
large-prime variance identity and Chebyshev give the tail above its mean at
threshold `H log(z)/(8 log₂(x))`. With the zero-measure exceptional branch,
their union has the explicit sum of these two tail bounds.
`BadIntervalTypicalAntiSieve` proves the deterministic complement. It
partitions every squarefree shift component's logarithmic prime weight among
the three branches, obtains the required lower mass from square avoidance and
the comparable-scale identity, and proves the one-eighth scalar gap. Hence
every typical tuple lies in the union eventually. Conditional only on
`TaoExplicitCubefreeBurgessBound`, the final theorem gives a constant `B>0`
such that
`Pr(typical) ≤ B(8 log₂(x))^50/(H log(z)^2)` eventually. This is the compiled
source interpretation of Proposition 6.6's
`O(1/(H log(z)^(2-o(1))))`. `BadIntervalProbabilityUniform` strengthens the
quantifier order to one `B` chosen before the eventual ambient scale and then
simultaneously valid for every positive admissible `H` and every remainder
`m'`. It also proves that the typical probability is exactly its finite
supported-tuple cardinality divided by the product of the 1001 band
cardinalities, and exports the corresponding uniform tuple-count bound.
`BadIntervalTypicalCounting` now sums that bound over the exact finite smooth
remainder family, restores the literal `Psi` factor, and sums every
power-of-two length with geometric cost at most `2`. Evaluation maps the
complete fixed-prime-scale family into `B¹ ∩ [1,2x]`; a general fiber theorem
reduces its cardinality to `badOneTermCount (2x)` times the maximum evaluation
fiber. `BadIntervalTypicalScales` constructs the moving dyadic scale grid and
orders every 1001-coordinate scale tuple. `BadIntervalTypicalEnlargement` and
`BadIntervalTypicalMultiplicity` implement Tao's doubled/quadrupled bands,
map their values into the one-term bad set at one fixed dilation, and prove
the absolute fixed-scale fiber bound `1000^1000`. `BadIntervalTypicalGlobal`
shows that the same bound survives after summing every ordered scale tuple.
Finally, `BadIntervalTypicalAssembly` compares original and enlarged prime
bands by PNT, absorbs the `8^1001` loss into an explicit factor tending to
zero, and proves that the complete global typical-tuple family is little-o of
`badOneTermCount` at the fixed enlarged endpoint, conditional on Burgess.
`BadIntervalTypicalWeighted` supplies the corresponding length-weighted
all-scale estimate. Multiplication by `2^r` cancels the `1/2^r` probability
gain, while the `O(log₂ x)` number of dyadic lengths is absorbed by the
remaining logarithmic saving. `BadIntervalTypicalUnion` constructs a
canonical injective code from every actual forward typical interval, with
tuple start exactly `N+1` and tuple length exactly `H`, into that weighted
global family. The backward modules prove the reflected `v-l` anti-sieve,
source mean/variance and uniform support bound, then repeat the weighted
assembly and construct a canonical injective code with tuple start exactly
`N+H`. The exact forward-or-backward cover therefore makes the full actual
typical union little-o of the fixed-dilation one-term count, conditional on
Burgess, with an explicit fixed logarithmic saving. `BadIntervalRecombination`
combines this with the quantitative Proposition 6.5 diagonal and the exact
factor-`30` maximal transfer. Conditional on explicit Burgess,
Lemma 1.6(ii), and the proved eventual scale-local large-prime theorem, it
proves the logarithmically saving local dyadic-window bound. It also proves the exact finite power-of-two cover that
bounds `nontrivialBadCount x` by the sum of these window cardinalities. What
follows in `BadIntervalDyadicSummation` is the exact conditional endgame. The
adjacent ratio `B¹(2^r)/B¹(2^(r+1))->1/2` gives geometric summability for the
logarithmically weighted terms; the finite prefix and `[x,2x]` endpoint
comparison then yield both clauses of `TaoTheorem17Conclusion`. That adjacent
ratio is now proved in `BadOneTermRegularVariation` from
`TaoCriticalSmoothDilationLimitConclusion`: the exact one-term sum is
concentrated on a slowly widening central prime packet, dilation by `1/2` is
uniform there, and the complementary mass is `o(B¹(x))`. The Gaussian saddle
 asymptotic target implies this dilation limit. Scale-local variants of every
 intervening reduction culminate in
 `taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess`. The sharp
 saddle asymptotic and analytic Burgess remain the two open inputs; the finite
 residual Sylvester--Schur rectangle is independent. Lemma 1.6(ii) is supplied
by that same dilation limit.
None of Theorems 1.7--1.10 is complete unconditionally or claimed. Imports from
node 74 enter only through the exact immutable snapshot under `Dependencies/`.

## Release 2.57: finite Burgess amplification

`BurgessAmplification.lean` adds the exact elementary reindexing layer between
the existing prefix target and `BurgessMoment`. Its interval sum agrees with
the established `Ioc 0 H` prefix, additive translation has two boundary
pieces of total norm at most `2K`, and multiplication by a unit turns the
affine sum into the translated interval without changing its norm. Summing
the affine identity over `1 <= b <= B` and exchanging finite sums yields the
existing complete-moment inner function `burgessShiftSum B χ` exactly.
The coprime multiplier pairs are then grouped by their residue `(N+n)/a`;
the multiplicity has the expected exact first moment, and the full affine
average is proved equal to its multiplicity-weighted shifted-character sum.

The next proof obligation is the second-moment collision bound for those
multiplicities, followed by Hölder, the fourteenth-moment bound, and
optimization of `A` and `B`. This module contains no placeholder theorem for
that still-open step.

## Release 2.58: collision identity and Hölder

The second multiplicity moment is now exactly the cardinality of
`burgessResidueCollisionPairs`. For two coprime multipliers, its defining
residue equality is equivalent to the cross-multiplied congruence, recorded
also as the membership criterion for `burgessMultiplierCollisionFiber`.
The reusable finite interpolation theorem from `VinogradovMeanValue` then
gives the exact Burgess Hölder product, including complex norm and affine-
average forms. The missing arithmetic step is now precisely the source's
upper bound on each fixed-multiplier collision fiber.

## Release 2.59: arithmetic collision fibers

`BurgessAmplification` now converts the cross-multiplied congruence into
divisibility of an integer determinant. The range condition `2*A*H <= q`
forces the difference of two determinant values to vanish in `ℤ`, and
coprime reduction then gives spacing by `a/gcd(a,c)` and `c/gcd(a,c)`.
The resulting local bounds include the symmetric source-shaped estimate
`card <= H / (max a c / gcd a c) + 1`.

The global ordered collision family is also decomposed exactly into fixed-
multiplier fibers and injected into those local fibers, yielding the complete
finite `max/gcd` sum bound. Estimating that remaining gcd sum, then carrying
the induction/error and parameter choices through to the primitive `r = 7`
core theorem, remains open.

## Release 2.60: summatory collision bound

The explicit `max/gcd` majorant is now summed unconditionally. For fixed `c`,
divisor incidence and exact multiple counting bound the upper-triangular
quotient sum by `H * c.divisors.card`. Symmetry costs a factor two. A second
finite double count proves
`sum_{c in (0,A]} c.divisors.card = sum_{d in (0,A]} A/d`, whose real cast is
at most `A * harmonic A`.

The resulting source-facing theorem bounds the residue-collision count by the
square of the coprime multiplier count plus `2*H*A*harmonic A`. The remaining
work is to execute the induction with the affine boundary error and optimize
the `r = 7` Burgess parameters.

## Release 2.61: exact pre-Hölder recursion

The amplification module now contains the real multiplicity regrouping needed
by the source, not merely a norm of the total complex affine average. For each
coprime multiplier, the exact translated-interval identity is summed over
`b`; two arbitrary shorter-interval bounds control its endpoint error. The
global theorem then proves equation (28)'s finite inequality with main term
`sum_x v_A(x)*|W_B(x)|` and error `2*sum_{a,b} E(ab)`.

The remaining recursion work is scalar: specialize `E` to the inductive
Burgess power and estimate the resulting finite power sum. Hölder, the
collision estimate, and the complete fourteenth moment are already available
for the main term.

## Release 2.62: normalized power-boundary recursion

The scalar recursion work is complete for every nonnegative power majorant.
Monotonicity replaces `E(a*b)` by `E(A*b)`, and the finite `b`-sum is bounded
by `B` copies of its endpoint. Positivity of the coprime-multiplier count and
of `B` then justifies division by the averaging denominator and cancels the
common boundary factor exactly.

The resulting theorem states
`|S(N,H)| <= M/(#A*B) + 2*C*(A*B)^alpha*Q`, with both shorter endpoint
intervals retained as hypotheses. The next main-term step is to take the
`2r`-th root of Hölder and substitute the compiled collision and moment
bounds before specializing to `r = 7`.

## Release 2.63: rooted Hölder and full pre-optimization recurrence

Positivity now converts the powered Hölder inequality into the required
reciprocal-real-power form. An abstract monotone theorem permits independent
upper bounds for its collision and moment factors. Its `r=7` specialization
inserts the harmonic collision estimate and the complete cubefree-Weil moment
estimate, producing an explicit `1/14`-power main term.

That main term is also substituted into the normalized affine recurrence.
The resulting theorem has no remaining finite-sum or Hölder placeholder: only
the complete-Weil hypothesis and the scalar parameter estimates remain. The
next package is a quantitative lower bound for coprime multipliers followed by
the integer `A,B` optimization and inductive absorption.

## Release 2.64: short coprime-multiplier density

`BurgessOptimization.lean` now supplies an exact Möbius formula for the
coprime multipliers in `(0,A]`. Comparing natural quotients with real
quotients and evaluating the complete period gives
`A*phi(q)/q - q.divisors.card <= #A`. The same result is exposed in the
`burgessCoprimeMultiplierPairs q A 1` notation used inside the collision and
recurrence theorems.

A separate corollary retains half the expected totient density as soon as the
explicit divisor error is at most half the main term. The next scalar package
also proves `q/phi(q) <= tau(q)`, reducing that hypothesis to the natural
condition `2*tau(q)^2 <= A`. It remains to establish this condition for the
rounded `A`, then carry out the `A,B` range estimates and boundary absorption.

## Release 2.65: scalar recurrence and rounded Burgess parameters

The divisor-epsilon estimate now proves eventual domination
`2*tau(q)^2 <= floor(q^eta)` for every `eta>0`. The rooted Holder numerator is
also reduced to scalar rectangle bounds and, when `A<=H`, its collision term
is compressed to `3*H*A*harmonic(A)`. The resulting normalized recurrence has
no multiplier-cardinality placeholder.

For `r=7` the module defines `B=floor(q^(1/14))` and `A=H/(K*B)`. Compiled
lemmas give the two-sided floor estimate for `B`, a half-quotient lower bound
for `A`, all shortening/no-wrap inequalities from explicit lower and upper
range hypotheses, and eventual divisor-discrepancy dominance for this actual
rounded `A`. Harmonic and totient epsilon losses, final exponent algebra, and
boundary absorption remain.

## Release 2.66: Burgess exponent normalization

The scalar file now bounds both `harmonic(A)` and `q/phi(q)` by explicit
epsilon powers of the conductor and rewrites the half-density denominator as
`2*S*(q/phi(q))/(A*B)`. At `B<=q^(1/14)`, both complete-moment terms collapse
to one `q^(3/2+epsilon)` monomial, whose fourteenth root is exactly bounded at
`q^(3/28+epsilon/14)`.

The compressed collision root is factored exactly, and the combined
pre-substitution main term is bounded by an explicit constant times
`A^(13/14)*H^(13/14)*q^(3/28+epsilon/14+delta/14)`. Substitution of the
rounded `A,B`, the final totient epsilon allocation, and boundary contraction
remain.

## Release 2.67: rounded Burgess exponent substitution

The scalar module now carries out the rounded `A,B` substitution itself. It
proves the exact fourteenth-power base bound arising from
`A=H/(K*B)` and `B=floor(q^(1/14))`, then takes its real fourteenth root to
obtain `2*K^(1/14)*H^(6/7)/q^(13/196)`.

Combining this with the release-2.66 rooted moment gives the normalized main
term at `H^(6/7)*q^(2/49+epsilon/14+delta/14)`, including the explicit
constant. The remaining scalar tasks are reciprocal-totient insertion,
epsilon allocation, and strict contraction of the affine boundary.

## Release 2.68: epsilon allocation and boundary contraction

The rounded main estimate now includes `q/phi(q)`. Its separate exponent
losses are specialized by taking moment epsilon `6*eta`, harmonic epsilon
`eta`, and totient epsilon `eta/2`, giving exactly
`H^(6/7)*q^(2/49+eta)`.

For the boundary, exact quotient geometry strengthens `A*B<=H` to
`K*A*B<=H`. Thus its `6/7` power gains `K^(-6/7)`; under
`K^(6/7)>=4` the boundary consumes at most half the induction majorant. The
module verifies this condition for `K=128`. Recurrence-level assembly and the
complete-Weil analytic input remain.

## Release 2.69: rounded recurrence and strong induction

The two scalar estimates are now inserted into the complete-Weil recurrence.
The chosen induction coefficient absorbs the main term and its own half-sized
boundary, while `K*A*B<=H` makes every translated multiplier length strictly
smaller. Strong induction therefore removes the two boundary callbacks; the
trivial estimate handles recursive lengths below the nontrivial threshold.

With `K=128`, the core lower inequality eventually implies every rounded
parameter condition. The resulting theorem proves
`H^(6/7)*q^(2/49+eta)` throughout the quadratic no-wrap range. The remaining
large-length bridge is Pólya--Vinogradov, and the complete-Weil finite-field
residual remains the analytic input to the medium theorem.

## Release 2.70: Pólya--Vinogradov and all-prefix closure

`BurgessPolyaVinogradov.lean` now proves primitive Fourier inversion and the
exact Gauss-sum norm at composite conductors. The interval kernel is bounded
by the existing geometric majorant and summed explicitly, giving
`10*sqrt(q)*(1+harmonic(q))`.

When the rounded no-wrap inequality fails, its lower floor estimate supplies
exactly `q^(45/98)<=H^(6/7)`. This closes the large branch at the same
`H^(6/7)*q^(2/49+eta)` monomial as strong induction. The module then
combines both ranges, absorbs small conductors, applies periodicity and
conductor reduction, and exports Tao's decimal sieve-facing Burgess contract.
Only the prime finite-field complete-Weil input remains conditional.

## Release 2.71: sharp prime Kummer boundary

`BurgessWeilPrimeKummer.lean` states the remaining prime theorem with the
classical sharp coefficient `(t-1)*sqrt(p)`. Its exceptional case is exactly
a nonzero scalar multiple `C(c)*Q^(orderOf χ)`.

The tagged Burgess root has multiplicity not divisible by `orderOf χ`; a new
checked polynomial argument proves this rules out the full scalar-power
shape. The Kummer statement now implies the split-polynomial, linear-
quotient, and composite complete-Weil contracts directly. Its finite-field
proof remains the only analytic Burgess dependency.

## Release 2.72: small Sylvester--Schur lengths

`SylvesterSchurSmallLengths.lean` proves `SylvesterSchurBelow 49`. Monotone
binomial-growth propagation handles every start above small verified
baselines, and bounded prime certificates cover the remaining cases through
length forty-eight. Thus the finite rectangle in the Theorem 1.7 arithmetic
input now has `H>=49`. No new assumption is used.

## Release 2.73: eventual start-uniform Sylvester--Schur

`SylvesterSchurEventual.lean` proves `exists_sylvesterSchurAboveStart`: one
start cutoff works simultaneously for every positive length. This is enough
for all sufficiently large admissible dyadic scales, whose starts grow with
the ambient endpoint.

The new scale-local interfaces propagate that fact through `BadIntervals`,
`NormalizedBadIntervals`, `BadIntervalMaximal`, `BadIntervalRecombination`,
and `BadIntervalDyadicSummation`. Packaged window, tail, and partial-sum
conclusions avoid duplicating the endgame and preserve the former global
Sylvester--Schur APIs as compatibility theorems. The audited endpoint
`taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess` now reduces
Theorem 1.7 to analytic Burgess and the critical smooth-number saddle
asymptotic alone.

## Release 2.74: distinct-root Kummer trace

`BurgessWeilPrimeKummer.lean` rewrites the split-polynomial correlation as an
exact finite trace over distinct roots and their multiplicities. It constructs
the scalar-power base whenever every multiplicity is divisible by the
character order and proves the converse equivalence. Hence
`TaoPrimeKummerRootProductWeilBound` is exactly equivalent to the former
polynomial endpoint, with all algebraic factorization bookkeeping discharged.
The remaining input is the sharp finite-field trace bound itself.

## Release 2.75: elementary Kummer root counts

The sharp Kummer trace estimate is proved for at most two distinct roots.
The one-root sum vanishes, while the two-root sum is controlled by the exact
Jacobi-sum argument already in the production graph. The new restricted
predicate `TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore` is equivalent
to the full polynomial endpoint and has a direct composite Burgess bridge.
Only traces with at least three distinct roots remain open.

## Release 2.76: degree-divisible three-root Kummer closure

For exactly three roots and character-order-divisible degree, the sharp
Kummer bound is now unconditional. Active/inactive-root separation reduces
the trace to an existing Jacobi or projective Jacobi estimate plus one deleted
point, yielding `sqrt(p)+1 <= 2*sqrt(p)`. The equivalent refined residual is
`TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible`; the
degree-divisible Burgess family now starts at four roots.

## Release 2.77: exact three-point Kummer normalization

The active-root degree congruence is now an equivalence. A three-active-root
trace with nondivisible degree translates literally to
`TaoPrimeThreePointHypergeometricWeilBoundAt`; all inactive-root and small
characteristic cases are elementary. Under that hypergeometric endpoint, the
full Kummer theorem is equivalent to
`TaoPrimeKummerRootProductWeilBoundFourRootsOrMore`, which feeds composite
Burgess directly.

## Release 2.78: degree-divisible four-root Kummer closure

The sharp `3*sqrt(p)` bound is proved for degree-divisible four-root traces
from the existing three-point hypergeometric endpoint. Exact active-root
splitting covers two, three, and four active roots and absorbs all inactive
deleted points. The equivalent residual is now
`TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible`; for the
cleared Burgess family only five-or-more-root traces remain.

## Release 2.79: exact four-point Kummer normalization

The degree-nondivisible four-active-root trace is translated literally to
`TaoPrimeFourPointHypergeometricWeilBoundAt`. A general deletion lemma and the
fact that four distinct roots imply `p >= 4` close every inactive-root split.
Under the three- and four-point endpoints, the full polynomial Kummer theorem
is equivalent to `TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore`, which
feeds the composite Burgess chain directly.

## Release 2.80: degree-divisible five-root Kummer closure

`fiveRootMobius_term` sends one of five roots to infinity and cancels the
denominator through the trivial total character product. The resulting
four-point sum and one deleted value give the sharp `4*sqrt(p)` bound for
degree-divisible five-root traces. The generic residual is now six roots or
a nondivisible-degree five-root case. For `primeLinearOrderPolynomial`, the
new source-specific residual begins at six active roots and still has direct
linear-quotient and composite Burgess bridges.

## Release 2.81: source-shaped four-point endpoint

`fourPointMulCharSum_eq_legendreForm` scales four marked finite points to
`0,1,t,u`. The new power and reduced-power endpoint hierarchy proves that the
exact five-active-root Burgess branch needs only powers of its single input
character, reduced exponents, two geometric parameters, and `p > 64`.
`TaoPrimeLinearOrderPolynomialWeilBoundSixActiveRootsLargeCharacteristic`
now reaches composite Burgess through this narrower endpoint; the two reduced
hypergeometric estimates and the six-active-root residual remain open.

## Release 2.82: six-root projective reduction

The new `BurgessWeilPrimeSixRoots` module proves the pointwise and complete
six-root Möbius identities, the `4*sqrt(p)+1` active-root estimate, and the
split-polynomial bridge. Its five-point analytic input is reduced to powers
of one character, exponents below `orderOf χ`, `p > 64`, and the three
parameters of `0,1,t,u,v`. The source-specific residual now starts at seven
active roots.

## Release 2.83: literal fixed-order Burgess boundary

`TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven` now feeds every
fourteenth-moment consumer through the explicit cubefree Burgess theorem.
The local input is independently specialized: fixed-`Fin 7` prime-power
predicates, cube-free CRT strong induction, and
`TaoPrimeLinearQuotientWeilBoundRSeven` connect the fixed seven-active-root
source residual to that composite endpoint. The unconditional prime-square
argument remains shared with the general interface.

## Release 2.84: seven-root projective reduction

The new `BurgessWeilPrimeSevenRoots` module proves the seven-root pointwise
and complete Möbius identities, the sharp `5*sqrt(p)+1` active-root estimate,
and the split-polynomial bridge. Its six-point analytic input is reduced to
powers of one character, exponents below `orderOf χ`, `p > 64`, and the four
parameters of `0,1,t,u,v,w`. Both source routes now retain only an
eight-active-root residual.

## Release 2.85: finite fixed-order residual window

At `r=7`, `primeLinearOrderPolynomial` has at most fourteen distinct roots,
and every active root is among them. The production hypothesis is therefore
restricted to `8 ≤ activeRoots.card ≤ 14`, with direct bridges through the
fixed prime quotient and composite Weil predicates.

## Release 2.86: eight-root projective reduction

`BurgessWeilPrimeEightRoots` proves the exact eight-root Möbius and complete-
sum identities, the sharp `6*sqrt(p)+1` active-root estimate, and the
split-polynomial bridge. Its seven-point analytic input is reduced to powers
of one ambient character, finite exponent ranges, `p > 64`, and the
five-parameter form `0,1,t,u,v,w,z`. The literal residual window is now
`9 ≤ activeRoots.card ≤ 14`.

## Release 2.87: nine-root projective reduction

`BurgessWeilPrimeNineRoots` proves the nine-root Möbius and complete-sum
identities, the sharp `7*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its eight-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the six-parameter form
`0,1,t,u,v,w,z,r₀`. The literal residual window is now
`10 ≤ activeRoots.card ≤ 14`.

## Release 2.88: ten-root projective reduction

`BurgessWeilPrimeTenRoots` proves the ten-root Möbius and complete-sum
identities, the sharp `8*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its nine-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the seven-parameter form
`0,1,t,u,v,w,z,r₀,s₀`. The literal residual window is now
`11 ≤ activeRoots.card ≤ 14`.

## Release 2.89: eleven-root projective reduction

`BurgessWeilPrimeElevenRoots` proves the eleven-root Möbius and complete-sum
identities, the sharp `9*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its ten-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the eight-parameter form
`0,1,t,u,v,w,z,r₀,s₀,a₀`. The literal residual window is now
`12 ≤ activeRoots.card ≤ 14`.

## Release 2.90: twelve-root projective reduction

`BurgessWeilPrimeTwelveRoots` proves the twelve-root Möbius and complete-sum
identities, the sharp `10*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its eleven-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the nine-parameter form
`0,1,t,u,v,w,z,r₀,s₀,a₀,b₀`. The literal residual window is now
`13 ≤ activeRoots.card ≤ 14`.

## Release 2.91: thirteen-root projective reduction

`BurgessWeilPrimeThirteenRoots` proves the thirteen-root Möbius and complete-
sum identities, the sharp `11*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its twelve-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the ten-parameter form
`0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀`. The literal fixed-`r=7` residual is now only
the exact case `activeRoots.card = 14`.

## Release 2.92: fourteen-root projective reduction

`BurgessWeilPrimeFourteenRoots` proves the fourteen-root Möbius and complete-
sum identities, the sharp `12*sqrt(p)+1` active-root estimate, and the exact
split-polynomial bridge. Its thirteen-point input is reduced to one ambient
character, finite exponent ranges, `p > 64`, and the eleven-parameter form
`0,1,t,u,v,w,z,r₀,s₀,a₀,b₀,c₀,d₀`.

The structural fourteen-root cap closes the last literal fixed-`r=7` source
case. Consequently the fixed prime quotient and cube-free composite complete-
Weil interfaces depend only on the reduced trace endpoints through thirteen
points, with no remaining source-cardinality residual. The reduced trace
endpoints remain unproved, so no unconditional Burgess or Theorem 1.7 claim is
made.

## Release 2.93: source-facing Erdős--Selfridge bridge

`ErdosSelfridgeSource` formalizes the exact translation from the stronger
prime-valuation statement in Erdős--Selfridge Theorem 2 to the square theorem
used by Tao. It proves the local interval product equals the source's closed
product over `[N+1,N+H]`, constructs the least prime `p^(H)`, and uses Bertrand
to verify `p^(H) <= N+H` whenever `H<N`. At exponent two, a square has every
prime valuation divisible by two, contradicting the source witness.

The resulting theorem feeds both the Lemma 4.2 and direct source-input
Theorem 1.10 consumers. The prime-multiplicity theorem itself remains a
proposition-valued input, so this release narrows and source-aligns the
dependency without claiming an unconditional Erdős--Selfridge or Theorem
1.10 proof.

## Release 2.94: Erdős--Selfridge power-free coefficients

`ErdosSelfridgePowerFree` formalizes equation (3) of the pinned paper. Prime
valuations split canonically into remainder modulo `l` and quotient by `l`,
giving `m=a*x^l` with every valuation of `a` below `l`. A strengthened
interval uniqueness lemma handles every prime `p>=H`, including `p=H`, and
identifies its product valuation with that of the unique factor it divides.

Thus a counterexample to source Theorem 2 now yields the simultaneous
equation-(3) decomposition of every factor in `[N+1,N+H]`, with each
coefficient supported only on primes below `H`. The source's distinct-product
Lemma 1 and later deletion/counting argument remain to be formalized.

## Release 2.95: Erdős--Selfridge product separation

`ErdosSelfridgeProductSeparation` formalizes source equation (2), equation
(4), and all of Lemma 1. The Sylvester--Schur witness turns failure of source
Theorem 2 into `H^l<N`; gcd control for products of interval elements then
proves distinctness for equally sized subfamilies of cardinality below `l`.

The source's stronger statement about quotients is proved over positive
rationals, not merely for equal products. Cancelling the numerator and
denominator gcd reduces it to coprime powers; a lower power-gap estimate and
a strict interval upper-gap estimate are incompatible. Equation (3) then
transfers both conclusions to the canonical power-free coefficients. Lemma 2
and the remaining deletion/counting cases are still open, so no unconditional
Erdős--Selfridge or Theorem 1.10 conclusion is claimed.

## Release 2.96: Erdős--Selfridge deletion lemma

`ErdosSelfridgeDeletion` formalizes Lemma 2 and equation (9). It chooses a
maximal-valuation interval position for every prime below `H`, proves the
factorization bound against the corresponding position distance, and computes
the complete distance product as `m!*(H-1-m)!`. The binomial factorial
divisibility then gives the required divisor of `(H-1)!`.

Duplicate chosen positions are harmless: the core deletion set is extended
inside `range H` to exactly `primeCounting (H-1)` positions, so the survivor
cardinality is exactly the source value. The same valuation proof at exponent
two gives equation (21), with the full coefficient product dividing
`(H-1)!` times the product of primes below `H`. The remaining square proof
requires the source's large-length inequality and finite residual analysis.

## Release 2.97: the 36-term squarefree-density lemma

`ErdosSelfridgeSquareDensity` begins the proof of source equation (22). A
general interval lemma counts multiples of any divisor `d` of the block
length exactly. Applied to `4`, `9`, and their coprime product `36`,
inclusion--exclusion proves that exactly twelve values in `(N,N+36]` are
divisible by `4` or `9`.

Squarefree values cannot occupy any of those positions, so Lean obtains the
source bound of at most 24 squarefree values in every block of 36 consecutive
positive integers, together with the `N+(i+1)` offset formulation used by the
existing interval API. The full product lower bound (22), the valuation
comparison (23), and the finite residual lengths remain open.

## Release 2.98: source equation (22)

The same module now proves equation (22) itself. A cumulative squarefree
count is initialized on `44≤M<80` by an explicit small-prime-square sieve and
then advanced in exact blocks of 36. The first 64 squarefree values are
described by excluding `4`, `9`, `25`, and `49` up to 103; their cardinality
and strict product inequality are kernel-evaluated without `native_decide`.

Increasing finset enumerations prove that this first-64 product is minimal.
For larger finsets, removing the maximum and using `3*card≤2*max` propagates
the cleared inequality `3^H H! < 2^H ∏a`. Lemma 1 supplies injectivity of the
canonical counterexample coefficients, yielding the source-facing equation
(22). Equation (23) and the finite residual lengths remain open.

## Release 2.99: the exact pre-equation-(23) valuation ledger

`ErdosSelfridgeSquareValuations` defines the canonical coefficient product
and proves that the squarefree primorial in equation (21) has valuation one
at every prime below `H`. It then extracts the full powers of `2` and `3` from
the equation-(21) divisibility relation without division or rounding.

The source-facing theorem combines this result with equation (22), producing
the exact strict integer inequality on which the paper applies its four
elementary logarithmic valuation bounds. Those bounds and the final displayed
equation (23) remain the next large-length obligations.

## Release 3.00: the four valuation bounds and logarithmic pre-(23) form

`ErdosSelfridgeSquareValuations` now proves the paper's four explicit
valuation estimates. Legendre's digit-sum formula gives the lower bounds for
the powers of `2` and `3` in `(H-1)!`; exact halving and thirding recurrences
for odd interval valuations give the matching upper bounds for the canonical
squarefree coefficient product.

The integer ledger is then cast to `ℝ`, `(H-1)!` is cancelled, the right-hand
powers are divided out, and all four estimates are inserted into
`powerFreePart_two_preEquation23_logarithmic_of_failure`. The only remaining
step to the displayed equation (23) is its elementary real-power
simplification to the constant `14/3`; the primorial contradiction and finite
residual square cases remain open.

## Release 3.01: displayed equation (23)

`erdosSelfridge_equation23_root_factor_le` bounds the residual root factor by
`4H²`, hence by the source constant `(14/3)H²`. Exact `rpow`/`logb`
identities then turn the logarithmic endpoint into
`erdosSelfridge_equation23_of_failure`, the paper's displayed equation (23).
The next large-length obligation is the explicit primorial estimate and its
contradiction for the required range of `H`.

## Release 3.02: eventual primorial contradiction

`ErdosSelfridgePrimorial` identifies the source prime product with the
standard primorial at `H-1`. The frozen prime number theorem gives the
eventual upper bound `prod_{p<H} p <= 3^H`.

The effective base of equation (23) is proved strictly larger than `3` using
the exact rational comparisons `14/9 < 2^(2/3)` and
`13/10 < 3^(1/4)`. Polynomial-versus-exponential growth therefore contradicts
equation (23) for every sufficiently large `H`. The paper's explicit cutoff
and the finite residual square lengths remain open.

## Release 3.03: first finite Section 3.2 cases

`ErdosSelfridgeFinite` proves a general finite-candidate embedding: under a
square-case failure, the `H` distinct canonical coefficients inject into the
positive divisors of `prod_{p<H} p`. It closes `H=3` and `H=5` by exact
candidate-cardinality computations.

For `H=4`, the four coefficients exhaust `1,2,3,6`, so their product is `6^2`.
Equation (3) would make four consecutive integers a square, contradicting
`(N+1)(N+2)(N+3)(N+4) = (N^2+5N+5)^2-1`. The remaining finite range starts
at `H=6`.

## Release 3.04: the exceptional length-six split

`not_erdosSelfridgePrimeMultiplicityFailureAt_two_six` formalizes both source
branches at `H=6`. If `5` does not divide `N+1`, exactly five of the six
positions avoid `5`, so their distinct coefficients cannot fit among the four
products supported on `2` and `3`.

If `5` divides `N+1`, the middle four positions avoid `5`; their coefficients
exhaust `1,2,3,6`, and equation (3) makes those four consecutive integers a
square, contradicting the release-3.03 identity. The combined finite endpoint
now covers `3 <= H <= 6`.

## Release 3.05: length seven

`not_erdosSelfridgePrimeMultiplicityFailureAt_two_seven` closes `H=7` by
the small-prime count from Section 3.2. An exact modulo-five enumeration shows
that at least five of the seven interval positions avoid `5`. Their distinct
canonical coefficients are therefore supported only on `2` and `3`, but the
only four candidates are `1,2,3,6`.

The combined endpoint
`not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seven`
now excludes every square-case failure with `3 <= H <= 7`. The release-3.04
endpoint remains available as a compatibility theorem, and the finite
residual begins at `H=8`.

## Release 3.06: the exceptional length-eight split

`not_erdosSelfridgePrimeMultiplicityFailureAt_two_eight` formalizes the
source's full `H=8` argument. Reduction modulo `35` proves that at least five
positions avoid both `5` and `7` unless `7 | N+1` and `5 | N+2`; in the
ordinary branch their distinct coefficients cannot fit among `1,2,3,6`.

In the exceptional class the middle four terms `N+3,...,N+6` avoid both
primes. Their coefficients exhaust `1,2,3,6`, and equation (3) again forces a
forbidden square product of four consecutive integers. The combined endpoint
now covers `3 <= H <= 8`, and the finite residual begins at `H=9`.

## Release 3.07: uniform lengths nine through thirteen

The small-prime pigeonhole argument now closes `9 <= H <= 13`. For lengths
nine through eleven, a modulo-`35` count produces five positions avoiding
`5` and `7`. For lengths twelve and thirteen, a modulo-`385` count produces
five positions avoiding `5`, `7`, and `11`.

In both blocks the surviving canonical coefficients are distinct but must be
among `1,2,3,6`. The combined endpoint
`not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_thirteen`
therefore covers `3 <= H <= 13`; the next finite boundary is `H=14`.

## Release 3.08: interval-union counts through seventeen

`ErdosSelfridgeFiniteCounts` replaces large residue enumeration by a reusable
union bound for multiples of `5,7,11,13`. Exact block counts at the divisible
lengths and the general interval-multiple estimate leave at least five terms
with coefficients supported only on `2,3` for every `14 <= H <= 17`.

The resulting five-to-four contradiction extends the combined finite endpoint
to `3 <= H <= 17`. The next finite boundary is `H=18`, where `17` enters the
excluded prime support.

## Release 3.09: scalable counts through twenty

`ErdosSelfridgePrimeUnion` proves sharp ceiling and finite-prime union bounds.
`ErdosSelfridgeFiniteTwenty` transfers the resulting five survivors through
coprimality with the excluded-prime product, forcing every coefficient to
divide six. The combined finite endpoint now covers `3 <= H <= 20`; the next
source range begins at `H=21`.

## Release 3.10: complete finite range through seventy

`ErdosSelfridgeFiniteSeventy` proves that for every `21 <= H <= 70`, at
least nine interval terms avoid all coefficient primes `p >= 7`. Their
canonical coefficients are therefore nine distinct divisors of `30`, although
`30` has only eight positive divisors. The combined finite endpoint now covers
the complete source range `3 <= H < 71`.

## Release 3.11: explicit Section 3.1 split

`ErdosSelfridgeLargeGrowth` proves the paper's numerical equation-(23) split.
A rational lower bound `31335/10000` for the effective exponential base gives
the exact growth cutoff `H >= 297`. For every `71 <= H <= 296`, one closed
natural-number certificate checks the actual prime product and contradicts
equation (23). Thus the only remaining square-case input is the named
elementary assertion `prod_{p<H} p <= 3^H`, needed from `H=297` onward.

## Release 3.12: Hanson's elementary three-primorial bound

`ErdosSelfridgeHanson` formalizes Hanson's Sylvester sequence and its strict
reciprocal floor sum.  The resulting factorial coefficient is divisible by
every prime below its index.  For the quantitative upper bound, the first four
denominators `2,3,7,43` and integer weights `903,602,258,42,1` (summing to
`1806`) produce a five-part multinomial estimate with no real logarithms.

After clearing the exponent `1806`, exact natural-number inequalities absorb
the remainder primorial and floor losses from length `1400` onward.  Twenty-five
monotone endpoint certificates cover the smaller lengths.  Thus
`erdosSelfridgeThreePrimorialConclusion_hanson` proves
`prod_{p<H} p <= 3^H` for every `H`, and the square conclusion now requires
only `SylvesterSchurConclusion`.

## Release 3.13: prime-count factorial Sylvester--Schur threshold

`SylvesterSchurFactorialThreshold` replaces the coarse fixed-length cutoff
`H^H+1` by a factorial argument.  From
`(N+1)^H <= H! * choose (N+H,H)` and `N+H <= 2(N+1)`, it proves that
`H! 2^r < (N+1)^(H-r)` forces a prime divisor above `H`, whenever `r` bounds
the number of primes at most `H`.

Taking the exact exponent `r=pi(H)` yields the cutoff
`H! 2^pi(H)+1`.  The public classical cutoff `H! 2^(H-1)+1` follows from
`pi(H)<H`.  The unrestricted theorem is now reduced to the corresponding
exact-prime-count finite rectangle; lengths below `49` remain discharged by
the earlier certificate.

## Release 3.14: Sylvester--Schur through length one hundred

`SylvesterSchurHundred` verifies the `3H` binomial-growth baseline for every
`49<=H<=100`.  One finite-type certificate supplies a prime witness for all
starts below that baseline; `choose_growth_of_le` propagates the result to
every later start.

The public endpoint `sylvesterSchurBelow_oneHundredOne` is unconditional and
uniform in the start.  Together with the exact factorial cutoff, it restricts
the remaining rectangle to lengths `H>=101`.

## Release 3.15: square-root and one-third primorial envelopes

`SylvesterSchurSqrtEnvelope` splits the prime factorization of `choose n k`
at `sqrt n`.  Low primes contribute at most `n^sqrt(n)`.  High primes have
valuation at most one; under the no-large-prime hypothesis they contribute a
primorial, which Hanson's theorem bounds by an explicit power of three.

In the central range `2k<=n`, primes in `(n/3,k]` have zero binomial
valuation, sharpening the bound to
`choose n k <= n^sqrt(n) * 3^(n/3+1)`.  Both this bound and its weaker
`3^(k+1)` form now export exact numerical-gap criteria for a prime `p>k`, in
binomial and consecutive-product form.  This is the scalable analytic layer
for the still-open `H>=101` rectangle; no unconditional global
Sylvester--Schur claim is made here.

## Release 3.16: explicit central tail

`SylvesterSchurCentralTail` discharges the sharper release-3.15 gap without
real logarithms or an ineffective asymptotic threshold.  A block induction
proves `x <= 2^(sqrt(x)/16)` once `sqrt(x)>=320`, then absorbs the complete
square-root factor at `n=3H` into `2^(H/4)`.  A second fixed-base induction
proves the remaining comparison against `4^H`.

Consequently, for every `H>=34134` and every central start
`H<N<=2H`, the interval product has a prime divisor `p>H`.  The result is
uniform over that entire two-dimensional region and is exported both for
binomial coefficients and consecutive products.  The noncentral starts and
the finite bridge `101<=H<34134` remain part of the unrestricted
Sylvester--Schur boundary.

## Release 3.17: effective all-start tail

`SylvesterSchurExplicitTail` closes every start once `H>=4^101`.  In the near
range `N+H<=1024H`, an exact logarithmic estimate discharges the original
square-root/Hanson envelope.  At the endpoint `1024H`, Mathlib's explicit
Chebyshev prime-count bound proves
`(1024H)^pi(H) < choose (1024H) H`; the checked binomial monotonicity theorem
then propagates this inequality to every larger upper index.

Combining this effective tail, the proof below `101`, and the exact
prime-count factorial start cutoff gives the concrete proposition
`SylvesterSchurExplicitResidualRectangle`: only
`101<=H<4^101` and
`N+1 < H! * 2^pi(H) + 1` remain.  Discharging precisely that finite rectangle
now implies unrestricted `SylvesterSchurConclusion`.

## Release 3.18: sharpened effective tail

The same `SylvesterSchurExplicitTail` architecture now uses the transition
point `64H` and starts at `H>=250000`.  Antitonicity of `log x/sqrt x`,
anchored at `250000=500^2`, gives `log H<=sqrt(H)/40`.  This absorbs the
near square-root/Hanson envelope through `64H`; the explicit Chebyshev
prime-count estimate supplies the far binomial-growth baseline at `64H`.

Consequently `exists_large_prime_dvd_consecutiveProduct_of_explicit_tail`
closes every start for `H>=250000`, and
`SylvesterSchurExplicitResidualRectangle` is now exactly the finite region
`101<=H<250000`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.19: prime-counted effective tail

`SylvesterSchurPrimeCountEnvelope` retains the exact number of low primes in
the square-root split, replacing the exponent `sqrt(n)` by
`pi(sqrt(n))`.  A checked reduced-residue count gives
`pi(m)<=m/4` for every `m>=120`.

`SylvesterSchurPrimeCountTail` uses this saving to prove the near
square-root/Hanson gap through `64H` already for `H>=10000`.  On the far
branch, a modulo-210 reduced-residue count gives `pi(H)<=H/4`; exact
logarithmic comparison at `64H` supplies the binomial-growth baseline and
the existing monotonicity theorem propagates it to every larger start.

Consequently
`exists_large_prime_dvd_consecutiveProduct_of_primeCount_tail` closes every
start for `H>=10000`.  The new exact residual proposition
`SylvesterSchurPrimeCountResidualRectangle` is
`101<=H<10000`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.20: bounded prime-count bridge

`SylvesterSchurPrimeCountTailSixThousand` proves the exact finite envelope
`6*pi(m)<=m+84` for `100<=m<800`.  Combined with
`log H<=13*sqrt(H)/100`, it closes the near branch through `64H` throughout
`6000<=H<10000`.  The generalized release-3.19 far baseline applies from
`H>=2200`, and the previous tail handles `H>=10000`.

Thus every start is closed for `H>=6000`.  The exact remaining rectangle is
`101<=H<6000`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.21: adaptive-transition tail

`SylvesterSchurPrimeCountTailTwoThousandTwoHundred` proves the bounded
envelope `4*pi(m)<=m+12` for `60<=m<400`.  It uses transition `16H` on
`2200<=H<3000` and transition `20H` on `3000<=H<6000`.  Certified logarithmic
bounds close both near branches, while `pi(H)<=H/4` supplies the matching
far binomial-growth baselines.

Consequently every start is closed for `H>=2200`.  The new residual is exactly
`101<=H<2200`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.22: finite prime-count tail to 512

`SylvesterSchurPrimeCountTailFiveHundredTwelve` uses transition `5H` on
`512<=H<625`, transition `6H` on `625<=H<1134`, and transition `5H` on
`1134<=H<2200`.  Exact finite certificates prove the required bounds
`pi(H)<=H/5` and `pi(H)<=H/6`; the last segment is derived from
`pi(1906)=291` and four kernel-checked coprimality counts modulo `210`.
The corresponding logarithmic bounds close the near branches, and the finite
prime-count bounds supply the matching far binomial-growth baselines.

Consequently every start is closed for `H>=512`.  The new residual is exactly
`101<=H<512`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.23: central finite bridge to 121

`SylvesterSchurPrimeCountTailOneHundredTwentyOne` kernel-checks the central
binomial-growth inequality at `n=2H` throughout `121<=H<512`, apart from the
five exact exceptions `139,140,199,200,201`.  The prime-counted square-root
envelope covers those rows up to `n=281` and `n=403`, where separately checked
binomial baselines take over.  Growth monotonicity then handles every larger
upper index.

Consequently every start is closed for `H>=121`.  The new residual is exactly
`101<=H<121`, `N+1 < H! * 2^pi(H)+1`.

## Release 3.24: unrestricted Sylvester--Schur and square Erdős--Selfridge

`SylvesterSchurComplete` proves a common exact binomial baseline at upper
index `243` for every remaining length `101<=H<121`. A single bounded
certificate covers all starts below that baseline, completing
`SylvesterSchurConclusion` without assumptions.

`ErdosSelfridgeComplete` inserts this theorem into the checked Hanson and
Erdős--Selfridge chain. It proves `ErdosSelfridgeSquareConclusion`, the
unconditional two-element factorial-fiber bound, and public Theorem 1.10
bridges whose only remaining inputs are Theorem 2.5 and Proposition 2.3(ii)
or the source-shaped Baker--Harman--Pintz theorem.

## Release 3.25: literal Type II convolution bridge

`TypeIIConvolutionBridge` identifies a product-restricted convolution double
block with an exact Type II outer sum and proves the Cauchy--Schwarz passage to
the canonical squared-inner-sum quantity.  Its bounded support is shown to be
identical to the full Vaughan support under the product restriction.  The
actual source beta and gamma coefficients satisfy the required bounds `1` and
`log(2B)`, and a final triangle inequality reassembles arbitrary block square
bounds into the full product convolution norm.

`TypeIISourceBlock` composes this bridge with the conditional source
Vinogradov theorem, producing a bound for the literal source Type II Vaughan
double block rather than an abstract inner-sum endpoint.  The remaining
Theorem 2.5 work is the Vinogradov proposition itself, the all-block source
regime split and asymptotic Type I/II summation, and the Fourier closure.

## Release 3.26: complete finite Type II family split

Both source tail cutoffs are now used at block level.  A dyadic outer block
below the common subdivision budget has identically zero beta coefficient;
the analogous inner block has identically zero gamma coefficient.  Under the
source-sized cutoffs, every nonzero Type II block is therefore large--large
and falls directly under the conditional mixed Weyl--Vinogradov theorem.

The explicit `vaughanTypeIISourceBlockMajorant` packages this case split, and
the full product convolution is bounded by the sum of its square roots over
all canonical block pairs.  The exact family count converts any uniform block
square bound `R` into `(log₂ B+1)^204 sqrt(R)`.  The remaining Type II step is
the uniform source-parameter comparison and asymptotic simplification of this
majorant, in addition to the still-open Vinogradov proposition.

## Release 3.27: canonical cube-root Type II cutoffs

`TypeIISourceBlock` now defines the literal natural cutoff
`vaughanSourceTailCutoff B = ⌊B^(1/3)⌋₊`.  Real-power little-o estimates prove
that it eventually dominates twice the exact short-family budget and that it
dominates `2B^(1/4)` despite floor rounding.  Thus `P≤B` automatically yields
the source lower-scale inequality with `c=1/4`.

The all-block theorem also tests the true dyadic cutoff boundaries, discards
empty product supports exactly, bounds every contributing product scale by
`2B`, and turns the global phase inequality into the required blockwise one.
Its canonical-cutoff corollary fixes both Vaughan tail parameters to
`⌊B^(1/3)⌋₊` and removes all blockwise scale assumptions.  Only the conditional
Vinogradov proposition and asymptotic simplification of the displayed
majorant remain in the Type II branch.

## Release 3.28: canonical Type II geometric majorant

The Type II family is now fully canonical: the two source cutoffs are
`⌊B^(1/3)⌋₊` and the derivative orders are exactly `{5,6}`.  Large surviving
blocks satisfy the literal quarter-power lower bounds on both dyadic scales.
Their short lengths are bounded by `B/(log B)^100`, the outer block
cardinality by its length, and the component logarithm by `2log B`.

`vaughanTypeIICanonicalGeometricBlockMajorant` packages the resulting first
geometric compression, and
`vaughanTypeIICanonicalSourceBlockMajorant_le_geometric` proves that it bounds
the exact piecewise source majorant.  The remaining Type II work is to prove
`VinogradovExponentialSumEstimate` and absorb the displayed powers and family
loss into the target logarithmic saving.

## Release 3.29: scale-local Type II exponent ledger

The block simplification now uses the actual dyadic widths
`2^s/(log b)^100` and `2^t/(log b)^100`.  Product support proves both
`2^s 2^t≤b` and the two cubic/quartic monomial bounds needed after expansion.
The resulting product-compressed majorant has explicit logarithmic
denominators `298`, `197`, and `297`.

The diagonal term additionally keeps the cutoff saving
`D²E≤b²/b^(1/4)`.  The exact source majorant is bounded by this power-saved
form blockwise, and the complete conditional Type II convolution is bounded
by the sum of its square roots.  Phase decay, endpoint decay, and final family
summation remain, as does `VinogradovExponentialSumEstimate` itself.

## Release 3.30: phase and endpoint absorption

`vaughanTypeIICanonicalDecayAbsorbedBlockMajorant` removes every surviving
block parameter from the power-saved ledger.  The global phase inequality
supplies `(log b)^d≤F`, and the outer cutoff supplies
`b^(1/4)≤K`.  Negative- and positive-exponent monotonicity then replace the
two local decay factors uniformly.

`vaughanTypeIICanonicalExplicitDecayBlockMajorant` flattens the nested real
powers to `b^(7/4)`, `(log b)^(-d/1024)`, and `b^(-1/4096)`.  The full
conditional convolution is now bounded by
`(3 log b)^204 sqrt(R)` with this block-independent explicit `R`.
Choosing `d,T` and absorbing these displayed terms into the requested
arbitrary logarithmic saving remains, together with the named Vinogradov
estimate.


## Release 3.31: arbitrary Type II logarithmic saving

The explicit block ledger is now bounded eventually by
`C b²(log P)^(-E)` whenever
`E≤d/1024+197` and `E≤T+297`.  The fixed diagonal and endpoint powers
absorb arbitrary logarithmic exponents, while `P≤b≤2P` compares the two
logarithmic bases.

After square-root extraction, the `(3log b)^204` family loss requires
`E=2S+408`.  The source-facing theorem chooses
`d=2048S+216064`, `T=2S+111`, and
`A=(2S+113)/3`, proving `C b/(log P)^S` for every `S≥0`, conditional
only on `VinogradovExponentialSumEstimate`.

## Release 3.32: literal Type I convolution bridge

`TypeIConvolutionBridge.lean` now rewrites every canonical outer Vaughan
block as the exact product-restricted Type I outer sum.  For `m>0`, the
inner support is proved equal to
`[⌈a/m⌉,⌈b/m⌉)`, and its phase is exactly rescaled to
`(N/m, M/m^j)`.

The first Type I coefficient retains norm at most `1`; the second retains
the uniform `log(2B)` envelope.  Both complete outer-block families are
reassembled into source-interval theorems.  The logarithmically weighted
inner is connected directly to `norm_sum_Ico_log_smul_le`, so the remaining
quantitative Type I work is precisely a uniform bound for the displayed
unweighted reciprocal-phase prefixes.  No analytic estimate is assumed or
claimed by this release.

## Release 3.33: cutoff-active Type I families

The Type I triangle reduction now removes every zero outer coefficient
before estimating inner sums. The first active support has cardinality at
most `U`; the second has cardinality at most `UV`, exactly reflecting the two
Vaughan cutoffs.

For a uniform inner bound `Q`, the complete canonical families consequently
cost `(logâ‚‚ B+1)^102 U Q` and
`(logâ‚‚ B+1)^102 log(2B) UV Q`. This removes the spurious ambient factor `B`
from the provisional bridge and leaves a quantitatively usable analytic
callback.

## Release 3.34: Type I scale and ceiling geometry

The reciprocal-phase scale is now proved antitone in its positive scale
argument and exactly invariant under the Type I substitution
`(N,M,X) -> (N/m,M/m^j,X/m)`.  The exact multiplication form is also
exported for rounded natural endpoints.

For `P>0` and `m>0`, the rounded inner scale `ceil(P/m)` is positive, its
dyadic fiber lies in `[ceil(P/m),2ceil(P/m))`, and the rescaled phase at that
rounded scale is no larger than the source phase at `P`.  Hence the source
condition `F(P) <= (P/m)^4` implies the low-scale Weyl condition at
`ceil(P/m)`.  The remaining Type I analytic step is to fit the four-step
differencing buffer (or subdivide the fiber) and bound its effective error.

## Release 3.35: quadratic Type I Weyl subdivision

`TypeIWeylBridge.lean` resolves the endpoint obstruction for the source
specialization `j=2`.  A full dyadic inner interval is reconstructed exactly
from at most ten ceiling-rounded short blocks.  For base scale at least ten,
each nonempty block satisfies `lo+5(hi-lo)<=2lo`; this automatically fits the
interval and all four optimized differencing rounds into `[lo,2lo]`.

The quadratic phase scale loses at most a factor four across a dyadic window.
Consequently one explicit source-scale budget controls the complete local
effective error, and the existing two-term four-step Weyl theorem applies to
every nonempty block.  The next step is to uniformize and sum the resulting
ten local widths, then insert that bound into the active Type I callback.

## Release 3.36: uniform Type I subinterval Weyl bound

The local two-term widths are now dominated by one source-scale width
`(F/D^5+4/F)^(1/1024)`. Every nonempty ten-block is bounded by the same
explicit majorant, and the exact block count gives a factor ten for the full
dyadic interval.

The construction now applies to every half-open subinterval of `[D,2D)`,
including all initial subintervals used by Abel summation. Such an interval
still has at most ten pieces with the same source majorant. The next step is
to substitute `(N/m,M/m^2)` and `D=ceil(P/m)`, then make the resulting source
budget uniform over active Vaughan outer indices.

## Release 3.37: rescaled active Type I callbacks

The uniform subinterval theorem is now instantiated at the literal Type I
parameters `(N/m,M/m^2)` and `D=ceil(P/m)`. The resulting explicit majorant
controls the unweighted inner fiber directly and, uniformly over every
prefix, controls the logarithmically weighted fiber through finite Abel
summation.

Both estimates now feed the complete active Vaughan families. The second
Type I term is bounded by `(log₂ B+1)^102 log(2B) UV Q`; the first is bounded
by `(log₂ B+1)^102 U Q`, with no ambient `B` loss. The remaining Type I task
is to derive the displayed active-index admissibility and common-majorant
premises from the eventual source parameter choices and absorb their explicit
losses into the requested logarithmic saving.

## Release 3.38: exact Type I high/low split

The rescaled Type I fiber no longer assumes that every active index lies in
the Weyl regime. At the rounded inner scale `D=ceil(P/m)`, the proof now
splits exactly at `F(D)=D^4`: the low branch uses the ten-block Weyl estimate,
while the high branch uses the source Vinogradov component envelope.

The split is uniform over arbitrary subintervals and therefore over every
Abel prefix. Both complete active Vaughan families consume the resulting
hybrid majorant. Under the source exponential parameter bound and a
positive-power lower bound for `D`, the high branch's derivative cutoff and
numerical smallness conditions are discharged eventually. The remaining
Type I work is the low-branch effective-error inequality and uniform
absorption of the explicit hybrid majorant.

## Release 3.39: automatic active-fiber admissibility

The low-scale Weyl budget is now derived from the branch inequality
`F(D) <= D^4` once `D` exceeds one explicit absolute threshold. Ceiling
arithmetic compares the source phase scale at `P` with the transformed scale
at `D=ceil(P/m)` with loss at most four.

The new `TypeISourceBlock.lean` proves that either canonical Vaughan Type I
active support forces `D >= B^(1/4)` eventually. Consequently the global
source lower and exponential upper frequency bounds imply the complete
hybrid admissibility predicate simultaneously for every active outer index.
The remaining Type I step is to dominate and sum the explicit hybrid
majorants with the logarithmic saving required by Theorem 2.5.

## Release 3.40: reciprocal-weighted Type I aggregation

The complete Type I family bounds now retain the natural fiber length
`D ~ P/m`. For each short-interval block, the reciprocal weights over either
canonical active support are bounded by the exact harmonic number at cutoff
`U` or `UV`. Summing a bound of the form `(P/m)Q` therefore costs only this
harmonic factor, not the former cardinality factors `U` and `UV`.

This removes the structural loss that would have overwhelmed every
logarithmic saving. The remaining analytic step is branch-sensitive
absorption of the low Weyl and high Vinogradov majorants into such a common
reciprocal-weighted `Q`.

## Release 3.41: complete quantitative Type I closure

The Type I estimate now uses a branch-sensitive majorant rather than the
maximum of both analytic formulas. On high fibers the existing source
Vinogradov envelope is eventually at most `3 D (log B)^(-T)`. On low fibers
the Weyl source width is reduced to
`(1/D + 16/(log B)^d)^(1/1024)`; the active-support quarter-power lower bound
for `D` absorbs the endpoint contribution.

These estimates are inserted into both complete canonical Vaughan Type I
families through the reciprocal-weighted aggregation theorems. The exact
coefficient, short-interval, harmonic, and Abel ledger costs 104 logarithmic
powers. Choosing `T=S+104`, with `S+106<=3A` and
`1024*(S+105)+1<=d`, gives the requested arbitrary saving for both families.
Thus the quantitative Type I side is complete, conditional only on the named
source `VinogradovExponentialSumEstimateAt C1` input. The next Theorem 2.5
step is to combine these Type I bounds with the complete Type II bounds and
the formalized Vaughan identity.

## Release 3.42: quadratic Mangoldt Vaughan assembly

The new `MangoldtSourceBlock.lean` connects the completed analytic families
to the exact source-oriented Vaughan identity. The initial Mangoldt-cutoff
term vanishes once the dyadic interval begins above the canonical cube-root
cutoff; the two Type I norms and the Type II norm then combine by the exact
triangle inequality, including the subtraction sign of the second Type I
term.

With the shared phase exponent `2048*S+216064`, the final theorem supplies an
arbitrary logarithmic saving for the complete quadratic Mangoldt reciprocal-
phase sum. Its absolute constant is the sum of the two Type I contributions
and the endpoint-adjusted Type II contribution. The theorem remains
conditional only on the named Vinogradov exponential-sum proposition. The
next interface task is to derive the currently displayed Type I scale bounds
and Type II `|N|` bounds from one source-facing frequency range, then pass
from Mangoldt weights to primes and the Fourier reconstruction.

## Release 3.43: unified source-frequency range

The quadratic Mangoldt theorem now has a source-facing wrapper with only one
lower and one upper bound on `|N|`. Elementary scale lemmas prove
`F(N,N,2,P) <= 2|N|`; the common lower bound implies both
`log(B)^d <= F(N,N,2,P)` and the absolute threshold `64 <= F`.

Consequently the Type I reciprocal-scale premises and the Type II absolute-
frequency premises no longer appear side by side in the exported endpoint.
The next step is the Mangoldt-to-prime partial-summation transfer, followed by
the already prepared Fourier reconstruction.

## Release 3.44: quadratic prime source estimate

The new `PrimeSourceBlock.lean` completes the Mangoldt-to-prime transfer on
every half-open dyadic subinterval. An exact endpoint identity converts
`[a,b)` to the frozen prime-power-tail interval convention. The resulting
tail is bounded by a quarter-power saving and then absorbed into an arbitrary
negative power of `log P`.

The Mangoldt estimate is applied uniformly to every initial prefix, prime
powers are removed, and the existing reverse Abel theorem removes the
logarithmic prime weight. The exported unweighted quadratic prime sum now has
the same single source-facing frequency range and an arbitrary logarithmic
saving. The next boundary is to bound the logarithmic integral for nonzero
Fourier modes and combine it with the low-frequency and zero-mode pieces.

## Release 3.45: diagonal Fourier source bridge

The new `FourierSourceBlock.lean` identifies the half-open `(1,1)` Fourier
prime sum exactly with the completed diagonal quadratic prime sum. For the
matching logarithmic integral, an explicit integration-by-parts identity
uses the derivative of `e(N/t+N/t^2)` and proves the dyadic bound
`6*P^2/(|N|*log P)`.

Combining these results gives the audited `(1,1)` discrepancy bound: the
release-3.44 prime saving plus that explicit inverse-frequency integral term.
This is a genuine diagonal Fourier bridge, not the full Fourier assembly.
The file also identifies every general mode exactly with coefficients
`q1*N` and `q2*M`, proves its derivative formula, and verifies
nonstationarity when those coefficients have one strict and one weak common
sign. General unequal-coefficient estimates, opposite-sign stationary cases,
and the low-frequency and zero-mode branches remain open.

## Release 3.46: unequal Type II high-pair bridge

The new `UnequalTypeIIVinogradov.lean` removes the equality restriction from
the high-scale Type II correlation path. Independent coefficients `N` and
`M` now pass through the exact product-restricted correlation rewrite, the
fixed Vinogradov envelope, the uniform logarithmic saving, the decay-kernel
callback, and the canonical Vaughan inner-block specialization.

Independent exponential upper bounds for `|N|` and `|M|` give the same
factor-five transformed-scale envelope as the diagonal proof. The next Type
II boundary is the low-scale Weyl branch: its current distance-kernel lower
bound uses `N=M`. Full unequal Type II aggregation and the subsequent
Mangoldt/prime/Fourier transfers are not yet claimed.

## Release 3.47: unequal Type II Weyl and double-block bridge

The new `UnequalTypeIIWeyl.lean` closes the complementary low-scale Type II
argument for independent coefficients. On a canonical positive dyadic inner
band, the transformed quadratic coefficient controls the part of the source
scale not supplied by the transformed linear coefficient. This gives the
unequal distance-kernel width bound and the four-step Weyl estimate.

The result is propagated through nearby-pair absorption, near/far
aggregation, the Weyl--Vinogradov split, canonical inner blocks, and one
actual weighted Vaughan Type II double block. The complete sum over the
Vaughan double-block family is still diagonal, so unequal Mangoldt, prime,
and general Fourier-mode endpoints are not yet claimed.

## Release 3.48: unequal Type II, Mangoldt, and prime source closure

The new `UnequalTypeIISourceBlock.lean` sums the independent-coefficient
double-block estimate over the complete Vaughan Type II family and carries
the result through the canonical cutoff, compressed block majorant, explicit
decay, and arbitrary logarithmic saving. A synthetic diagonal coefficient
matches each unequal block's phase scale exactly, so the audited scalar
majorant algebra is reused without weakening the bound.

`UnequalMangoldtSourceBlock.lean` inserts that Type II theorem together with
the already-general Type I families into the exact Vaughan identity. It
exports one source-facing range at scale `4*P`, with separate upper bounds on
`|N|` and `|M|`. `UnequalPrimeSourceBlock.lean` then removes prime powers and
uses reverse Abel summation to obtain the corresponding unweighted prime
estimate. The quadratic coefficient is required to be nonzero. General
Fourier completion still needs the zero-quadratic-mode branch, oscillatory
integrals (including stationary opposite-sign modes), low frequencies, and
the final mode sum; Theorem 2.5 is not claimed.

## Release 3.49: same-sign unequal Fourier modes

The new `UnequalFourierSourceBlock.lean` generalizes the logarithmic
oscillatory-integral argument to independent linear and quadratic
coefficients in both same-sign chambers. For positive coefficients it uses
the exact amplitude `t^3/((A*t+2*B)*log t)`, proves its monotonicity, and
performs integration by parts. Complex conjugation transfers the result to
negative coefficients.

Combining these integral bounds with release 3.48 gives a literal
prime-sum-minus-integral discrepancy estimate for every mode whose two
rescaled coefficients are nonzero and have the same sign. The opposite-sign
stationary chamber, coordinate-axis modes, low frequencies, and final mode
assembly remain open; Theorem 2.5 is not claimed.

## Release 3.50: stationary-point near/far reduction

The new `StationaryFourierSourceBlock.lean` identifies the unique critical
point `-2*B/A` of an opposite-sign quadratic reciprocal phase and factors the
phase derivative exactly through distance from that point. If the critical
point lies in the dyadic interval, the source phase-scale lower bound forces
an explicit lower bound on `|A|`; outside a radius `δ` this becomes a
quantitative derivative lower bound.

The logarithmic integral is split exactly into left-far, central, and
right-far pieces. The central contribution is at most `2*δ/log P`. Completing
the opposite-sign chamber now reduces to cancellation estimates for the two
far integrals, followed by optimization of `δ`. Coordinate-axis modes, low
frequencies, and final Fourier assembly also remain open.

## Release 3.51: optimized interior stationary cancellation

`StationaryFourierSourceBlock.lean` now proves the missing cancellation on
both far pieces. The integration-by-parts identity was generalized to every
interval avoiding the critical linear factor. The amplitude derivative is
monotone on the left and through the first right-hand segment; beyond its
turning point it has the explicit dyadic bound `64*P/(A*log P)`. Splitting
there gives the complete right-far estimate, including its post-turning tail.

Combining the two far bounds with the central length estimate gives a raw
stationary inequality. The source lower bound `A >= (16/5)*P*L` is inserted
exactly, and the choice `δ=P/sqrt L` yields the audited interior estimate
`50*P/(sqrt L*log P)` for `L>=4`. Endpoint-clipped stationary neighborhoods,
the conjugate opposite-sign chamber, coordinate-axis modes, low frequencies,
and final Fourier assembly remain open; Theorem 2.5 is not claimed.

## Release 3.52: complete stationary Fourier chamber

The optimized stationary estimate now permits the critical neighborhood to
meet either integration endpoint. A four-case clipped decomposition uses only
the required one-sided far integral and bounds the remaining central piece by
length, preserving the same `50*P/(sqrt L*log P)` bound.

Stationary-point invariance and complex conjugation transfer the result to the
opposite coefficient orientation, and an absolute-linear-coefficient wrapper
unifies both signs. The result is connected to `fourierModeIntegral` and the
unequal prime theorem, producing the literal prime-minus-integral discrepancy
for every nonzero-coefficient mode whose stationary point lies in the source
interval. Coordinate-axis modes, low frequencies, and final Fourier assembly
remain open; Theorem 2.5 is not claimed.

## Release 3.53: pure quadratic coordinate axis

The new `CoordinateAxisFourierSourceBlock.lean` treats modes with zero linear
coefficient and nonzero quadratic coefficient. A positive-variation form of
the general integration-by-parts lemma gives the dyadic integral bound
`16*P^3/(|B|*log P)`. Since the pure quadratic source scale is exactly
`|B|/(16*P^2)`, this becomes `P/(L*log P)` under scale lower bound `L`.

The result is transported to the literal Fourier integral and combined with
the unequal prime theorem, closing the pure quadratic prime-minus-integral
axis. The pure linear axis requires a separate Type II argument because both
the low-scale quadratic kernel and high-scale Vinogradov callback currently
use a nonzero transformed quadratic coefficient. Low modes and final Fourier
assembly remain open; Theorem 2.5 is not claimed.

## Release 3.54: pure-linear Type II pointwise chamber

The new `LinearAxisTypeII.lean` closes the pointwise Type II obstruction for
zero quadratic coefficient. In this chamber the reciprocal-derivative
critical sets are empty. The high-scale branch therefore applies the existing
conditional `VinogradovExponentialSumEstimate` on the whole interval, with no
critical deletion or component loss. The low-scale branch similarly runs the
internal four-step Weyl estimate on the regular interval directly, and proves
the short-block geometry, far-pair inverse-scale estimate, and effective-error
bound needed for the standard four-kernel decay estimate.

The pure-linear integral side is also available: the dyadic bound is
`6*P^2/(|A|*log P)`, its exact phase scale is `|A|/(4*P)`, and a source lower
bound gives `2*P/(L*log P)`. The pointwise high- and low-scale Type II
correlation estimates have not yet been aggregated through the double-block,
Vaughan, Mangoldt, and prime layers. Those propagation steps, low modes, and
final Fourier assembly remain open; Theorem 2.5 is not claimed.

## Release 3.55: complete pure-linear Type II source family

`LinearAxisTypeII.lean` now lifts the pointwise low/high dichotomy through
arbitrary short double blocks, canonical Vaughan dyadic blocks, and literal
weighted-convolution double blocks. The new
`LinearAxisTypeIISourceBlock.lean` then performs the finite block-family sum,
reuses the audited unequal-parameter scalar majorant compression, and reaches
the fully explicit arbitrary-log-saving Type II source theorem.

Thus the pure-linear Type II branch is complete from correlation estimates to
the canonical Vaughan source family. The two pure-linear Type I families are
now the next analytic obstruction before Vaughan assembly, Mangoldt and prime
propagation, and the literal prime-minus-integral axis discrepancy. Low modes
and final Fourier assembly remain open; Theorem 2.5 is not claimed.

## Release 3.56: complete pure-linear coordinate axis

The new `LinearAxisTypeI.lean` supplies the zero-quadratic low-scale Weyl and
high-scale conditional Vinogradov branches for Type I fibers, then propagates
them through both finite Vaughan Type I source families with explicit
arbitrary logarithmic saving.

`LinearAxisMangoldtSourceBlock.lean` combines those two families with the
complete pure-linear Type II family through the exact Vaughan identity.
`LinearAxisPrimeSourceBlock.lean` removes prime powers and performs reverse
Abel summation. `LinearAxisFourierSourceBlock.lean` finally combines that
prime theorem with the audited `2*P/(L*log P)` integral estimate, yielding the
literal zero-quadratic prime-minus-integral Fourier discrepancy. Both
coordinate axes are now complete. Low modes and final Fourier assembly remain
open; Theorem 2.5 is not claimed.

## Release 3.57: low-frequency discrete-to-continuous bridge

The new `LowFrequencyIntegral.lean` proves the exact elementary bridge from
the logarithmically weighted reciprocal-phase integer sum to its interval
integral. A dyadic inverse-log Lipschitz estimate and the existing phase
variation theorem give the unit-cell error; exact interval additivity and a
cell-count bound then yield
`2*pi*(j+1)*F/log(P) + 1/log(P)^2` on the full interval.

No quantitative PNT is introduced. The next analytic task is the classical
arbitrary-log-saving Mangoldt discrepancy estimate needed to connect this
bridge to primes. The zero mode and final finite Fourier assembly remain
open; Theorem 2.5 is not claimed.

## Release 3.58: quantitative-PNT interface and weighted Abel consumer

`LowFrequencyIntegral.lean` now carries the release-3.57 variation estimate
through Abel summation for `Lambda(n)/log(n)`, producing a direct conditional
Mangoldt/log-to-integral theorem with one explicit partial-sum parameter.

The new `LowFrequencyPNT.lean` states the missing classical PNT input in
global prefix form, proves its uniform dyadic subinterval consequence, and
feeds it into that weighted theorem. The contract remains an explicit
hypothesis. Higher prime powers, the zero mode, and final Fourier assembly
remain open; Theorem 2.5 is not claimed.

## Release 3.59: low-frequency prime and Fourier endpoint

`LowFrequencyPrime.lean` splits the Mangoldt/log sum exactly into the
unweighted prime sum and the higher-prime-power tail. The tail is controlled
by the existing frozen local estimate with arbitrary logarithmic saving.

`LowFrequencyFourier.lean` transports the resulting conditional prime theorem
to the literal Fourier-mode sum and integral and exposes the zero mode
explicitly. Final logarithmic absorption and the finite high/low mode
partition remain. The quantitative-PNT contract is still a hypothesis, and
Theorem 2.5 is not claimed.

## Release 3.60: low-frequency logarithmic absorption

The new `LowFrequencyAbsorption.lean` converts the explicit release-3.59
majorant into `P/(log P)^S` for every fixed target exponent `S`, uniformly for
modes satisfying `reciprocalPhaseScale <= (log P)^D`. The proof supplies the
eventual log-versus-power estimates and checks all three error terms with
explicit constants.

This completes the conditional low-frequency source bound. Quantitative PNT
is still a named hypothesis, and the finite high/low mode partition remains;
Theorem 2.5 is not claimed.

## Release 3.61: exterior stationary and scale-complete same-sign bounds

`StationaryFourierSourceBlock.lean` now treats a stationary point anywhere in
the ambient dyadic block, even when it lies outside the summed subinterval,
and supplies a separate first-derivative bound when it lies at most at
`P/2`. For the specialization `M=N`, the stationary point is the fixed ratio
`-2q₂/q₁` and is uniformly at most `2R` on a radius-`R` Fourier box.

`UnequalFourierSourceBlock.lean` now controls the same-sign integral using the
total phase scale rather than only the linear coefficient. Final finite mode
partition and absorption remain. `LowFrequencyAbsorption.lean` also records
the exact `F(P) <= 16 F(4P)` comparison and its deterministic high/low
dichotomy. Theorem 2.5 is not claimed.

## Release 3.62: specialized all-mode high/low partition

`SpecializedFourierPartition.lean` combines the absorbed PNT branch with the
axis, same-sign, and opposite-sign high-frequency estimates for `M=N`,
`j=2`. It is uniform over every mode in a fixed Fourier box and every natural
half-open dyadic subinterval. A second theorem absorbs all three displayed
majorant terms into an arbitrary target `P/(log P)^S`.

The analytic inputs remain the explicit propositions
`ClassicalMangoldtDiscrepancyLogSaving` and
`VinogradovExponentialSumEstimate`. Finite Fourier summation and the
arbitrary-interval endpoint reduction remain; Theorem 2.5 is not claimed.

## Release 3.63: specialized finite Fourier assembly

`eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving` feeds the
release-3.62 uniform mode theorem into the existing exact finite Fourier
assembly. It uses the actual retained coefficient `ℓ¹` norm and absorbs that
fixed constant with two extra powers of `log P`. Only the reduction from an
arbitrary real order-convex interval to its natural `Ico` core remains in
this specialized polynomial pipeline.

## Release 3.64: arbitrary-interval natural core

`SpecializedIntervalReduction.lean` proves that the natural points of an
order-convex real interval form exactly one `Finset.Ico`. The corresponding
real `Set.Ico` preserves `primesInScaleSet` and
`primeEquidistributionSum` exactly. Its symmetric difference from the
original interval has Lebesgue measure at most two whenever the core is
nonempty. Integral endpoint absorption and the empty-core case remain.

## Release 3.65: arbitrary-interval finite Fourier estimate

`SpecializedIntervalReduction.lean` now completes the endpoint reduction.
It proves a generic symmetric-difference set-integral estimate, caps the
analytic core at `2P` while preserving every sampled prime, handles the
degenerate composite endpoint and the empty-core unit-cell geometry, and
absorbs the resulting endpoint errors. Consequently every fixed finite
Fourier polynomial satisfies the specialized arbitrary-log-saving estimate
on every measurable order-convex real interval in the dyadic block.

The result remains conditional on `ClassicalMangoldtDiscrepancyLogSaving`
and `VinogradovExponentialSumEstimate`. Quantitative reconstruction of a
general smooth periodic weight remains, so Theorem 2.5 is not claimed.

## Release 3.66: exact smooth Fourier-tail reconstruction

`SpecializedFourierReconstruction.lean` transfers the release-3.65
finite-polynomial estimate to a smooth periodic weight with the literal
outer-box coefficient tail. `FourierRadial.lean` bounds that coefficient tail
by `27 * taoC3Norm W` times the universal radial cubic-envelope tail. Thus all
non-tail terms already have arbitrary logarithmic saving on arbitrary real
order-convex intervals.

An explicit rate for the universal tail and a mode theorem uniform for the
corresponding growing Fourier box remain. Theorem 2.5 is not yet claimed.

## Release 3.67: quantitative growing-box reconstruction

`FourierDecayRate.lean` extracts a half power from the radial cubic envelope
outside the square box and sums the remaining radial `5/2` envelope through a
separable `5/4` majorant. Hence the universal tail is at most a fixed summable
constant times `(R+1)^(-1/2)`.

`SpecializedGrowingFourier.lean` uses
`R(P)=ceil((log P)^B)`. Polylogarithmic frequency growth is absorbed by
replacing epsilon with epsilon/2 in the fixed-constant Vinogradov range. The
all-mode partition, finite assembly, natural-core endpoint reduction, and
smooth reconstruction are uniform in the growing box. The final theorem is
`C3`-normalized with one universal reconstruction constant and quantifies the
weight only after the eventual natural-scale threshold.

The two analytic propositions remain explicit hypotheses. A wrapper from
eventual natural scales to every real `P>=2`, together with proofs of those
analytic inputs, remains before Theorem 2.5 is claimed.

## Release 3.68: literal real-scale specialized contract

`SpecializedRealScale.lean` sends a real scale `P` to `ceil(P)` and intersects
the source interval with the corresponding upper ray. It proves exact equality
of the sampled prime sets, a unit bound for the discarded endpoint strip, and
the resulting `taoC3Norm W / log P` integral error. It also transfers the
Vinogradov parameter bound monotonically to the ceiling scale.

The module converts the natural logarithmic saving to every positive real
exponent, then controls the bounded initial range by an explicit elementary
prime-sum/integral estimate. The final declaration
`taoTheorem25Specialized_of_analyticInputs` proves the literal
`TaoTheorem25SpecializedConclusion` from the two named analytic propositions.
No scale or Fourier-reconstruction wrapper remains; only proofs of
`ClassicalMangoldtDiscrepancyLogSaving` and
`VinogradovExponentialSumEstimate` are still needed for an unconditional
specialized Theorem 2.5.

## Release 3.69: classical quantitative-PNT normalization

`QuantitativePNTBridge.lean` restates the low-frequency input in the standard
de la Vallée Poussin form for Chebyshev's `ψ`. It proves the exact endpoint
identity `cumsum Λ k = ψ(k) - Λ(k)`, absorbs the endpoint term, and shows that
the stretched-exponential `ψ` error implies every logarithmic saving required
by `ClassicalMangoldtDiscrepancyLogSaving`.

The declaration
`taoTheorem25Specialized_of_chebyshevPsiDeLaValleePoussin` now proves the
literal specialized conclusion from that classical `ψ` proposition and
`VinogradovExponentialSumEstimate`. The quantitative `ψ` estimate and the
Vinogradov polynomial mean-value input remain analytic obligations.

## Release 3.70: unconditional classical quantitative PNT

`ClassicalQuantitativePNT.lean` assembles the frozen sharp explicit formula,
Ford's proved rectangle-uniform Vinogradov--Korobov zero-free region, and the
proved global Jensen count. A finite low-zero reciprocal constant and a
coarse eventual `N(0,T) <= K*T^2` bound control the zero sum. Choosing
`T=exp(a*sqrt(log x))` with `a=min(1,c/8)` yields the standard eventual
de la Vallee Poussin estimate for `psi(x)-x`.

Consequently `ClassicalMangoldtDiscrepancyLogSaving` is now proved
unconditionally, and `taoTheorem25Specialized_of_vinogradov` has the literal
specialized conclusion with only `VinogradovExponentialSumEstimate` as an
input. The remaining analytic frontier for this specialization is the
uniform critical-VMVT coefficient-growth estimate already isolated by the
Vinogradov modules.

## Release 3.71: unconditional specialized Theorem 2.5 and Theorem 1.8

`VinogradovIKDegree.lean` separates the source's Taylor cutoff from its
effective mean-value degree `k=floor(4 log F/log X)`. It proves that the
degree-`k` remainder is at most one and transfers the shifted Taylor sum at
that smaller degree. `VinogradovIKMeanValue.lean` extracts at least `k^2/25`
of weighted quarter-block mass and converts it into the required coordinate
saving.

`VinogradovIKFord.lean` treats `k>=10000` with an explicit Ford moment;
`VinogradovIKFinite.lean` takes a finite maximum of the already proved native
critical coefficients for `16<=k<10000` and uses the trivial estimate in the
complementary parameter branch. `VinogradovIKComplete.lean` assembles the
local product, pair-sum, and Taylor-transfer bounds, proving
`vinogradovExponentialSumEstimate_unconditional`.

Finally, `Theorem25Complete.lean` combines that theorem with the native
quantitative PNT. The exact specialized Theorem 2.5 conclusion and Tao's
literal Theorem 1.8 conclusion are now unconditional.

`PublicEndpointReductions.lean` also removes Theorem 2.5 from the remaining
Section 4 interfaces: Proposition 2.3(ii) alone implies both Theorem 1.9 and
Theorem 1.10, while the source-facing variants require only the pinned
Baker--Harman--Pintz proposition.

## Release 3.72: explicit tilted saddle local-limit target

`SmoothNumberSaddleTilt.lean` normalizes the exact smooth Dirichlet weights
to total mass one. The log-partition function equals `phiZero`, with first
and second derivatives `-phiOne` and `phiTwo`. It also proves
`Psi(X,y) = exp(phase) * cutoffFactor`, `0 <= cutoffFactor <= 1`, and the
exact saddle-ratio identity with `smoothSaddleGaussianScale`.

`SmoothNumberSaddleLocalLimit.lean` proves that the critical saddle
asymptotic is equivalent to convergence of that explicit normalized cutoff
quantity to one. This release closes the normalization and reduction layer;
the Gaussian local-limit estimate and analytic Burgess remain the two open
inputs for Theorem 1.7.

## Release 3.73: probability-law Fourier bridge

`SmoothNumberSaddleProbability.lean` realizes the tilted masses as a literal
probability measure on `log n`. Its characteristic function is proved equal
to the absolutely convergent Fourier series of the explicit masses, equals
one at zero, and has norm at most one. At the exact saddle, the first two
log-partition derivatives give center `log X` and variance `phiTwo`; the file
defines the centered, variance-normalized characteristic function and proves
its exact Fourier expansion in `(log n - log X) / sqrt(phiTwo)`. Establishing
Gaussian convergence of this series remains open.

## Release 3.74: finite-prime characteristic Euler product

`SmoothNumberSaddleEulerCharacteristic.lean` proves that the unnormalized
complex Fourier Dirichlet series is absolutely summable and factors exactly
as a finite Euler product. After division by the untwisted normalizer, the
tilted characteristic function is the literal product over `p ≤ y` of
`(1-p^(-sigma))/(1-p^(-sigma) exp(i t log p))`.

Every local factor has norm at most one. Its squared norm is proved equal to
`(1-a)^2 / ((1-a)^2 + 2a(1-cos(t log p)))`, where `a=p^(-sigma)`. Consequently
the centered variance-normalized saddle characteristic function has an exact
finite contraction product. Uniform estimates for this product and the
local-limit inversion remain open.

## Release 3.75: central Gaussian frequency envelope

`SmoothNumberSaddleFrequency.lean` turns the exact contraction product into
quantitative decay. On `|theta| ≤ pi`, the checked inequality
`1-cos(theta) ≥ 2 theta^2/pi^2` gives a quadratic local contraction. On the
central subwindow this is bounded by a Gaussian exponential, whose coefficient
is proved exactly equal to the corresponding `phiTwo` summand.

Multiplication gives
`|characteristic(t)|^2 ≤ exp(-2 t^2 phiTwo/pi^2)`. At the exact saddle,
variance normalization cancels `phiTwo`, producing the universal bounds
`|characteristic(t)|^2 ≤ exp(-2t^2/pi^2)` and
`|characteristic(t)| ≤ exp(-t^2/pi^2)` under one explicit source-scale range
condition. Proving that a sufficiently growing normalized window satisfies
this condition, and controlling the remaining frequencies, are next.

## Release 3.76: explicit finite central window

`SmoothNumberSaddleCentralWindow.lean` packages that condition as the exact
positive radius
`pi/2 * (1-2^(-sigma)) * sqrt(phiTwo) / log y`. Membership in the symmetric
interval is equivalent to the source-scale hypothesis, so both Gaussian
envelopes hold everywhere on it.

The module also isolates the remaining asymptotic input: if
`log y / sqrt(phiTwo) → 0` in the critical regime, then the radius tends to
infinity, every fixed normalized frequency eventually lies in the window,
and the pointwise Gaussian envelope follows. Proving this sharper curvature
limit and treating complementary frequencies remain open.

## Release 3.77: expanding critical central window

`SmoothNumberSaddleCurvatureLower.lean` proves the missing curvature limit.
The comparison point `1-8 log(u)/log(y)` lies below the exact saddle. Since
`phiTwo` is antitone, the exact secant identity then gives the eventual bound
`phiTwo/log(y)^2 ≥ u/(16 log u)`.

Consequently normalized curvature tends to infinity,
`log(y)/sqrt(phiTwo) → 0`, and the release-3.76 radius tends to infinity
unconditionally in every critical regime. Every fixed normalized frequency
therefore eventually satisfies the universal Gaussian envelope. The remaining
local-limit work is complementary-frequency decay and Fourier inversion.

## Release 3.78: Gaussian finite-product transfer

`SmoothNumberSaddleGaussianProduct.lean` factors the normalized saddle
characteristic exactly into centered prime-local factors and proves a
quantitative triangular-array product theorem. The nonnegative prime variance
shares sum to one, while every share is at most
`20 log(y)^2 / phiTwo`; release 3.77 makes this uniform bound tend to zero.

Consequently fixed-frequency convergence to `exp(-t^2/2)` is reduced to one
explicit statement: the sum of the prime-local quadratic Taylor remainders
tends to zero. Proving that local geometric-factor estimate is the remaining
central-frequency step. Complementary-frequency decay and Fourier inversion
also remain open.

## Release 3.79: prime-local Taylor closure

`SmoothNumberSaddlePrimeTaylor.lean` proves exact geometric prime-power
moments, bounds the third absolute centered moment by `4000a`, and establishes
a global cubic remainder for `exp(ix)`. The centered geometric characteristic
is identified with the existing prime-local saddle factor, giving total error
at most `16000 |t|^3 log(y)/sqrt(phiTwo)`.

This tends to zero in every critical regime, so the normalized saddle
characteristic converges to `exp(-t^2/2)` at each fixed frequency.
Complementary-frequency decay and Fourier inversion remain open.

## Release 3.80: one-sided Laplace cutoff

`SmoothNumberSaddleLaplaceCutoff.lean` identifies the cutoff factor as a
one-sided Laplace moment of the normalized logarithmic displacement. The
Laplace rate is `sigma*sqrt(phiTwo)`, the Gaussian prefactor is
`sqrt(2*pi)` times this rate, and the rate diverges. The source saddle
asymptotic is exactly equivalent to convergence of this normalized target;
the remaining task is shrinking-scale Fourier control and inversion.

## Release 3.81: central saddle integral

`SmoothNumberSaddleCentralIntegral.lean` defines the exact normalized
Laplace kernel and the characteristic-function integrand cut off to the
explicit central radius. The kernel has norm at most one and tends to one;
the characteristic factor supplies the uniform `exp(-t^2/pi^2)` envelope
and converges pointwise to `exp(-t^2/2)`.

Dominated convergence evaluates the expanding central integral as
`sqrt(2*pi)`, hence its normalized Laplace contribution tends to one. The
remaining smooth-number boundary is the truncated Perron identity and its
complementary-frequency error.

## Release 3.82: exact normalized Perron line

`SmoothNumberSaddlePerronLine.lean` defines the original vertical-line
central height and the normalized twisted-Dirichlet-series integrand. It
proves exact equality with the centered characteristic/Laplace kernel under
`u=-t*sqrt(phiTwo)`, including the source denominator `sigma+i*t`.

The standard-deviation change of variables maps both interval endpoints
exactly and identifies the normalized central Perron integral with the
release-3.81 contribution. The sharp cutoff error and complementary line are
the remaining saddle tasks.

## Release 3.83: smooth sharp-Perron cutoff

`SmoothNumberSaddlePerronCutoff.lean` proves absolute termwise integration of
the smooth Dirichlet series and equates the normalized finite vertical line
with a summable series of frozen sharp-Perron kernels. Its inclusive subtype
cutoff sums exactly to `psiNat`, yielding the exact cutoff-error decomposition.

The strict lower and upper ranges inherit the frozen logarithmic bounds, and
the endpoint has uniform error at most `3/2`. Aggregation at the saddle height
and the noncentral line are the remaining tasks.

## Release 3.84: symmetric Perron inversion

`SmoothNumberSaddlePerronLimit.lean` proves the large-height kernel limits
`1`, `1/2`, and `0` below, at, and above the cutoff. A summable uniform
envelope upgrades the pointwise result by Tannery's theorem to the full smooth
Dirichlet series. Its limit is exactly `psiNat X y` minus the possible
source-smooth endpoint half-mass, and that correction has norm at most `1/2`.

The endpoint convention behind Granville's `O(1)` is therefore exact. What
remains is the saddle-scale estimate for the noncentral part of the finite
vertical line.

## Release 3.85: complementary Perron line

`SmoothNumberSaddlePerronComplement.lean` normalizes the complete finite
Perron line by the saddle main term and proves it equals the frozen-kernel sum
with the identical normalization. Removing the central contribution gives
exactly the two tail integrals outside the central height.

The large-height limit of this complement is the half-endpoint-corrected
saddle ratio minus the central Gaussian term. Critical-regime convergence of
the corrected ratio is therefore equivalent to vanishing of this explicit
infinite complement. The normalized endpoint is bounded by
`1/(2*mainTerm)`. Proving complementary-line decay and main-term divergence
are the remaining steps in this saddle closure.

## Release 3.86: saddle main-term growth

`SmoothNumberSaddleMainTermGrowth.lean` bounds the critical curvature by
`7*log(y)*log(X)` and proves the concrete lower bound
`sqrt(X)/(sqrt(14*pi)*log(X)) <= smoothSaddleMainTerm`. It follows that the
main term tends to infinity in every critical regime and the normalized
Perron endpoint correction tends to zero.

Consequently the source-facing, uncorrected critical saddle asymptotic is
equivalent to vanishing of the explicit infinite complementary Perron line.
Only that complementary-frequency decay remains.

## Release 3.87: wide-frequency annular decay

`SmoothNumberSaddleWideFrequency.lean` proves a prime-local exponential
contraction throughout the full phase range `|t log p| <= pi`, multiplies it
over the finite Euler product, and obtains
`|characteristic(t)| <= exp(-t^2/(48*pi^2))` whenever
`|t|*log(y)/standardDeviation <= pi`.

The induced annular integrand is measurable, Gaussian dominated, and
eventually zero at each fixed frequency because its inner central radius
diverges. Dominated convergence therefore makes its complete integral tend
to zero. Frequencies outside `pi/log(y)` on the physical Perron line remain.

## Release 3.88: physical wide-Perron interface

`SmoothNumberSaddleWidePerron.lean` proves the exact signed interval
substitution from the normalized annulus to the two literal Perron-line
segments. Its wide physical height is `pi/log(y)`, and the corresponding
normalized contribution tends to zero in every critical regime. Only the two
outer line integrals beyond this height remain.

## Release 3.89: named outer Perron tails

`SmoothNumberSaddleOuterPerron.lean` defines the two tails beyond
`pi/log(y)`, proves the exact finite complementary-line decomposition, and
identifies their infinite-height limit. Since the intervening annulus tends
to zero, the critical saddle asymptotic is equivalent to decay of the named
infinite outer line alone.

## Release 3.90: global outer-frequency decay envelope

`SmoothNumberSaddleOuterDecay.lean` defines exact prime-local and aggregate
phase losses. A global reciprocal estimate gives
`|smoothTiltedCharacteristic| <= exp(-smoothSaddleCosineLoss/96)` at every
frequency and transfers this bound to the physical Perron integrand. The
remaining analytic input is now a quantitative lower bound for that explicit
weighted cosine loss on the outer frequency range.

## Release 3.91: first outer shell

`SmoothNumberSaddleOuterShell.lean` combines the top dyadic prime block with
the global cosine-loss envelope. Throughout
`[pi/log(y), 4*pi/(3*log(y))]`, every block prime contributes loss at least
one, and the existing Chebyshev–PNT estimates give the explicit lower bound
`y^(-sigma)*y/(16*log(y))`. Further shells remain to be assembled.

## Release 3.92: adaptive outer shell

`SmoothNumberSaddleMovingShell.lean` selects the prime scale
`N(t)=ceil(exp(pi/t))`. Its certified ceiling bounds place
`pi/log(N(t)) <= t <= 4*pi/(3*log(N(t)))` throughout an explicit
small-frequency range, while the outer boundary guarantees `N(t) <= y`.
A large Chebyshev--PNT threshold and a finite logarithmic half-block estimate
then feed the release-3.91 block theorem at this moving scale, giving
`N(t)^(-sigma)*N(t)/(16*log(N(t))) <= smoothSaddleCosineLoss`. Uniform
assembly beyond the controlled small-frequency range and integration of the
complete outer line remain.

## Release 3.93: accumulated first-shell loss

`SmoothNumberSaddleMultiShell.lean` uses the full CEP dyadic alphabet below
`y`. Every retained prime remains in the negative-cosine window on the first
outer shell, and the accumulated reciprocal mass is `≫ 1/log(u)`. Explicit
saddle and cutoff bounds produce a named loss scale `≫ u/log(u)`, prove that
it tends to infinity in every critical regime, and give uniform decay of the
literal Perron integrand on this shell. Integration with the growing saddle
prefactor and coverage of later shells remain.

## Release 3.94: integrated first outer shell

`SmoothNumberSaddleFirstShellIntegral.lean` defines the exact symmetric
normalized Perron contribution on
`pi/log(y) <= |t| <= 4*pi/(3*log(y))`. Its two intervals have total width
`2*pi/(3*log(y))`; the release-3.93 envelope bounds their integrand, while
the curvature estimate gives
`smoothSaddleStandardDeviation/log(y) <= sqrt(7*u)`. The elementary limit
`sqrt(u)*exp(-c*u/log(u)) -> 0` therefore absorbs the complete normalization,
and the first outer-shell contribution tends to zero in every critical
regime. Later outer-frequency shells and the infinite tail remain.

## Release 3.95: extended first-shell band

`SmoothNumberSaddleExtendedShell.lean` sharpens the accumulated-alphabet
phase window to its exact endpoint `3*pi/(2*log(y))`. It introduces a
reusable symmetric-shell integral and norm bound, then applies the same
divergent `u/log(u)` loss to the newly covered adjacent band from
`4*pi/(3*log(y))` to `3*pi/(2*log(y))`. That normalized contribution also
tends to zero in every critical regime. Frequencies beyond the new endpoint
and the infinite outer tail remain.

## Release 3.96: square-root second shell

`SmoothNumberSaddleSecondShell.lean` moves the accumulated CEP alphabet to
`floor(sqrt(y))`. Its logarithm is eventually between `2/5*log(y)` and
`1/2*log(y)`, while the retained alphabet begins above one third of the top
logarithmic scale. Consequently every retained prime has nonpositive cosine
throughout `3*pi/(2*log(y)) <= t <= 3*pi/log(y)`. The CEP mass theorem gives
an explicit accumulated loss on this whole second shell. Conversion of that
loss to a divergent normalized envelope and integration remain.

## Release 3.97: integrated second outer shell

`SmoothNumberSaddleSecondShellIntegral.lean` compares the square-root
cofactor power with `(u/(15*log(4)))^(2/5)` and packages the resulting
cosine loss as a named scale of order `u^(2/5)/log(u)`. The scale diverges,
and a direct exponential-absorption lemma shows that its envelope dominates
the `sqrt(u)` normalization. Applying the reusable symmetric-shell estimate
proves that the exact contribution on
`3*pi/(2*log(y)) <= |t| <= 3*pi/log(y)` tends to zero in every critical
regime. Later frequencies and the infinite outer line remain.

## Release 3.98: fourth-root third shell

`SmoothNumberSaddleThirdShell.lean` moves the CEP alphabet to
`floor(sqrt(floor(sqrt(y))))`. Explicit rounding estimates place the scale
between logarithmic exponents `1/5` and `1/4`, while the retained primes
start at exponent `1/6`. The full alphabet consequently has nonpositive
cosine from physical height `3*pi/log(y)` through `6*pi/log(y)`. Critical
growth discharges its PNT and cofactor hypotheses, giving a uniform explicit
loss on this third shell. Its normalized integral remains to be proved.

## Release 3.99: integrated third outer shell

`SmoothNumberSaddleThirdShellIntegral.lean` compares the fourth-root
cofactor power with `(u/(15*log(4)))^(1/5)`, proves the resulting
`u^(1/5)/log(u)` loss diverges, and shows its exponential envelope absorbs
`sqrt(u)`. Cosine-loss symmetry and the generic symmetric-shell norm bound
then make the exact contribution on
`3*pi/log(y) <= |t| <= 6*pi/log(y)` tend to zero. Later frequencies and the
infinite outer line remain.

## Release 4.00: eighth-root fourth shell

`SmoothNumberSaddleFourthShell.lean` introduces the third iterated natural
square root. Its logarithmic support is certified between exponents `1/12`
and `1/8`, placing the complete retained CEP alphabet in the
negative-cosine half-circle throughout
`6*pi/log(y) <= t <= 12*pi/log(y)`. The resulting accumulated loss and all
critical-regime range hypotheses are formal. Divergent-scale conversion and
integration remain.

## Release 4.01: integrated fourth outer shell

`SmoothNumberSaddleFourthShellIntegral.lean` proves the eighth-root loss is
of order `u^(1/9)/log(u)`, diverges, and exponentially absorbs `sqrt(u)`.
The signed envelope and symmetric-shell estimate then show that the exact
normalized band through `12*pi/log(y)` tends to zero.

## Release 4.02: indexed shell infrastructure

`SmoothNumberSaddleIndexedShell.lean` defines arbitrary iterated natural
square-root alphabets, proves their recursive and closed-form logarithmic
bounds, and packages the doubling physical shell heights. The existing
second, third, and fourth scales and endpoints are recovered exactly.

## Release 4.03: uniform indexed phase loss

`SmoothNumberSaddleIndexedPhase.lean` converts one `4/5` lower scale bound
into the retained-prime support, exact `[pi/2,3*pi/2]` phase window, and full
CEP accumulated loss for every indexed shell `k >= 2`.

## Release 4.04: indexed scale range

`SmoothNumberSaddleIndexedScaleRange.lean` proves antitonicity of iterated
roots and converts the exact rounding ledger into the criterion
`10*(2^k-1)*log(2) <= log(y)`, which implies the uniform four-fifths scale
bound whenever the terminal root has not collapsed below four.

## Release 4.05: fixed-depth indexed admissibility

`SmoothNumberSaddleIndexedFixedDepth.lean` identifies terminal noncollapse
exactly with `a^(2^k) <= y`. Thus every fixed depth survives eventually in a
critical regime, and divergence of `log(y)` makes the release-4.04 rounding
criterion automatic. The resulting theorem packages terminal noncollapse
and both logarithmic scale bounds needed by the indexed phase theorem.

## Release 4.06: fixed-index critical phase loss

`SmoothNumberSaddleIndexedFixedLoss.lean` proves that every fixed iterated
scale eventually dominates the square of the critical Rankin ratio. Together
with fixed-depth admissibility, this discharges all hypotheses of the uniform
indexed phase theorem and yields the full CEP cosine-loss bound on the exact
physical shell at each fixed index `k >= 2`.

## Release 4.07: growing indexed diagonal

`SmoothNumberSaddleIndexedDiagonal.lean` proves finite-prefix simultaneous
control and then diagonalizes. The selected depth tends to infinity, while
all shells from index two through that moving depth satisfy the full
critical-regime cosine-loss estimate together. Integral aggregation and the
tail beyond the terminal indexed height remain.

## Release 4.08: explicit indexed loss scale

`SmoothNumberSaddleIndexedLossScale.lean` assigns shell `k` the positive
exponent `(4/5)*2^(-k)`. It converts the CEP cutoff power to an explicit
Rankin-ratio loss, proves that loss bounds the cosine sum throughout every
fixed indexed shell eventually, and proves its divergence in each fixed
index.

## Release 4.09: fixed indexed shell integrals

`SmoothNumberSaddleIndexedShellIntegral.lean` proves the general exponential
absorption theorem needed for arbitrary positive fixed shell exponents,
extends the indexed envelope across both frequency signs, and integrates the
exact symmetric shell. Every fixed indexed Perron contribution tends to zero
in every critical regime.

## Release 4.10: vanishing growing indexed prefix

`SmoothNumberSaddleIndexedPrefix.lean` proves every fixed finite shell sum
vanishes and applies a second slow diagonal to the norm of the entire prefix.
The resulting depth tends to infinity, the moving prefix tends to zero, and
all included shells simultaneously retain their cosine-loss estimates.

## Release 4.11: telescoped indexed segment

`SmoothNumberSaddleIndexedTelescoping.lean` proves adjacent normalized
symmetric shells concatenate exactly. The vanishing moving prefix is
therefore one contiguous Perron segment from indexed height one through a
terminal indexed height whose index tends to infinity.

## Release 4.12: exact post-terminal remainder

`SmoothNumberSaddlePostTerminalTail.lean` joins all controlled outer pieces
before indexed height one and proves their combined contribution tends to
zero. The infinite outer line is then decomposed exactly into this
pre-indexed segment, the vanishing moving indexed segment, and one named
post-terminal tail. The critical smooth-number saddle asymptotic is
equivalent to decay of that final tail along the supplied slow diagonal.

## Release 4.13: indexed-height ceiling

`SmoothNumberSaddleIndexedHeightCeiling.lean` converts terminal scale
survival into the exact inequality
`indexedHeight <= 3*pi/(2*log 4)`. It then proves that any growing index with
an eventually admissible terminal scale has bounded physical height and
therefore cannot tend to infinity. This formally rules out completing the
post-terminal tail by iterating the existing root-shell construction alone.

## Release 4.14: Hildebrand--Tenenbaum envelope

`SmoothNumberSaddleHildebrandTenenbaumEnvelope.lean` names the original
minor-arc loss `u*t^2/((1-sigma)^2+t^2)`, proves its radial monotonicity, and
formulates the finite-range characteristic estimate of HT Lemma 8(ii). That
contract controls the exact Perron integrand and integrates to an explicit
finite symmetric-shell envelope, including a sequence-level convergence
theorem. Proving the contract and the compatible truncation error remains.

## Release 4.15: HT Mangoldt transform

`SmoothNumberSaddleHTMangoldtTransform.lean` defines the finite complex
Mangoldt transform and the corresponding weighted cosine sum from HT Lemma
6. It proves the exact real-part subtraction identity and the sharp algebraic
fact that two transform errors bounded by `E` yield cosine error at most
`2E`.

## Release 4.16: exact HT Lemma 6 interface

`SmoothNumberSaddleHTLemmaSix.lean` records the source frequency ceiling
`exp((log y)^(3/2-epsilon))` and the exact equation-(3.10) error scale as a
named uniform transform proposition. It computes the complex main term's
zero-frequency value, real part, and norm, gives the Cartesian cosine main
term, and derives the full cosine corollary from that proposition. The
shifted Perron/zero-free-region proof of the proposition remains.

## Release 4.17: HT prime-power bridge

`SmoothNumberSaddleHTPrimePowerBridge.lean` splits the Mangoldt cosine sum
exactly into its prime and higher-prime-power parts. The prime part is at
most `log y` times the Euler-product cosine loss, while the tail is at most
twice an explicit nonnegative remainder. Thus the exact Lemma 6 contract now
implies a checked lower bound for the loss used by Lemma 8(ii). Bounding that
remainder at the source strength remains.
