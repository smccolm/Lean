# Tao2026 Lean package

This isolated package contains the active node-73 formalization. The production
root currently imports source-faithful arithmetic-anatomy, interval, literal
counting, and asymptotic-language definitions. It is pinned to Lean `v4.30.0`
and Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The package proves Proposition 2.3(i),(iii), the exact one-term `B¹` and `VB¹`
counts, the full `VB¹` zeta-ratio asymptotic, Lemma 3.2, the complete signed
and uniform Lemma 2.10, and the complete `x^(2/5+o(1))` Corollary 2.11. It
also compiles the exact Theorem 2.5 summation/integral contract and proves the
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
strict inequality.
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
most `1/K`; in the quadratic case this is now derived from the explicit
monomial inequality `5q|N|≤K^5R^2`. The kernel and Weyl layers now accept arbitrary positive block
endpoints and are specialized to the exact named dyadic Vaughan blocks. The
effective-error family is reduced to one explicit scalar bound, and the
logarithmic Vaughan width proves `5q≤K`, which supplies the expansion margin
on every band above the subdivision budget. The canonical dyadic theorem
therefore exposes `5q|N|≤K^5R^2`, rather than an abstract block-error
hypothesis. It also derives the complete effective-error condition from the
source-faithful near/far split: scaled distance at most three is absorbed by
the kernel's `1/4` lower bound, while farther pairs have reciprocal transformed
scale at most `2/3` and use a `1/4` upper-scale budget. That budget follows
from `E≤1/K`, and `2≤log Bcap` automatically makes the common subdivision
budget large enough. The remaining source inequalities,
high-transformed-scale case, and singleton-band branch are not yet claimed.
The prime/Mangoldt conversion is exact: the prime-logarithm phase sum and
higher-prime-power tail are split in `PrimePowerReduction`, and unit modulus
reduces the tail to the frozen explicit local prime-power bound.
None of Theorems 1.7--1.10 is complete or claimed. Imports from
node 74 enter only through the exact immutable snapshot under `Dependencies/`.
