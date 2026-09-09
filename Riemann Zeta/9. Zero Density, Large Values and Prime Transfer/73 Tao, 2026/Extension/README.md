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
off-diagonal bound yields the final real squared-inner-sum inequality.
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
coordinate. The radial comparison and `taoC3Norm` bridge remain.
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
Establishing the paper's precise
polylogarithmic scale/count envelopes and the analytic cancellation theorem
remain open.
The prime/Mangoldt conversion is exact: the prime-logarithm phase sum and
higher-prime-power tail are split in `PrimePowerReduction`, and unit modulus
reduces the tail to the frozen explicit local prime-power bound.
None of Theorems 1.7--1.10 is complete or claimed. Imports from
node 74 enter only through the exact immutable snapshot under `Dependencies/`.
