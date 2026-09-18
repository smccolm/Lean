# Tao 2026 build tools

`Probes/` is reserved for non-production API experiments. Such files are
excluded from the production import graph; any result used by the formalization
must be promoted to `Extension/Tao2026/` and audited there.

`run_tao_build.ps1` verifies the pinned Tao source artifacts, all 1,339 frozen
dependency hashes and their exact file set, the raw Mermaid contract, Lean and
dependency pins, direct production-root coverage, forbidden proof shortcuts,
the current axiom audit, and a warning-free build. It currently certifies only
Proposition 2.3(i),(iii), the exact `B¹`/`VB¹` sums, the factorial
endpoint/counting bridge, and the `F₃¹` square-family lower bound, including
its reverse-big-O transfer to the `F₃` and factorial-triple counts. It also
certifies the dominated-convergence limit, square-times-squarefree series
identity, zeta identification, and exact `ζ(3/2)/ζ(3) √x` asymptotic for
`VB¹`. It is not
yet the final
proof-release verifier described by `Tao Goal Prompt.md`.
The audit also covers the positive-start first clause of Lemma 3.1 and the
complete Lemma 3.2 proof: canonical extraction, coefficient-product
divisibility, finite Abel/Chebyshev bounds, polynomial selection, and the
nonzero-shift powerful relation.
It also covers the complete Theorem 1.8 finite/asymptotic assembly conditional
only on Theorem 2.5: the injective interval encoding, explicit subpolynomial
length and coefficient budgets, uniform Corollary 2.11 family count, and final
zeta-ratio endpoint.
It also covers the complete Lemma 2.10 and Corollary 2.11 chains: the concrete
quadratic maximal-order construction, sharp ideal-divisor count, rank-one
unit and height estimates, signed square-solution theorem, exact dyadic
powerful-number fibers, interpolation, and the uniform signed `≪ x` endpoint.
It now also audits the complete Lemma 4.3 chain: canonical square extraction,
prime support, exact coefficient-product divisibility, its logarithmic
Chebyshev bound, two-half averaging, and the final explicitly bounded smooth
square relation.
The Section 4 audit additionally covers the exact nontrivial endpoint and
interval finsets, structured chosen certificates, injective interval codes,
uniform Lemma 2.10 rounding budget, and the arbitrary-`A,C,G` finite endpoint
bound used by the pending Theorem 1.9 case split. It also checks the literal
easy/hard interval partition and additive endpoint-count reduction. The
bounded-length refinement is audited too: exact smooth-pair cardinality,
chosen-certificate membership, injective code range, and the final
`A·psiNat(x,P)²·G³` endpoint bound. It additionally audits the iterated
retained-smooth square decomposition, its Chebyshev-based logarithmic
`psiNat=x^o(1)` consequence, and the unconditional `x^o(1)` closure of every
fixed-bounded-length endpoint family.
For Theorem 2.5 it now certifies the exact source contract, reciprocal-phase
derivative and coefficient bounds, Type I/II phase rescalings, and Vaughan's
identity in convolution, nested-divisor, and weighted reciprocal-phase forms.
It also certifies the exact finite reindexing of divisor-antidiagonal sums into
bounded product boxes with `m*n∈I`, including the resulting product-restricted
form of all three Vaughan convolution terms.
Those bounded product sums are audited through exact short outer-block and
double-block coefficient decompositions, with `m*n∈I` retained.
It additionally audits bidirectional finite Abel summation: the explicit
logarithmic loss used for the alternate Type I form and the reciprocal-log
loss used to remove the prime logarithmic weight.
The low-frequency audit also covers the explicit reciprocal-phase derivative
and additive-character dyadic total-variation bounds in terms of `F`, the
complex Abel identity, and the exact Mangoldt-minus-integer phase comparison
from a uniform `Λ-1` partial-sum bound. It also audits the frozen `WeakPNT`
bridge to global `o(k)`, uniform dyadic `o(P)`, and the fixed-bounded-scale
`o(P)` phase comparison.
It also audits the exact finite two-dimensional Fourier-mode evaluation,
prime-sum/integral interchange, coefficient-weighted error aggregation, and
integer-frequency Vinogradov-parameter rescaling. It verifies automatic
mode-integrability on the source interval and the exact `(2R+1)²` retained-box
mode count with its uniform-envelope discrepancy bound. The audit also covers
continuous-weight integrability and the explicit uniform-approximation
transfer costs for both the prime sum and logarithmic integral.
Nested finite Fourier truncations are audited through their exact discarded
coefficient `ℓ¹` tail and the resulting full discrepancy bound.
The audit also covers summability of the source cubic `ℤ²` coefficient
envelope, exhaustion by square frequency boxes, vanishing outer-box tails,
and uniform convergence of finite polynomials to their infinite series. It
also checks the open-quotient descent of continuous periodic plane weights,
compatibility of the plane and torus character conventions, and conditional
uniform Fourier reconstruction of the original weight. The axiom audit also
covers the exact one-step and three-step periodic integration-by-parts
identities, both Fubini factorizations of the actual torus coefficient, both
real-slice coefficient identities, and the resulting directional cubic
coefficient estimates. It also audits derivative periodicity and compact-square
boundedness, the automatically generated pure coordinate chains, and the
unconditional radial `taoC3Norm` coefficient estimate with constant `27`.
It audits the finite shorter-than-dyadic quotient-block sum identity, ceiling
block-count estimate, strict within-block diameter, supported-coefficient
restriction, exact pointwise and finite weighted-sum decompositions, and
preservation of uniform coefficient norm bounds as well.
It checks the exact `j=1` absorption into `j=2, M=0` at the pointwise and
finite prime-sum levels.
It also audits the exact Type II finite Cauchy--Schwarz, double-correlation,
outer-sum rearrangement, and coefficient-envelope reductions. The
diagonal/off-diagonal split, exact diagonal correlation `#K`, trivial diagonal
bound, coefficient-explicit off-diagonal norm reduction, and the
`#S(#S-1)` uniform-correlation propagation are audited too.
The off-diagonal transformed-parameter nonvanishing lemmas are audited as
well.
The audit also covers their exact absolute-size and support-bound estimates,
the product-scale normalization and dyadic `j·2^(j-1)` specialization,
the literal `mn∈I` restricted inner sum, its rearrangement onto
`K ∩ (1/n)I ∩ (1/n')I`, the exact restricted split and diagonal bound, and
the uniform-correlation-to-real-squared-sum conclusion.
The Type II decay-kernel audit also includes exact regrouping by natural
distance, the at-most-two distance-fiber bound, and the resulting factor-two
bound for nonnegative kernels, plus nonnegativity, zero normalization, and
antitonicity of the source real-power decay kernel and its finite
sum-to-integral comparison. Its affine-rpow antiderivative, exact integral
evaluation, exact source-scale normalization, endpoint absorption under
`1 ≤ R * F^(-c)`, and final factor-two finite-support correlation bound are
audited as well. The unconditional `1 + O(R * F^(-c))` form and the
distance-zero lower-bound obstruction to dropping the endpoint are audited.
For the actual erased-center off-diagonal support, it additionally audits the
empty zero-distance fiber, direct positive-distance integral bound, pure
`R * F^(-c)` estimate without an endpoint hypothesis, and propagation through
the full and short-block squared-inner-sum reductions. The audit also checks
the source-shaped kernel-plus-error summation over exact
ordered off-diagonal pairs and its final propagation into the
product-restricted squared-inner-sum inequality.
The actual short-inner-block and exact Vaughan double-block specializations of
the endpoint-free source-scale estimate,
including automatic distance and nonzero-index side conditions, are audited.
The quotient-block cardinality bound and the resulting final estimate with
both support sizes replaced by their explicit block lengths are audited too.
The separate Type II arithmetic audit covers generic real-power logarithmic
absorption and its `log P`/strict-high-frequency source specializations.
The Type I variable-support rescaling and coefficient-envelope triangle
reduction are audited as well.
The derivative critical expression and its two-point separation algebra are
also audited; this does not yet include the interval-diameter estimate.
It does not yet certify the analytic exponential-sum or equidistribution
estimate.
The root-level `ProbeBase.lean` and `ProbeRam.lean` files are explicitly
development-only and excluded from production-root coverage pending owner
permission to remove them; they are not imported by `Tao2026.lean`.

`refresh_gafnitao_snapshot.ps1` reconstructs the exact recursive import
closures of `GafniTao.Theorem11` and the native Wooley VMVT bridge from node
74, including `public import`
declarations, and regenerates the per-source SHA-256 manifest. Run it only as
an intentional dependency-update operation and review all resulting changes.

Release 4.05 adds the fixed-depth indexed-shell arithmetic and eventual
critical-regime scale package to both the production root and axiom audit;
the canonical build continues to check these through root reachability,
warning failure, and the semantic-regression gates.

Release 4.06 additionally audits the fixed-index Rankin/cofactor comparison
and the resulting critical-regime indexed cosine-loss theorem.

Release 4.07 audits the finite-prefix intersection and the growing shell
depth selected through the frozen countable-diagonal theorem.

Release 4.08 audits the generic indexed Rankin-power loss scale and its
fixed-index critical-regime divergence.

Release 4.09 audits the generic exponential absorption and vanishing fixed
indexed symmetric Perron contribution.

Release 4.10 audits the finite-prefix convergence and the second slow
diagonal that makes the complete moving shell sum vanish.

Release 4.11 audits exact symmetric-shell concatenation and the resulting
vanishing contiguous moving Perron segment.

Release 4.12 audits the pre-indexed concatenation, its critical-regime
vanishing, the exact post-terminal remainder decomposition, and the
equivalence between decay of that remainder and the critical saddle
asymptotic.

Release 4.13 audits the absolute indexed physical-height ceiling and the
resulting impossibility of an admissible indexed terminal height tending to
infinity.

Release 4.14 audits the Hildebrand--Tenenbaum minor-arc loss, its symmetry
and radial monotonicity, the exact characteristic-to-Perron transfer, and the
finite symmetric-shell integration theorem.

Release 4.15 audits the HT complex Mangoldt transform, its exact cosine-sum
real-part identity, and the two-error stability estimate.

Release 4.16 audits the exact HT Lemma 6 frequency ceiling and error scale,
the complex main-term formulas, and the deduction of the cosine corollary
from the named uniform transform estimate.

Release 4.17 audits the exact prime/prime-power decomposition of the HT
cosine sum and its conversion to the Euler-product cosine-loss lower bound.

Release 4.18 audits the exact prime-power exponent decomposition, its
geometric slice bounds for `sigma>=1/2`, the finite geometric-series
estimate, and the resulting explicit `O(log y)` HT Lemma 5 remainder bound.

Release 4.19 audits the phase-uniform HT cosine-main-term lower bound and its
explicit combination with the Lemma 6 bridge and prime-power remainder.

Release 4.20 audits the canonical finite Abel saddle comparison and the
resulting source-shaped Rankin-ratio lower bound for the HT cosine main term.

Release 4.21 audits the exact theta-Abel identity, its uniform Chebyshev
main-scale bound, and the resulting cutoff-free saddle/HT comparison.

Release 4.22 audits the exact HT source-coordinate Dirichlet-sum and main-term
identities, shifted-Perron contract equivalence, and finite psi-Abel formula.

Release 4.23 audits the shifted initial-line series/integral interchange,
zeta logarithmic-derivative identity, exact source cutoff, and termwise
finite-height Perron error formula.

Release 4.24 audits the translated zeta-surrogate integrand, its single-pole
residue theorem, the exact four-edge rectangle decomposition, and the
source-coordinate specialization.

Release 4.25 audits the translation of the native Vinogradov--Korobov
rectangle to HT coordinates, the resulting surrogate nonvanishing theorem,
and extraction of native positive zero-free constants.

Release 4.26 audits the concrete HT contour shift, height, and initial line;
their exact decay and power identities; and the assembled equality reducing
the transform error to contour-edge and sharp-Perron truncation remainders.

Release 4.27 audits the exact VK denominator computation, log-versus-power
width comparison, factor-three height transfer, uniform actual-height width,
and native eventual contour decomposition in the large-beta branch.

Release 4.28 audits the shifted coefficient norm, optimized-exponent power
cancellation, all three cutoff locations, summability of the scalar
truncation majorant, and its control of the complete complex remainder.

Release 4.29 audits the integral-cutoff reciprocal-distance bounds, the
endpoint-plus-Dirichlet-series domination of the complete scalar majorant,
the frozen explicit `log y+C` estimate, and the resulting source-height
bound for the complete complex truncation remainder.

Release 4.30 audits the finite harmonic weight, its half-integral comparison
and eight-harmonic mass bound, the additive near and Dirichlet far estimates,
their complete scalar summation, and the harmonic-strength source-height
truncation bound.

Release 4.31 audits the stretched-exponent gap, fixed logarithmic absorption,
the three one-third component estimates, complete scalar-majorant absorption,
the resulting complex truncation decay, and its inclusion in the full HT
Mangoldt-error allowance.

Release 4.32 audits the generic normalized horizontal and vertical
length-times-sup inequalities, the exact HT edge lengths, and the assembly of
all three displaced edges into the named scalar sup majorant.

Release 4.33 audits the exact reciprocal-distance integral, the weighted
vertical contour estimate with logarithmic height cost, the exact shifted
integrand norm factorization, and the source-scale weighted three-edge
assembly.

Release 4.34 audits the eventual twice-width comparison, quantitative VK
separation of every local sharp-Landau zero, the reciprocal-distance zero
sum, large-zero exclusion, arbitrary-height Landau partial-fraction bound,
and its transport to the physical positive-height zeta logarithmic
derivative.

Release 4.35 audits exact conjugation to negative height, the sign-uniform
absolute-ordinate parameterization, and simplification of the raw Landau
bound to explicit reciprocal-width times logarithmic growth.

Release 4.36 audits compactness of the half-VK low-height rectangle,
surrogate nonvanishing, its uniform logarithmic-derivative bound, restoration
of the explicit zeta pole term, and the resulting `C+1/eta` left-line bound.

Release 4.37 audits the nine-frequency VK comparison, exact horizontal
physical-coordinate ranges, their two pointwise logarithmic-derivative
bounds, and the complete vertical compact/Landau max assembly.

Release 4.38 audits the two shifted-integrand transfer bounds, the
surrogate-to-zeta nonvanishing bridge on every edge, the horizontal `1/T`
gain, the denominator-retaining vertical numerator, and the complete
VK-specialized weighted contour-edge assembly.

Release 4.39 audits the corrected doubled contour shift, its strengthened VK
comparison, cubic high/left logarithmic-derivative envelopes, quadratic
vertical logarithm, the two scalar stretched-exponential absorptions, and the
uniform large-beta three-edge target theorem.

Release 4.42 audits the variable VK disk geometry, normalized zero-freeness,
Euler-product center lower bound, Pintz disk maximum, empty-zero-set disk
logarithmic derivative, native-width `O(D(A)*loglog(A))` specialization, HT
scale absorption, and the final compact/high-height `K/beta` origin-residue
assembly.
