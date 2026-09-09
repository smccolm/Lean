# Tao 2026 build tools

`Probes/` is reserved for non-production API experiments. Such files are
excluded from the production import graph; any result used by the formalization
must be promoted to `Extension/Tao2026/` and audited there.

`run_tao_build.ps1` verifies the pinned Tao source artifacts, all 1,226 frozen
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
It also covers the complete Lemma 2.10 and Corollary 2.11 chains: the concrete
quadratic maximal-order construction, sharp ideal-divisor count, rank-one
unit and height estimates, signed square-solution theorem, exact dyadic
powerful-number fibers, interpolation, and the uniform signed `≪ x` endpoint.
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
closure of `GafniTao.Theorem11` from node 74, including `public import`
declarations, and regenerates the per-source SHA-256 manifest. Run it only as
an intentional dependency-update operation and review all resulting changes.
