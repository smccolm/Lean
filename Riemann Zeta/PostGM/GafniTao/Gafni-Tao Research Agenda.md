# Gafni-Tao research agenda

Status: research and execution plan, not a proof claim.

Suggested commit message: `PostGM Gafni-Tao: prove exact second and fourth zero-strip moment bounds`

Update that line after every substantive proof milestone. Do not hard-code it
inside `push_to_github.bat`.

## 1. Objective

Formalize the complete proof mechanism of Gafni-Tao Theorems 1.2 and 1.3 and
the zero-density short-interval consequences in Theorem 1.1, then instantiate
the mechanism with the frozen Guth-Maynard zero-density theorem and the exact
published zero-additive-energy inputs needed for the paper's two displayed
unconditional sample bounds.

The first new public result should be the exact refined exceptional-set
transfer, not an informal statement that GM “improves primes in short
intervals.” The project quantifies the Lebesgue measure of the exceptional set;
it does not prove the Riemann Hypothesis or a new zero-free region beyond its
formalized published inputs.

## 2. Exact mathematical contract

For `0 < theta < 1`, `X > 1`, and `delta > 0`, model

```text
E_delta(X,theta) = {
  x in [X,2X] :
  |sum_{x<n<=x+x^theta} Lambda(n) - x^theta| >= delta*x^theta
}.
```

Use Lebesgue measure, not a cardinality of sampled endpoints. Define
`mu_delta(theta)` as the infimum of exponents `xi` for which the fixed-power
bound `|E_delta(X,theta)| <<_{delta,theta} X^xi` holds for all sufficiently
large `X`, and define `mu(theta)` as the supremum over positive `delta`. Do not
insert an epsilon loss into the definition of `mu_delta`. The later global
exceptional-set formulation has a `mu(theta)+o(1)` exponent only after the
paper's countable diagonalization in `delta`. The source permits `-infinity`
when the exceptional set is eventually empty, so the canonical definition
should use `EReal` (or an equivalent extended-order construction) together
with proved real-valued interfaces for ordinary fixed-power estimates.

Let `N(sigma,T)` be the frozen, analytic-multiplicity count for zeros with
`Re rho >= sigma` and `|Im rho| <= T`. Define `A(sigma)` as the least density
exponent in the source sense. Define

```text
N*(sigma,T) = # {
  (rho1,rho2,rho3,rho4) in Z(sigma,T)^4 :
  |gamma1+gamma2-gamma3-gamma4| <= 1
}
```

with the product of analytic multiplicities, and define `A*(sigma)` from this
actual count. Do not replace it with the additive energy of a set of distinct
ordinates or a separately supplied finite set.

The main theorem must be equivalent to

```text
mu(theta) <= inf_{epsilon>0}
  sup_{0<=sigma<1, A(sigma)>=1/(1-theta)-epsilon}
    min (
      (1-theta)(1-sigma)A(sigma) + 2*sigma - 1,
      (1-theta)(1-sigma)A*(sigma) + 4*sigma - 3
    ).
```

The epsilon-infimum is mandatory. The paper explains that deleting it would
silently assume continuity of `A`, which is not known.

## 3. Proof conversion, in source order

### 3.1 Definitions and source entry

1. Pin the exact paper PDF/source and every imported repository revision.
2. Cross-walk each displayed equation and theorem to a Lean declaration.
3. Prove the bridge between the paper's zero multiset and the frozen finite
   zero set weighted by `analyticVanishingOrder`.
4. Prove measurability and finiteness of every exceptional set and zero sum.
5. Establish direct envelope predicates first, then prove they are equivalent
   to the canonical `EReal` infimum/supremum definitions. Use fixed-power
   eventual big-O for `mu_delta`, but epsilon-power bounds for `A` and `A*`,
   exactly as in the paper. This keeps routine estimates usable without
   weakening the source theorem.

### 3.2 From primes to the finite zero sum

6. Prove
   `sum_{x<n<=x+y} Lambda(n) = psi(x+y)-psi(x)` with real endpoints, floors,
   and the paper's half-open convention.
7. Formalize the local cover of `[X,2X]` by `O_delta(1)` intervals
   `[X0,(1+delta/J)X0]` and the Brun-Titchmarsh replacement of `x^theta` by
   `x/tau`, where `tau = X0^(1-theta)`.
8. Prove the sharp truncated explicit formula at
   `T = J*(log X)^2*tau`. Preserve the pole, trivial zeros, prime powers,
   horizontal endpoints, multiplicity, possible sign convention, and the
   uniform `O(x log^2 x/T)` remainder. The source uses an absolute value later,
   but that does not authorize an unexplained sign change.
9. Define the exact finite sum `S_I(x)` from equation (2.4) and prove the
   exceptional-set reduction (2.3).

### 3.3 The four analytic estimates

10. Formalize a Vinogradov-Korobov zero-free region strong enough for (2.6).
11. Formalize the near-one logarithmic density estimate
    `N(1-eta,T) <= T^(C eta^(3/2))*log(T)^B`. Do not absorb the logarithm into
    `T^epsilon`; Gafni-Tao explicitly state that such a loss is unusable here.
12. Assemble the Stieltjes/partial-summation calculation to prove Lemma 2.1's
    exponential right-edge decay.
13. Prove Lemma 2.2 by monotonicity of `N`, the exact scale relation
    `T = X^(1-theta+o(1))`, and all `sigma_-`, `sigma_+` losses.
14. Construct a nonnegative smooth bump bounded below on `[0,log 2]`; prove
    the complexified Fourier transform identity, tenfold decay uniformly in
    the bounded imaginary shift, and
    `|((1+1/tau)^rho-1)/rho| <= C/tau`, including `rho=0` exclusion.
15. Expand the smoothed square, justify finite sums/integrals, use the unit
    local-zero bound with multiplicity, and prove Lemma 2.3 exactly.
16. Define the pair-count function `F`, prove the double-counting identity,
    Schur bound, and comparison with tolerance-one `N*`; then prove Lemma 2.4.

### 3.4 Global assembly

17. Partition `[0,1)` into the exact half-open strips
    `[j/J,(j+1)/J)`. Prove that zeros on the right endpoint do not disappear
    and that there are no zeros on `Re s = 1` in the required range.
18. Prove the three cases in equation (2.7): right edge, small `A` giving an
    eventually empty event, and the `L2`/`L4` Markov alternatives.
19. Maintain an explicit exponent ledger for `delta`, `J`, `epsilon`, the
    local cover, `tau`, `T`, logarithms, and the `2/J` and `4/J` losses.
20. Take limits in the source order. Prove the `J -> infinity` and
    `epsilon -> 0` order-theoretic steps without continuity assumptions.
21. Export Theorem 1.3 and derive Theorem 1.2 as the exact second-moment
    corollary. Export the alternate `max(1-theta, ...)` form as a separate
    proved theorem.
22. Derive Theorem 1.1: all intervals for `theta > 1-1/A0` and almost all for
    `theta > 1-2/A0`, with the source's density-zero meaning proved from
    `mu(theta) < 1`.

### 3.5 Native published consumers

23. Import the frozen theorem
    `guthMaynardZeroDensity_published_native` and prove the `A0=30/13`
    envelope bridge. Do not merely project the theorem beside the target.
24. Formalize the exact ordinary Pintz segment needed for the source's
    `sigma<=23/24` cutoff and the Heath-Brown `A*` segments needed at and
    around `sigma=7/10`; prove their endpoint compatibility, exponent
    normalization, and multiplicity convention.
25. Prove, with rational arithmetic and limiting margins,
    `mu(17/30) <= 7/12`.
26. Prove the quantified statement “for sufficiently small `Delta>0`” and
    `mu(2/15+Delta) <= 1-9*Delta/13`, including the `sigma <= 23/24` cutoff
    from the actual Pintz input and all epsilon margins.
27. If the full Figure 4 envelope is claimed, pin ANTEDB and TT-Y, translate
    every relevant piecewise formula, and certify the finite optimizer in Lean
    using exact rational/algebraic interval endpoints. A floating-point plot
    may accompany the result but cannot establish it.

## 4. Risk register

### Highest risk: right-edge input

The pinned PNT+ dependency does not currently expose the required
Vinogradov-Korobov theorem or the logarithmic near-one density estimate. Its
`MediumPNT` is weaker in a different direction, and its `StrongPNT` source
contains a blueprint statement rather than the needed proved declaration.
Begin GT-09 and GT-10 immediately after the basic source-entry definitions.

### High risk: sharp explicit formula

Existing contour and Mellin machinery is substantial, but the exact sharp
truncation used here has real endpoints and a uniform height depending on
`X,theta,J`. A smoothed or sign-changed formula is only useful after Lean proves
the complete transfer and error.

### High risk: multiplicity in `N*`

`zerosInRect` is a finset of distinct complex zeros. The source counts a
multiset. All pair and quadruple sums must carry analytic vanishing orders.
Dropping those weights invalidates the connection to both `N` and `A*`.

### Medium risk: extended-real exponents

The empty supremum is `-infinity`; `mu` may also be `-infinity`. Build an
epsilon-bound interface and prove an order-isomorphism to the source's extended
exponents before attempting the final infimum/supremum theorem.

### Medium risk: numerical source tables

ANTEDB is moving executable data. Pin it and treat it as a source generator,
not a proof oracle. Separate the exact two sample corollaries from the optional
full plotted envelope so documentation cannot overclaim.

## 5. Verification and documentation

The isolated package needs its own warning-failing runner. Completion requires:

- default build plus every production module;
- no Lean warnings or linter diagnostics;
- repository-wide scans below `PostGM/GafniTao` for `sorry`, `admit`,
  project axioms, `unsafe`, `native_decide`, and equivalent bypasses;
- explicit axiom audits of every public theorem and every source-critical
  bridge;
- a theorem-dependency crosswalk demonstrating actual consumption of frozen
  GM and formalized `A*` inputs;
- reproduction logs with exact toolchains, commits, commands, exit codes, and
  hashes;
- synchronized architecture, Shitlist, agenda, README, and source ledger only
  after proof status changes.

The simple `push_to_github.bat` is not a verifier. It must never be inserted
into an automated build and must not be run by an agent without explicit
permission.

## 6. Kernel-checked progress

GT-13 through GT-16 are complete in the isolated package. The public endpoints
are `zeroStripPhysicalSecondMoment_epsilonBound` and
`zeroStripPhysicalFourthMoment_epsilonBound`. Their proof chains expand the
actual finite multiplicity-weighted zero sums, use uniform complexified
Fourier decay, and terminate respectively in `ZeroDensityEnvelope` and the
actual product-multiplicity `ZeroAdditiveEnergyEnvelope`. The finite quartic
bridge `zeroPairPairDecaySum_le_zeroAdditiveEnergyCount` proves the complete
decaying-kernel comparison with the tolerance-one count; it does not introduce
an abstract energy parameter. The isolated root build and explicit axiom audit
accept these declarations with only `propext`, `Classical.choice`, and
`Quot.sound`.

GT-17 remains open because equation (2.7) also consumes the still-open sharp
explicit-formula and right-edge branches GT-08 through GT-12. Half-open strip
partition, threshold-union, and Markov components are the next independent
assembly obligations.
