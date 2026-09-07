# Gafni-Tao Shitlist

Status: release theorem chain complete; isolated verification is authoritative.

This is the completion ledger for the Gafni-Tao program. A checked item means
that its stated release-scope conclusion is present in the isolated root and
on the central audit surface. It does not mean that every theorem in every
cited paper has been formalized.

The command of record is:

```powershell
cmd /c run_gafni_tao_build.bat --no-pause
```

The exact pins and local PNT+ derivation are in `Reproduction Manifest.md`.

## Definitions and Section 2

- [x] **GT-00 - Isolation and source freeze.** The package lives entirely
  under `PostGM/GafniTao`; the frozen foundation is the archived source of tag
  `gm-foundation-freeze-v1.0.1`, commit
  `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`. No frozen source was edited.

- [x] **GT-01 - Exact source crosswalk.** `Gafni-Tao Crosswalk.md` maps the
  definitions, equations, lemmas, theorem wrappers, source inputs, intervals,
  multiplicities, and endpoint conventions used by the release.

- [x] **GT-02 - Asymptotic and exponent language.** The release has the fixed-
  power eventual predicate used for `mu_delta`, epsilon-power predicates used
  for `A` and `A*`, `EReal` infimum/supremum definitions, empty-supremum
  behavior, countable positive-threshold diagonalization, and the limit
  interfaces consumed by the source theorem.

- [x] **GT-03 - Exact exceptional set.** `shortIntervalExceptionalSet delta theta X` is the
  Lebesgue-measurable subset of `[X,2X]` defined by the literal Mangoldt
  discrepancy on `(x,x+x^theta]`. `exceptionalExponentDelta` and
  `exceptionalExponent` implement `mu_delta` and `mu`; no sampled proxy is used.

- [x] **GT-04 - Multiplicity-weighted zero model.** Frozen zero rectangles are
  bridged to finite zero occurrences weighted by analytic vanishing order,
  with the strip and endpoint conventions used downstream.

- [x] **GT-05 - Exact `N*` and `A*`.** The ordered tolerance-one four-zero
  count uses product analytic multiplicity. The occurrence-count equality,
  epsilon envelope, and least exponent are release-integrated.

- [x] **GT-06 - Chebyshev interval bridge.** The real-endpoint sum of
  `Lambda(n)` on `(x,y]` is proved equal to `psi(y)-psi(x)`, including
  nonintegral endpoints and prime powers.

- [x] **GT-07 - Local cover and Brun-Titchmarsh replacement.** The finite
  multiplicative cover, `tau=X^(1-theta)`, replacement of `x^theta` by
  `x/tau`, endpoint errors, and global exceptional-set union are proved.

- [x] **GT-08 - Sharp truncated explicit formula.** The native formula tracks
  the minus sign, analytic multiplicity, pole, trivial-zero contribution,
  Perron endpoint, selected height, horizontal/vertical edges, prime-power
  convention, and the required `O(x log^2(x)/T)` scale. Public endpoints are
  `sharpPsiTruncationBound_native` and
  `sharpTruncatedExplicitFormulaBound_native`.

- [x] **GT-09 - Vinogradov-Korobov zero-free region.** The Ford detector chain
  proves `ford_asymptotic_zero_free_native : FordAsymptoticZeroFree`; the
  rectangle-to-count-vanishing consumer is included. This is the qualitative
  VK width required by equation (2.6), not a claim of Ford's optimized numeric
  constants.

- [x] **GT-10 - Near-one logarithmic zero density.** The Pintz chain proves
  `exists_pintz_nearOne_log_density_native`, with a genuine
  `T^(C*eta^(3/2))*log(T)^B` bound. The release uses an explicit sufficient
  logarithmic power; it does not claim Ford's older optimized coefficient.

- [x] **GT-11 - Lemma 2.1.** The native near-one density and VK vanishing are
  assembled into the physical right-edge stretched-exponential estimate.

- [x] **GT-12 - Lemma 2.2.** The physical `L-infinity` strip estimate uses the
  actual multiplicity-weighted zero count and the `X,T,tau` relations.

- [x] **GT-13 - Fourier bump and `c_rho`.** The nonnegative compactly
  supported bump, complex Fourier transform, uniform decay, and exact zero
  coefficient are proved with the release Fourier convention.

- [x] **GT-14 - Lemma 2.3.** The normalized second-moment estimate consumes
  the actual density exponent and the unit local-zero count.

- [x] **GT-15 - Four-zero energy bridge.** Pair counts, double counting, the
  Schur bound, decay tails, and the exact bridge to multiplicity-weighted `N*`
  are proved.

- [x] **GT-16 - Lemma 2.4.** The normalized fourth-moment estimate consumes
  the actual `A*` exponent.

- [x] **GT-17 - Equation (2.7).** The half-open `J` strips and the right-edge,
  small-`A`, `L2`, and `L4` alternatives are assembled, including the upper
  boundary and strip-measure sum.

- [x] **GT-18 - Limit assembly.** The epsilon, `J`, logarithmic, cover, and
  `2/J`, `4/J` losses are assembled in source order. The mandatory
  `inf_{epsilon>0}` is retained; no continuity of `A` is assumed.

## Public Gafni-Tao theorems

- [x] **GT-19 - Theorem 1.3.** The public theorem
  `gafniTaoTheorem13_native` proves
  `exceptionalExponent theta <= refinedExceptionalUpperExponent theta`, where
  the latter unfolds to the source infimum/supremum of the minimum of the
  ordinary and four-zero expressions. `gafniTaoTheorem13_max_native` gives the
  alternate strict-upper-half maximum form.

- [x] **GT-20 - Theorems 1.2 and 1.1.** `gafniTaoTheorem12_native` and its max
  form give the ordinary second-moment corollary.
  `gafniTaoTheorem11_guthMaynard_native` gives both the all-interval and the
  almost-all-interval statements, the latter with one measurable
  natural-density-zero exceptional set.

- [x] **GT-21 - Native frozen-GM consumer.** The zero-density envelope invokes
  the actual frozen `guthMaynardZeroDensity_published_native` chain. The public
  Theorem 1.1 specialization uses `A0=30/13` and proves the strict thresholds
  `theta>17/30` and `theta>2/15`; it is not a restatement of a supplied
  certificate.

## Published Section 3 samples

- [x] **GT-22 - Required published exponent inputs.** The Pintz source chain
  proves `pintzTwentyThreeTwentyFourCutoff_native`. The two native
  Heath-Brown energy cells needed in a neighborhood of `sigma=7/10` are proved
  and consumed. The stronger third high-range cell is not needed for either
  displayed sample and is not claimed by this release.

- [x] **GT-23 - Exact native sample bounds.** The release proves and audits:

  ```lean
  exceptionalExponent_seventeen_thirtieths_le_native :
    exceptionalExponent (17 / 30) <= ((7 / 12 : Real) : EReal)

  exceptionalExponent_two_fifteenths_add_le_native
      (hDelta : 0 < Delta) (hDeltaUpper : Delta <= 1 / 100) :
    exceptionalExponent (2 / 15 + Delta) <=
      ((1 - 9 * Delta / 13 : Real) : EReal)
  ```

  Both compose the native Theorem 1.3 with the actual formalized source input.

- [x] **GT-24 - Section 3 certification scope.** The release makes no claim to
  reproduce the paper's complete best-known numerical curve. Consequently the
  conditional full-curve clause is closed by explicit non-claim: no floating-
  point plot is used as proof, and the optional high Heath-Brown cell and exact
  all-piece optimizer remain outside the release theorem surface.

## Integrity and reproduction

- [x] **GT-25 - Integrity and coverage.** Every release production theorem is
  reachable from `Extension/GafniTao.lean`; the central audit contains every
  public and source-sensitive endpoint. Redundant per-module `#print axioms`
  commands were consolidated into that audit so a normal build does not replay
  thousands of informational diagnostics. The principal runner rejects every
  warning or linter diagnostic and every forbidden-token match.

- [x] **GT-26 - Documentation and reproduction.** The Architecture, Research
  Agenda, Crosswalk, Shitlist, Sources, README, source hashes, reproduction
  manifest, central audit, and runner describe the same release boundary.
  `push_to_github.bat` remains owner-operated and is not part of any build.

## Explicit exclusions, not hidden failures

The following are useful continuation projects, but none is an input to the
public conclusions listed above:

- Ford's optimized constants `9.463`, `133.66`, `76.2`, `4.45`, and `58.05`;
- the complete third/high Heath-Brown energy cell;
- the paper's entire best-known piecewise numerical curve; and
- publication, peer review, external semantic review, or canonical status.

The pinned upstream PNT+ module containing the clean Chebyshev PNT also contains
two unrelated admitted declarations. The isolated package uses the exact
83-file required closure and removes the unreachable four-declaration block
containing them. Eighty-two retained files are byte-identical; the runner
checks both hashes for the sole edited file, builds the local dependency, and
fails on any warning. This does not claim that upstream PNT+ is warning-free.
