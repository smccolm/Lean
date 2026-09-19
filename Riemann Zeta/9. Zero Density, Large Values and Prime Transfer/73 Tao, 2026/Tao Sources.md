# Tao 2026 Sources

## Release 5.10 source note

No new source artifact is required by the owner-approved completion
amendment. The pinned BHP paper and Tao's literal Rosser-weight formulation
remain provenance for stronger source-faithful alternatives. Release
acceptance instead uses the internally proved native-PNT Section 4 scale and
Selberg upper-sieve consumer properties; it does not cite the stronger
statements as if they had been formalized.

## Historical release 5.09 source note

No new source artifact or dependency is introduced. The final Section 4
route combines `classicalChebyshevPsiDeLaValleePoussin_native` with the pinned
Mathlib theorem `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`, then proves
prime-free shortness `4 H (log N)^2 ≤ N` internally. The crosswalk identifies
the exact replacement for the original BHP consumer.

All four frozen public endpoints are now proved and passed the release
verifier. BHP's `0.525` theorem remains unformalized: its pinned paper is
provenance for the stronger original alternative, not proof evidence or a
premise of the final route. The broader Kummer interfaces likewise remain
optional conditional alternatives to the proved simple-root route.
All twelve pinned source artifacts and all frozen dependency hashes passed.

## Historical release 5.08 source note

The author-hosted Cochrane--Pinner paper, *Using Stepanov's method for
exponential sums involving rational functions*, is pinned as
`Sources/cochrane-pinner-stepanov-author.pdf`. Its Section 3 is a roadmap
for the polynomial method. The formal proof supplies its own simple-root
nonvanishing, Hasse constraints, dimension count, integer parameter choice,
norm-fiber count, and character cancellation; no paper theorem is admitted.
The artifact, date distinction, DOI, exact locators, and SHA-256 are recorded
in `Sources/PINS.md` and `Sources/SHA256SUMS.txt`.

Together with the existing Newton recurrence, this proves the simple-root
Weil theorem actually required by Burgess and closes Theorem 1.7. It does
not assert the broader arbitrary-multiplicity Kummer theorem or BHP.

## Historical release 5.07 source note

No new external source or dependency is introduced. The polynomiality and
recurrence proofs use the pinned Mathlib interpolation, character
orthogonality, minimal-polynomial conjugacy, polynomial factorization, and
formal power series APIs. Exact claims and consumers are recorded in the
release-5.07 crosswalk. This does not claim a proof of the remaining Weil
bounds or BHP theorem.

`Sources/` is the provenance authority for node 73. It currently contains the
exact v2 PDF and TeX source archive for the target paper, the Baker--Harman--
Pintz paper used in Proposition 2.3(ii), the Erdős--Selfridge paper used in
Theorem 1.10, and Granville's smooth-number survey used in Proposition 2.1,
the primary Canfield--Erdős--Pomerance proof behind its critical lower bound,
plus pin and hash records.

## Primary paper

Terence Tao, *Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`, revised 22 April 2026.

- `Sources/tao-unusual-anatomy-2603.27990v2.pdf`
- `Sources/tao-unusual-anatomy-2603.27990v2.tar`

See `Sources/PINS.md` for origin URLs and `Sources/SHA256SUMS.txt` for exact
artifact identities.

## Baker--Harman--Pintz input

R. C. Baker, G. Harman, and J. Pintz, *The Difference Between Consecutive
Primes, II*, *Proceedings of the London Mathematical Society* 83 (2001),
532--562, DOI `10.1112/plms/83.3.532`.

- `Sources/baker-harman-pintz-2001.pdf`
- Required result: Theorem 1, journal page 532 (PDF page 1).
- Proof endpoint: journal page 561 (PDF page 30), where the positive
  `9/100` lower bound is obtained for intervals of length `x^0.525`.
- Analytic dependency warning: Section 2 and Lemma 2 use Watt's fourth-moment
  estimate for a zeta factor and a Dirichlet polynomial. The remainder uses
  Harman's sieve, one- and two-dimensional sieve asymptotics, role reversals,
  and numerical loss estimates. No local Lean theorem currently discharges
  this dependency.

## Erdős--Selfridge input

P. Erdős and J. L. Selfridge, *The Product of Consecutive Integers Is Never a
Power*, *Illinois Journal of Mathematics* 19 (1975), 292--301.

- `Sources/erdos-selfridge-1975.pdf`
- Required result: Theorem 1, specialized to squares.
- Stronger formalized boundary: Theorem 2's prime-multiplicity statement;
  `ErdosSelfridgePrimeMultiplicityConclusion` records its least-prime endpoint
  and valuation-divisibility conclusion exactly (journal/PDF page 292).
- Tao-facing use: equality of two factorial squarefree components would make
  a product of at least two consecutive positive integers a square; excluding
  that case leaves at most two consecutive factorial indices in each fiber.
- Formalization warning: the online `formal-conjectures` declaration is
  explicitly unfinished (`sorry`) and cannot be imported or copied as proof.

## Hanson primorial input

Denis Hanson, *On the Product of the Primes*, *Canadian Mathematical
Bulletin* 15(1) (1972), 33--37, DOI `10.4153/CMB-1972-007-7`.

- Primary source URL: `https://doi.org/10.4153/CMB-1972-007-7`.
- Source role: the Sylvester-sequence factorial coefficient and multinomial
  estimate behind the elementary bound on the product of primes.
- Representation note: the Lean proof uses the first four denominators
  `2,3,7,43` with exact integer weights and a strong-induction remainder,
  rather than importing Hanson's decimal estimate or numerical table.

## Granville smooth-number input

Andrew Granville, *Smooth numbers: computational number theory and beyond*,
MSRI Publications 44 (2008), 267--323.

- `Sources/granville-smooth-numbers-2008.pdf`
- Tao's cited formulas: (1.14), (1.15), and (3.24).
- Lower-bound proof locator: equation (3.3), journal page 282 (PDF page 16).
- Polylogarithmic assembly locator: journal page 291 (PDF page 25).
- Formalization warning: the source is a survey proof, not an imported Lean
  theorem; the finite lattice count and all asymptotic transfers must be
  formalized recursively.

## Canfield--Erdős--Pomerance critical lower input

E. Rodney Canfield, Paul Erdős, and Carl Pomerance, *On a problem of
Oppenheim concerning “Factorisatio Numerorum”*, Journal of Number Theory 17
(1983), 1--28.

- `Sources/canfield-erdos-pomerance-1983.pdf`
- Primary theorem locator: Theorem 3.1, journal/PDF pages 10--15.
- Finite proof locators: multiscale product decomposition (3.5), recursive
  insertion (3.10), reciprocal-prime multinomial estimate (3.11), and the
  assembled bootstrap inequality (3.15).
- Formalization status: this primary source fixes the proof architecture and
  constants but is not imported as a theorem. The exact source-band packet is
  formalized, and the sharp critical lower estimate is now proved by a coarse
  fixed-dyadic CEP variant using only the frozen qualitative PNT. The
  shrinking-band source route remains documented but is not required by the
  compiled Proposition 2.1 conclusion.

## Source policy

- Pin an explicit version; never silently replace these files with a later
  arXiv revision.
- Add a later version beside the existing one and update the crosswalk only
  after reviewing the delta.
- Keep source extraction intentional and documented. Do not commit a temporary
  Python environment or disposable PDF extraction cache.
- Third-party papers and archives retain their original rights and are not
  relicensed by the repository's MIT-0 license.
- Do not add candidate background sources until the paper crosswalk identifies
  why they are needed.

## Historical source-survey limits

The source archive has been validated as readable but not extracted into the
repository. An initial theorem-number and dependency survey is recorded in
`Tao Goal Prompt.md` and `Tao Architecture.md`; it is not yet the authoritative
row-by-row source crosswalk. The Baker--Harman--Pintz, Erdős--Selfridge,
Granville, and Canfield--Erdős--Pomerance artifacts are pinned, but pinning
papers is not a Lean proof of any
missing dependency.

## Release 2.92 source note

`BurgessWeilPrimeFourteenRoots.lean` adds no external source dependency. It is
the final finite algebraic/projective reduction for the literal fourteenth
moment: exact fourteen active roots reduce to a normalized thirteen-point
power-character trace. The corresponding reduced trace estimate remains an
explicit analytic hypothesis rather than a claimed consequence of the pinned
source archive.

## Release 2.93 source note

`ErdosSelfridgeSource.lean` uses the already pinned 1975 paper and introduces
no new external dependency. It transcribes Theorem 2 in source-facing form
and proves its implication to the exact square input. The online
`formal-conjectures` statement remains unusable because its proof is `sorry`.
The pinned `scottdhughes/erdos137` commit was re-inspected declaration by
declaration in `Base`, `Finiteness`, `TaoPoint`, `RoughPartStructure`, and
`SquarefreeCapacity`: it proves useful elementary facts but not the
perfect-power theorem, and those relevant interval/extraction facts are
already subsumed locally. No code or dependency was imported from it.

## Release 2.94 source note

`ErdosSelfridgePowerFree.lean` follows journal page 293 of the already pinned
1975 paper. It formalizes equation (3), including the canonical
`l`-power-free coefficient and its restriction to primes below the block
length under failure of Theorem 2. No external declaration is imported.

## Release 2.95 source note

`ErdosSelfridgeProductSeparation.lean` follows journal pages 293--294 of the
already pinned 1975 paper. It formalizes source equations (2) and (4) and the
full statement of Lemma 1, including the stronger assertion that the quotient
of two distinct equal-cardinality coefficient products is not an `l`-th
power in the positive rationals. No new external declaration is imported;
the package theorem uses the existing, explicitly named Sylvester--Schur
contract. The next source obligation is Lemma 2's deletion and
factorial-divisibility argument.

## Release 2.96 source note

`ErdosSelfridgeDeletion.lean` follows journal pages 294--295 and the beginning
of Section 3 on page 299 of the pinned paper. It formalizes Lemma 2 with the
exact deletion count and equation (9), then specializes the valuation ledger
to the squarefree case to obtain equation (21). No external result beyond the
already imported elementary factorial and prime-counting APIs is used. The
next source boundary is the quantitative square-case comparison in equations
(22)--(23) and the finite residual analysis.

## Release 2.97 source note

`ErdosSelfridgeSquareDensity.lean` formalizes the first two sentences of
Section 3.1 on journal page 299 of the pinned Erdős--Selfridge paper. The
source observes that twelve of every 36 consecutive integers are divisible
by `4` or `9`, hence at most 24 are squarefree. Lean proves the exact translated
interval count via inclusion--exclusion and exports the matching offset form.
Equation (22)'s subsequent product lower bound is not yet claimed.

## Release 2.98 source note

`ErdosSelfridgeSquareDensity.lean` now completes equation (22) on journal page
299. The source threshold `H≥64` is preserved, and `(3/2)^H` is represented
exactly by the natural-number inequality `3^H*H! < 2^H*∏aᵢ`. The proof also
exports the canonical-counterexample specialization using the already proved
source Lemma 1. Equation (23) is the next unformalized line.

## Release 2.99 source note

`ErdosSelfridgeSquareValuations.lean` follows the transition from equations
(21) and (22) to equation (23) on journal pages 299--300 of the pinned 1975
paper. It formalizes the exact 2- and 3-adic cancellation and the resulting
strict counterexample inequality before the paper substitutes its four
logarithmic valuation estimates. No new external dependency is introduced;
the displayed equation (23) and the Rosser--Schoenfeld primorial estimate are
not yet claimed.

## Release 3.00 source note

The same pinned Erdős--Selfridge paper, journal pages 299--300, supplies the
four estimates now formalized in `ErdosSelfridgeSquareValuations.lean`:
the factorial valuations are bounded using base-two and base-three digit
sums, and the coefficient-product valuations are bounded by recursively
counting odd local valuations in `(N,N+H]`.

Lean then derives the exact real-exponent logarithmic inequality immediately
before displayed equation (23). No new external dependency is introduced.
The final elementary simplification to `14/3` and the later
Rosser--Schoenfeld primorial input are not yet claimed.

## Release 3.01 source note

The elementary simplification on journal page 300 is now formalized exactly.
The logarithmic factors are evaluated with real-power identities, and the
remaining root factor is bounded with sufficient slack to recover the printed
constant `14/3`. Thus displayed equation (23) is now claimed and audited.
The subsequent explicit primorial estimate remains the next external
source-facing step.

## Release 3.02 source note

The line after equation (23) on journal page 300 is now reproduced in an
asymptotic form. `ErdosSelfridgePrimorial.lean` uses the already pinned prime
number theorem to prove `prod_{p<H} p <= 3^H` eventually and derives the
resulting contradiction for every sufficiently large `H`.

The original paper gives explicit elementary/numerical cutoffs before its
finite case analysis. Those constants have not been imported here, so release
3.02 claims only an extracted threshold and leaves the explicit cutoff and
Section 3.2 finite verification open.

## Release 3.03 source note

The opening cases of Section 3.2 on journal page 300 are now formalized.
Length three is impossible by coefficient distinctness and the two divisors
of `2`. At length four, the coefficients are exactly `1,2,3,6`; their product
is a square, and the source difference-of-squares identity gives the
contradiction. The same finite-candidate argument also closes length five.

No external theorem is used for these cases. The next source line is the
small-prime count beginning at length six.

## Release 3.04 source note

The exceptional `H=6` clause on journal page 300 is now formalized exactly.
Outside `5 | N+1`, five coefficients have no prime factor above three and
cannot be distinct. Inside that residue class, the middle four coefficients
have square product, reducing to the already proved four-consecutive
contradiction. The finite source analysis now begins at length seven.

## Release 3.05 source note

The `H=7` instance of the small-prime count on journal page 300 is now
formalized exactly. Every residue class modulo five leaves at least five of
the seven positions indivisible by five. Their coefficients have no prime
factor above three and therefore cannot all be distinct. No new external
theorem is used. The finite source analysis now begins at length eight and
its stated exceptional congruence class.

## Release 3.06 source note

The exceptional `H=8` clause on journal page 300 is now formalized exactly.
The ordinary count is a complete kernel-checked enumeration modulo `35`.
Its only four-position class is precisely `7 | N+1` and `5 | N+2`; the four
middle coefficients then have square product and reduce to the proved
four-consecutive contradiction. No new external theorem is used. The finite
source analysis now begins at length nine.

## Release 3.07 source note

The uniform five-coefficient count following the `H=8` exception on journal
page 300 is now formalized through `H=13`. Exact periodic checks modulo `35`
and `385` supply the count for the two prime-stable blocks `9..11` and
`12..13`. The coefficient-support contradiction uses no new external theorem.
The finite source analysis now begins at length fourteen.

## Release 3.08 source note

The journal-page-300 five-coefficient count is now formalized through
`H=17`. Rather than enumerate modulo `5005`, the proof bounds the union of
the four relevant prime-multiple sets, using exact block counts at the two
tight endpoints. No new external theorem is used. The finite source analysis
now begins at length eighteen.

## Release 3.09 source note

The journal-page-300 five-coefficient argument is now formalized through
`H=20`. Sharp ceiling sums handle the primes through `17` and `19`; the
generic coprimality transfer recovers the source conclusion that all surviving
coefficients use only `2` and `3`. No external theorem is added.

## Release 3.10 source note

The journal-page-300 finite analysis is now complete through `k<71`. The
source's nine-coefficient tier for `20<k<56` is formalized by the sharp union
count, whose checked inequalities remain sufficient through `k=70`. Nine
coefficients supported on `2,3,5` cannot be distinct. The next source line is
the explicit `k>=71` consequence of equation (23).

## Release 3.11 source note

Journal page 300 splits the large square case at `k=297`: the elementary
prime-product bound by `3^k` handles the tail, while the sharper tabulated
bound handles `71<=k<297`. The formalization now proves the exact equation-(23)
growth cutoff and checks each actual prime product in that finite interval.
It isolates the remaining source dependency as
`ErdosSelfridgeThreePrimorialConclusion`, with no imported numerical table.

## Release 3.12 source note

Hanson's 1972 paper supplies the elementary factorial-coefficient mechanism
now formalized in `ErdosSelfridgeHanson.lean`: the Sylvester reciprocal sum
leaves a positive valuation margin, so every prime below the index divides the
coefficient.  The quantitative Lean proof specializes the same multinomial
idea to `2,3,7,43`, clears denominator `1806`, and proves all entropy and
floor-loss comparisons as exact natural-number inequalities.

No decimal approximation or external prime table is imported.  Finite block
certificates below `1400` and strong induction above it prove the named
`ErdosSelfridgeThreePrimorialConclusion` internally.

## Release 3.13 source note

The pinned public Sylvester--Schur proof identifies the standard factorial
large-start decomposition, but its unlicensed Lean source is not copied or
imported.  `SylvesterSchurFactorialThreshold.lean` independently derives the
criterion from local Mathlib ascending-factorial identities and the already
proved binomial small-prime envelope.

The local result is slightly sharper at this stage: it retains the exact
prime-count exponent and obtains `H! 2^pi(H)+1`; the classical
`H! 2^(H-1)+1` threshold is then a corollary.  This is a reduction of the
remaining finite range, not a claim that the unrestricted theorem is complete.

## Release 3.14 source note

No new external input is used.  `SylvesterSchurHundred.lean` extends the local
finite certification architecture: the `3H` binomial baseline and every
smaller start are checked by Lean's kernel for `49<=H<=100`.  This advances
the independent local proof while leaving the pinned unlicensed reference
unimported.

## Release 3.15 source note

No external theorem or unlicensed implementation is imported.  The
square-root factorization split uses Mathlib's checked binomial-valuation
bounds, the local Hanson theorem from release 3.12, and the standard local
three-multiple valuation lemma.  The pinned public proof was consulted only
for high-level proof architecture; `SylvesterSchurSqrtEnvelope.lean` is an
independent implementation with a separately stated `n/3` support lemma and
explicit gap endpoints.

## Release 3.16 source note

No new external input is used.  `SylvesterSchurCentralTail.lean` is a purely
integral consequence of the independently implemented release-3.15 envelope.
Both exponential comparisons are proved by checked induction, and the cutoff
`34134` is derived from the exact inequality `320^2<=3H`; no floating-point
logarithm estimate, prime table, or unlicensed proof code is imported.

## Release 3.17 source note

The only new mathematical input is Mathlib's already pinned explicit
Chebyshev prime-count inequality.  All constants (`1024`, `4^101`, and the
rational logarithmic margins) are derived inside Lean from Mathlib's certified
logarithm bounds.  The near/far split, binomial baseline, propagation, and
finite-rectangle reduction are independent local proofs; no external table or
unlicensed implementation is imported.

## Release 3.18 source note

No new external source is used.  The improved constants `64` and `250000`
come entirely from tightening the local inequalities against the same pinned
Mathlib Chebyshev prime-count bound and certified logarithm estimates used in
release 3.17.  The proof remains an independent local implementation and
imports no numerical table or unlicensed code.

## Release 3.19 source note

No new external source is used.  The sharper low-prime exponent is derived
directly from Mathlib's checked factorization and prime-counting definitions.
The bounds `pi(m)<=m/3` and `pi(m)<=m/4` use Mathlib's
`Nat.primeCounting_add_le`, exact totient and prime-count evaluations checked
by the Lean kernel, and local arithmetic.  The finite `120<=m<690` endpoint
certificate is also a kernel computation; no external prime table,
unlicensed implementation, or opaque native decision procedure is imported.

## Release 3.20 source note

No new external source is used.  The bounded inequality
`6*pi(m)<=m+84` is an exact Lean-kernel computation from Mathlib's
`Nat.primeCounting` on a finite quotient range.  The logarithmic comparison
uses the same certified Mathlib bounds on `log 2` and antitonicity of
`log(x)/sqrt(x)` as the preceding releases.  No external prime table or
native decision procedure is used.

## Release 3.21 source note

No new external source is used.  The estimate `4*pi(m)<=m+12` is a compact
Lean-kernel computation from `Nat.primeCounting`.  The adaptive transitions,
logarithmic estimates, and far binomial baselines use only previously audited
local lemmas and Mathlib's certified logarithm bounds.  No external prime
table, unlicensed code, or native decision procedure is imported.

## Release 3.22 source note

No new external source is used.  The sparse endpoint values of
`Nat.primeCounting` and the four finite counts of integers coprime to `210`
are evaluated by Lean's kernel from Mathlib definitions.  The interval
comparison proving that every prime above `1906` lies in the counted coprime
set is formalized directly.  The adaptive transitions and logarithmic
estimates use only previously audited local lemmas and Mathlib bounds.  No
external prime table, unlicensed code, or native decision procedure is used.

## Release 3.23 source note

No new external source is used.  The bounded central binomial inequalities,
the two exceptional prime-counted gaps, and their endpoint baselines are
evaluated by Lean's kernel from Mathlib definitions.  The proof then uses the
already audited binomial monotonicity and consecutive-product reductions.
No external numerical table, unlicensed code, or native decision procedure
is used.

## Release 3.24 source note

No new external source is used.  The common endpoint `243`, all twenty
central binomial inequalities, and all 420 admissible earlier starts are
evaluated by Lean's kernel from Mathlib definitions.  The unrestricted
Sylvester--Schur assembly uses only the previously audited tail theorem, and
the square Erdős--Selfridge specialization uses the already formalized local
Hanson and Sylvester--Schur results.  No external numerical table, unlicensed
implementation, or native decision procedure is used.

## Release 3.25 source note

No new external source is used.  The Type II convolution bridge is an exact
finite rearrangement, Cauchy--Schwarz argument, support comparison, and
triangle inequality over the already pinned Vaughan decomposition.  The
source beta/gamma bounds are derived from the existing audited coefficient
lemmas.  The conditional source-block theorem only composes these results with
the previously isolated `VinogradovExponentialSumEstimate`; it does not claim
that open analytic proposition.

## Release 3.26 source note

No new external source is used.  Small-block vanishing follows directly from
the already audited support cutoffs in the pinned Vaughan identity.  The
large--large case reuses the existing conditional source-block estimate, and
the full-family result uses only finite case splitting, the exact canonical
family cardinality, monotonicity of square root, and the triangle inequality.
The open `VinogradovExponentialSumEstimate` remains an explicit hypothesis.

## Release 3.27 source note

No new external source is used.  The cube-root cutoff comparisons use only
Mathlib's real-power little-o estimates, the elementary comparison between
`Nat.log 2 B` and `log B`, and exact floor inequalities.  The product-support
and product-scale lemmas are finite consequences of the already audited
canonical short-block definitions.  The resulting theorem still states
`VinogradovExponentialSumEstimate` explicitly and does not claim the open
analytic estimate.

## Release 3.28 source note

No new external source is used.  The short-block length, cardinality, and
logarithm comparisons follow from the already audited canonical subdivision
definitions and elementary real inequalities.  The order set `{5,6}`, its
cardinality, the quarter-power scale bounds, and the geometric-majorant
comparison are all checked locally by Lean.  The release continues to expose
`VinogradovExponentialSumEstimate` as an assumption and does not claim the
remaining analytic cancellation.

## Release 3.29 source note

No new external source is used.  The scale-local width substitutions are the
already audited canonical subdivision inequalities.  All product monomial
bounds follow from membership in the literal filtered product support, and
the quarter-power improvement follows from the canonical cutoff comparison.
The exponents `298`, `197`, and `297` are checked by exact field and ring
normalization in Lean.  The release remains conditional on the explicitly
named `VinogradovExponentialSumEstimate`.

## Release 3.30 source note

No new external source is used.  Phase absorption is monotonicity of real
powers with a negative exponent; endpoint absorption uses reciprocal
monotonicity and the already audited quarter-power cutoff.  Flattening the
nested powers and the diagonal quotient is exact real-power and ring
arithmetic.  The family evaluation uses its audited exact cardinality and the
elementary bound `log₂ B+1≤3log B`.  The release continues to state
`VinogradovExponentialSumEstimate` as an explicit hypothesis.

## Release 3.31 source note

No new external source is used.  The arbitrary logarithmic absorption uses
Mathlib's standard fact that powers of `log x` are little-o of every positive
power of `x`, followed by exact reciprocal, real-power, square-root, and ring
arithmetic.  The explicit parameter choices are verified symbolically in
Lean.  The final theorem remains conditional on the separately named
`VinogradovExponentialSumEstimate` and does not claim that analytic input.

## Release 3.32 source note

No new external source is used.  The exact fiber identity is elementary
ceiling division of `mn∈[a,b)`, and the parameter change is the already proved
reciprocal-phase product rescaling.  The coefficient bounds come from the
audited Vaughan coefficient envelopes; the logarithmic inner uses the
existing finite Abel-summation theorem.  This release adds no analytic
cancellation hypothesis and does not claim Theorem 2.5.

## Release 3.33 source note

No new external source is used. Nonzero-support filtering is an exact finite
sum identity. The bounds `mâ‰¤U` and `mâ‰¤UV` use the audited support of the two
Vaughan Type I coefficients, and the family factors use the exact cardinality
`(logâ‚‚ B+1)^102`. The uniform analytic inner estimate remains open.

## Release 3.34 source note

No new external source is used.  Scale invariance is exact real-field
arithmetic, antitonicity uses positivity of the denominators, and the rounded
fiber bounds use elementary natural ceiling division.  This release proves
only the geometric transfer of the low-scale premise; the endpoint-buffer and
effective-error hypotheses of the analytic Weyl estimate remain open.

## Release 3.35 source note

No new external source is used.  The ten-block reconstruction uses the
already audited exact quotient-block decomposition.  The endpoint margin is
elementary ceiling arithmetic, the factor-four comparison follows directly
from the linear and quadratic reciprocal terms, and the local analytic bound
is an application of the existing audited four-step Weyl theorem.  This does
not yet sum or uniformize the local widths and does not claim Theorem 2.5.

## Release 3.36 source note

No new external source is used. Uniformization uses only monotonicity of
division, logarithm, and positive real powers together with the release-3.35
factor-four scale comparison. The arbitrary-subinterval decomposition is the
same exact quotient-block identity applied with general endpoints. The
rescaled active-family budget remains to be proved, so Theorem 2.5 is not
claimed.

## Release 3.37 source note

No new external source is used. The rescaled unweighted estimate is a direct
specialization of the audited release-3.36 subinterval theorem using the
release-3.34 ceiling geometry. The logarithmic estimate uses the already
audited finite Abel-summation interface, and the complete-family theorems use
the exact active-support cardinalities from release 3.33. All remaining
source-scale inequalities are explicit hypotheses; this release does not
claim Theorem 2.5.

## Release 3.38 source note

No new external source is used. The split at `F=X^4` is the literal split in
the proof of Proposition 1.12 of the pinned Matomäki--Radziwiłł--Shao--Tao--
Teräväinen source. The low branch uses the already audited Weyl theorem; the
high branch uses the explicitly named `VinogradovExponentialSumEstimateAt`
contract and existing source-parameter arithmetic. The remaining low-scale
budget and logarithmic absorption are not claimed here.

## Release 3.39 source note

No new external source is used. The low-branch estimate is elementary
arithmetic applied to the already audited Weyl budget, and the factor-four
scale comparison is ceiling arithmetic. The active-fiber lower bound uses
only the exact support and canonical cube-root cutoff already formalized from
Vaughan's identity. The resulting theorems discharge admissibility but do not
claim the remaining logarithmic majorant absorption or Theorem 2.5.

## Release 3.40 source note

No new external source is used. The reciprocal weighting is the literal
fiber length `P/m` already present after the Type I substitution. The new
family bounds use only active-support containment and the elementary identity
between the reciprocal sum on `[1,K]` and `harmonic K`. They do not claim the
branch-sensitive analytic absorption or Theorem 2.5.

## Release 3.41 source note

No new external source is used. The branch-sensitive high estimate is an
application of the already named and audited
`VinogradovExponentialSumEstimateAt C1` contract. The low estimate uses the
existing quadratic Weyl theorem plus elementary ceiling, logarithm, and real
power inequalities. Harmonic family insertion and the exact logarithmic loss
104 are internal Lean arithmetic. This release completes the quantitative
Type I families conditionally on that named source proposition; it does not
yet claim Theorem 2.5.

## Release 3.42 source note

No new external source is used. `MangoldtSourceBlock.lean` applies the exact
Vaughan identity already formalized from the pinned Proposition 1.12 proof,
the release-3.41 Type I estimates, and the release-3.31 Type II estimate. The
cutoff vanishing and three-term norm assembly are elementary. The resulting
quadratic Mangoldt estimate is conditional on the same explicitly named
Vinogradov proposition; the common source-frequency wrapper and the
Mangoldt-to-prime/Fourier transfers are not claimed here.

## Release 3.43 source note

No new external source is used. The unified interface follows directly from
the definition `F=|N|/P+|N|/P^2`, dyadic scale comparison, and elementary
real-power monotonicity. It changes no analytic assumption: the quadratic
Mangoldt estimate remains conditional only on the named Vinogradov
proposition. Prime partial summation and Fourier reconstruction remain open.

## Release 3.44 source note

No new external source is used. The half-open endpoint conversion is exact
natural interval arithmetic. The prime-power estimate is the already audited
local tail theorem specialized to a dyadic interval; its arbitrary-logarithm
absorption is elementary real-power asymptotics. The prime-log decomposition
comes from the exact Mangoldt identity, and the final unweighted estimate uses
the already audited finite reverse-Abel theorem. The sole analytic dependency
remains `VinogradovExponentialSumEstimate`; Fourier reconstruction is still
open.

## Release 3.45 source note

No new external source is used. `FourierSourceBlock.lean` unfolds the existing
Fourier definitions and proves the diagonal oscillatory-integral estimate by
ordinary differentiation, interval integration by parts, and elementary
dyadic inequalities. The combined discrepancy theorem inherits the sole
analytic dependency `VinogradovExponentialSumEstimate` from release 3.44.
The general-mode coefficient identity, derivative, and same-sign
nonstationarity are elementary and introduce no new input. Only the `(1,1)`
mode estimate is covered; unequal Fourier estimates, opposite-sign stationary
analysis, low frequencies, the zero mode, and Theorem 2.5 are not claimed.

## Release 3.46 source note

No new external source is used. `UnequalTypeIIVinogradov.lean` reuses the
already audited source proposition `VinogradovExponentialSumEstimate`, the
exact general Type II correlation identity, and the existing dyadic-block
transformed-scale bound. The new work is interface generalization: the linear
coefficient comes from `N`, the higher coefficient comes from `M`, and each
has its own source upper bound. The unequal low-scale Weyl estimate and full
Theorem 2.5 remain open.

## Release 3.47 source note

No new external source is used. `UnequalTypeIIWeyl.lean` combines the exact
Type II correlation identity, the existing four-step Weyl theorem, the
release-3.46 unequal Vinogradov callback, and elementary dyadic-band
inequalities. Its new scale comparison uses both transformed coefficients:
the linear term controls one source component and the quadratic term controls
the other on the positive inner band. The result reaches one weighted Vaughan
double block. Full double-family summation and Theorem 2.5 remain open.

## Release 3.48 source note

No new external source is used. `UnequalTypeIISourceBlock.lean` combines the
release-3.47 double-block theorem with exact finite Vaughan block summation
and reuses the already audited scalar majorant inequalities through a
blockwise coefficient having precisely the same phase scale.

`UnequalMangoldtSourceBlock.lean` uses the exact formalized Vaughan identity
and the existing Type I theorems; `UnequalPrimeSourceBlock.lean` uses the
already audited prime-power estimate and finite reverse-Abel identity. The
sole analytic dependency remains `VinogradovExponentialSumEstimate`. These
files cover nonzero quadratic coefficients, not the remaining Fourier
integral, zero-quadratic, low-frequency, or mode-assembly work. Theorem 2.5
is not claimed.

## Release 3.49 source note

No new external source is used. `UnequalFourierSourceBlock.lean` is an
elementary calculus continuation of the release-3.45 diagonal integral
argument. It differentiates the exact unequal amplitude, applies interval
integration by parts, and uses complex conjugation for the negative chamber.
The prime-sum term inherits the sole analytic dependency
`VinogradovExponentialSumEstimate` from release 3.48. Stationary opposite-sign
modes, coordinate-axis modes, and Theorem 2.5 remain open.

## Release 3.50 source note

No new external source is used. `StationaryFourierSourceBlock.lean` consists
of exact algebra for the reciprocal quadratic phase, elementary dyadic scale
comparisons, interval integrability, additive interval decomposition, and the
unit-modulus length bound for the central stationary neighborhood. It adds no
analytic assumption. Cancellation on the two far pieces, coordinate-axis
modes, and Theorem 2.5 remain open.

## Release 3.51 source note

No new external source is used. The release is an elementary continuation of
the exact integration-by-parts calculation in
`StationaryFourierSourceBlock.lean`: sign analysis of the differentiated
amplitude, dyadic logarithm inequalities, interval additivity, and explicit
real algebra. The optimized bound adds no analytic assumption. Endpoint
clipping, sign conjugation, coordinate-axis modes, and Theorem 2.5 remain
open.

## Release 3.52 source note

No new external source is used. Endpoint clipping is exact interval
additivity plus the release-3.51 one-sided estimates. Coefficient negation is
handled by complex conjugation, and the final discrepancy uses the already
audited unequal prime theorem. The sole analytic dependency remains
`VinogradovExponentialSumEstimate`. Coordinate-axis modes and Theorem 2.5
remain open.

## Release 3.53 source note

No new external source is used. The pure quadratic integral is an elementary
specialization of the audited unequal integration-by-parts identity, and its
prime term uses the existing unequal prime theorem. The pure linear axis is
not claimed: its transformed Type II phase has zero quadratic coefficient and
therefore lies outside the current quadratic Weyl/Vinogradov callbacks.

## Release 3.54 source note

No new external source is used. The high-scale pure-linear branch specializes
the existing conditional `VinogradovExponentialSumEstimate` after proving that
the derivative critical sets are empty. The low-scale branch is an internal
specialization of the audited four-step Weyl machinery to the full regular
interval. No additional analytic dependency is introduced. The pointwise
Type II chamber is complete, but its double-block, Vaughan, Mangoldt, and prime
propagation is not; the full pure-linear prime endpoint is not claimed.

## Release 3.55 source note

No new external source is used. The pure-linear double-block aggregation is
finite Cauchy--Schwarz and decay-kernel summation, and the source-family layer
reuses the already audited Vaughan block cover and scalar majorant algebra.
Its only analytic dependency is still the existing conditional
`VinogradovExponentialSumEstimate` in the high-scale branch. The pure-linear
Type I families and hence the Mangoldt and prime endpoints are not claimed.

## Release 3.56 source note

No new external source is used. `LinearAxisTypeI.lean` specializes the audited
four-step Weyl and conditional Vinogradov machinery to the empty-critical-set
pure-linear chamber and reuses the existing finite Type I source-family
ledger. The Mangoldt and prime transfers are exact Vaughan decomposition,
prime-power removal, and reverse Abel summation; the Fourier endpoint uses the
already audited pure-linear logarithmic integral. The sole analytic dependency
remains `VinogradovExponentialSumEstimate`.

## Release 3.57 source note

No new external source is used. `LowFrequencyIntegral.lean` is elementary:
real differentiation bounds `1/log`, the existing reciprocal-phase variation
bound controls the character, and interval additivity telescopes the unit
cells. It adds no analytic assumption. The missing low-frequency prime input
is explicitly the classical quantitative PNT with arbitrary logarithmic
saving for Mangoldt discrepancy; the frozen dependency currently provides
only qualitative PNT.

## Release 3.58 source note

No quantitative PNT is asserted. `ClassicalMangoldtDiscrepancyLogSaving` is a
proposition-valued interface for the standard global estimate
`psi(x)-x <<_A x/log(x)^A`. Its dyadic subinterval consequence and the full
weighted Abel consumer are proved internally. Thus the only new analytic
dependency is explicit and source-faithful; all transformations after that
contract are finite summation, variation bounds, and real inequalities.

## Release 3.59 source note

No new external source is used. Higher-prime-power removal reuses the pinned
`GafniTao.primePowerTailIntervalSum_le` estimate already audited by the
high-frequency prime transfer. The `Lambda/log` split, inverse-log comparison,
and Fourier-mode transport are exact. The only conditional analytic input in
the low-frequency row remains the explicitly named classical quantitative
PNT contract.

## Release 3.60 source note

No new external source is used. `LowFrequencyAbsorption.lean` is elementary
asymptotic and ordered-field bookkeeping applied to the release-3.59 bound.
The only analytic input remains the explicitly named quantitative-PNT
proposition; the new endpoint itself introduces no axiom.

## Release 3.61 source note

No new external source is used. The new stationary estimates are exact
interval-additivity and integration-by-parts consequences of the previously
audited clipped estimate. The same-sign refinement is elementary denominator
arithmetic for the existing reciprocal phase scale. All analytic hypotheses
remain explicit.

## Release 3.62 source note

No new external source is used. `SpecializedFourierPartition.lean` is a
finite logical partition of the previously audited PNT, Vaughan, axis,
same-sign, and stationary estimates. Its final absorption theorem uses only
elementary ordered-field identities and eventual growth of `log`. Both
analytic assumptions remain named propositions.

## Release 3.63 source note

No new external source is used. The finite Fourier assembly is an exact
finite-sum interchange and triangle inequality already present in
`FourierAssembly.lean`; the only new step is elementary eventual absorption
of the fixed coefficient `ℓ¹` norm.

## Release 3.64 source note

No new external source is used. The natural-core theorems use only order
convexity, finite minimum/maximum properties, exact unfolding of the sampled
prime set, and elementary Lebesgue interval volumes.

## Release 3.65 source note

No new external source is used. The capped-core prime preservation is an
elementary consequence of the compositeness of `2P` for `P >= 2`; the
integral comparison uses standard set-integral decomposition and Lebesgue
measure monotonicity. The empty-core and logarithmic-absorption arguments are
elementary. The same named quantitative-PNT and Vinogradov propositions are
the only analytic assumptions in the resulting finite-polynomial theorem.

## Release 3.66 source note

No new external source is used. The coefficient-tail comparison is the
triangle inequality for an absolutely summable Fourier series, and the
smooth tail envelope is obtained by summing the already audited radial cubic
coefficient bound. The prime-discrepancy transfer uses the existing exact
uniform-approximation stability theorem. Quantitative PNT and Vinogradov
remain the only analytic assumptions.

## Release 3.67 source note

No new external source is used. The inverse-square-root tail follows by
factoring the cubic radial weight into a half-power radius factor and a
summable radial `5/2` envelope. The growing-box parameter bridge is elementary
stretched-exponential domination of fixed log powers. The mode estimates use
the same explicitly named quantitative-PNT and Vinogradov assumptions as the
preceding releases.

## Release 3.68 source note

No new external source is used. `SpecializedRealScale.lean` is an elementary
formal bridge from the preceding eventual natural-scale estimate to the
literal all-real-scale specialized contract: natural ceiling, exact finite-set
extensionality, a unit Lebesgue endpoint strip, logarithm-versus-power
absorption, and a bounded-scale crude estimate. The resulting theorem remains
conditional on the same quantitative-PNT and Vinogradov propositions.

## Release 3.69 source note

No new external source is used. `QuantitativePNTBridge.lean` formalizes the
standard conversion from a de la Vallée Poussin Chebyshev-`ψ` error bound to
arbitrary logarithmic savings for the Mangoldt prefix discrepancy. The
quantitative `ψ` bound is recorded as a proposition, not imported or assumed
as an axiom. The frozen dependency's available terminal PNT theorem remains
qualitative; its sharp-Perron modules do not contain the missing contour-shift
estimate.

## Release 3.70 source note

No new external source is introduced. `ClassicalQuantitativePNT.lean`
assembles already frozen, audited results: the native Ford asymptotic
Vinogradov--Korobov zero-free theorem, its finite-low-zero rectangle bridge,
the native sharp Perron formula for `Chebyshev.psi`, and the global Jensen
zero-count estimate. The local proof weakens the Ford width to `c/log T`, uses
the deliberately coarse consequence `N(0,T)=O(T^2)`, and performs the
classical `T=exp(a*sqrt(log x))` optimization. The resulting quantitative PNT
is proved rather than postulated.

## Release 3.71 source note

No new source artifact is introduced. The completion follows the Singmaster
source's citation of Iwaniec--Kowalski, Theorem 8.25. The decisive source
distinction is that `10 ceil(log F/log X)` controls Taylor truncation error,
whereas the polynomial mean-value degree is `floor(4 log F/log X)`. The
formal proof uses quarter-scale critical moments, the already frozen explicit
Ford coefficient for the large-degree tail, and a finite maximum of native
critical coefficients below degree 10000.

## Release 3.72 source note

No new external source is introduced. The new modules formalize the standard
exponential-tilting interpretation of the already recorded finite smooth
Euler product and prove an exact equivalence with the existing critical
saddle-asymptotic contract. The remaining Gaussian local-limit estimate is
not claimed as proved.

## Release 3.73 source note

No new external source is introduced. The release formalizes the standard
probability-measure and characteristic-function interpretation of the same
finite-prime saddle tilt already fixed in release 3.72. The exact Fourier
series, saddle centering, and variance normalization are proved; Gaussian
convergence and Fourier inversion remain open.

## Release 3.74 source note

No new external source is introduced. The new module proves the standard
prime-power geometric factorization of the already defined tilted law. The
exact local contraction identity isolates `1-cos(t log p)`, matching the
classical characteristic-function route to the saddle local limit. The
frequency estimates themselves are not claimed.

## Release 3.75 source note

No new external source is introduced. This release formalizes the elementary
central-frequency part of the characteristic-function method: the standard
quadratic cosine loss, conversion of reciprocal contraction to an exponential,
and exact identification of the accumulated variance with `phiTwo`.
Complementary-frequency estimates and inversion remain open.

## Release 3.76 source note

No new external source is introduced. This release records the exact finite
central interval already implicit in the prime-local contraction argument and
proves the filter-theoretic implication from vanishing maximal normalized
prime phase to an expanding window. The required critical-regime curvature
limit, complementary-frequency estimates, and inversion are not claimed.

## Release 3.77 source note

No new external source is introduced. The quantitative curvature bound is
derived from the already formalized finite saddle equation, prime-counting
lower estimate, antitonicity of the explicit second-prime summands, and the
exact mean-value identity. This closes the central-window growth step but does
not claim complementary-frequency estimates or local-limit inversion.

## Release 3.78 source note

No new external source is introduced. The release packages the elementary
finite-product triangular-array argument for the already formalized geometric
Euler factors. It uses the exact saddle centering and curvature decomposition,
the standard quadratic remainder bound for the real exponential, and the
release-3.77 curvature growth. The prime-local third-order Taylor estimate,
complementary-frequency bounds, and inversion are not claimed.

## Release 3.79 source note

No new external source is introduced. The release derives the geometric
prime-power moments from Mathlib's geometric-series identities and proves the
needed pure-imaginary exponential remainder from the checked sine and cosine
bounds. These elementary inputs close fixed-frequency Gaussian convergence.
No complementary-frequency estimate or local-limit inversion is claimed.

## Release 3.80 source note

No new external source is introduced. This release is an exact algebraic and
probabilistic reformulation of the already pinned saddle cutoff. It records
the diverging one-sided Laplace rate and the precise normalized target for the
remaining local-limit argument; no new analytic estimate is claimed.

## Release 3.81 source note

No new external source is introduced. The release formalizes the central
segment of the saddle calculation described in the already pinned Granville
survey, equations (3.22)--(3.23): the Euler-product characteristic is
Gaussian on `|t| <= 1/log y`, which becomes the expanding normalized central
window. Mathlib's dominated-convergence theorem and Gaussian integral close
that segment. Granville's complementary Perron error is not claimed and is
the next source-facing obligation.

## Release 3.82 source note

No new external source is introduced. This release formalizes the exact
normalization of Granville (3.22) on the central segment used in (3.23). In
particular, the Fourier sign, the phase `exp(i*t*log X)`, the denominator
`sigma+i*t`, and the substitution by `sqrt(phiTwo)` are kernel checked. The
finite-height Perron cutoff error and the noncentral portion of the line are
still not claimed.

## Release 3.83 source note

No new external source is introduced. This release reuses the frozen
coefficient-free sharp-Perron kernel and its physical estimates, then proves
the smooth-coefficient convergence and inclusive cutoff identities locally.
It formalizes the finite-height comparison implicit in Granville
(3.22)--(3.23). The summed saddle-scale error and complementary segment are
not yet claimed.

## Release 3.84 source note

No new external source is introduced. The release makes the symmetric Perron
endpoint convention in Granville (3.22) exact: the kernel limits are `1`,
`1/2`, and `0`, and Tannery's theorem gives `psiNat` minus an explicit possible
half-endpoint correction. Its norm is at most `1/2`, formalizing the bounded
endpoint discrepancy absorbed by Granville's `O(1)`. The noncentral finite-line
estimate implicit in (3.23) is still not claimed.

## Release 3.85 source note

No new source is introduced. This release formalizes the subtraction implicit
between Granville (3.22) and the central segment used in (3.23): after exact
saddle normalization, the complement is the pair of tail integrals outside
the central height. Its infinite-height value is the endpoint-corrected
counting ratio minus the central Gaussian contribution. The normalized
endpoint is explicitly at most `1/(2*mainTerm)`. The analytic decay assertion
for those tails is not yet claimed.

## Release 3.86 source note

No new external source is introduced. The elementary comparison
`phiTwo <= 7*log(y)*phiOne` and the resulting explicit main-term lower bound
show that the bounded endpoint term in Granville (3.22) is negligible in every
critical regime. Thus the formal version of (3.23) is reduced exactly to decay
of the complementary line; that analytic decay is still not claimed.

## Release 3.87 source note

No new external source is introduced. The release proves directly from the
already formalized finite Euler product that the portion of Granville's
complementary line lying in the principal phase cell is negligible. It does
not claim decay beyond physical height `pi/log(y)`; that outer-frequency
estimate remains the source-facing analytic boundary.

## Release 3.88 source note

No new external source is introduced. This release verifies that the
principal-phase annulus proved negligible in release 3.87 is exactly the
corresponding portion of Granville's physical Perron line, with endpoint
`pi/log(y)`. It leaves the two outer tails beyond that endpoint unclaimed.

## Release 3.89 source note

No new external source is introduced. This release only packages and
decomposes the part of Granville's complementary Perron line beyond
`pi/log(y)`. The analytic assertion that the resulting named infinite outer
line tends to zero is not claimed.

## Release 3.90 source note

No new external source is introduced. Granville's survey states that the
central segment has a “small error” complement but does not supply the
outer-frequency inequality in the cited passage. This release derives a
global exponential envelope directly from the already formalized finite
Euler product. A lower bound for its explicit cosine-loss exponent is still
required and is not claimed.

## Release 3.91 source note

No new external source is introduced. The first omitted outer-frequency
shell is bounded directly using the already pinned qualitative PNT through
the compiled Chebyshev-theta dyadic block estimates. This is one finite part
of Granville's unstated “small error”; later shells are not yet claimed.

## Release 3.92 source note

No new external source is introduced. The adaptive choice
`ceil(exp(pi/t))`, its phase-window inequalities, and the finite
half-block-width estimate are proved directly. Prime population again uses
only the already compiled qualitative Chebyshev–PNT threshold. The full
outer-frequency “small error” remains unclaimed.

## Release 3.93 source note

No new external source is introduced. The accumulated first-shell estimate
reuses the compiled CEP dyadic alphabet, qualitative Chebyshev–PNT block
bounds, and exact saddle identities. Its divergent `u/log(u)` loss and
uniform integrand envelope are formal internal consequences. The complete
outer-frequency “small error” remains unclaimed.

## Release 3.94 source note

No new external source is introduced. This release integrates the already
proved first-shell envelope on the exact two physical Perron intervals. The
curvature upper bound and the elementary exponential-over-polynomial limit
are internal formal consequences. The first shell of Granville's unstated
outer-frequency “small error” is now complete; all later shells and the
infinite outer line remain unclaimed.

## Release 4.00 source note

No new external source is introduced. The third iterated square-root scale,
its exact rounding inequalities, the shifted CEP alphabet, and phase-window
calculation are internal; prime population still uses the pinned qualitative
PNT. This establishes a fourth finite portion of Granville's omitted
outer-frequency estimate. Its normalized integral and all later frequencies
remain unclaimed.

## Release 4.01 source note

No new external source is introduced. Rankin-ratio conversion, divergence,
exponential absorption, and symmetric-shell integration are internal. This
completes the fourth finite portion of Granville's omitted outer-frequency
estimate; later bands and the infinite line remain unclaimed.

## Release 4.02 source note

No new external source is introduced. The indexed iterated-root recursion,
closed-form rounding envelopes, and doubling shell geometry are internal
abstractions of the four already formalized finite frequency blocks.

## Release 4.03 source note

No new external source is introduced. The indexed support and phase
calculation abstract the already proved finite CEP arguments; population
continues to use only the pinned qualitative PNT.

## Release 4.04 source note

No new external source is introduced. The scale-range criterion is an
internal consequence of the exact iterated-floor rounding envelope.

## Release 3.95 source note

No new external source is introduced. The wider endpoint follows directly
from the already proved logarithmic support bound for the retained CEP
alphabet and the exact nonpositive-cosine interval. The symmetric-shell
integration is internal. This verifies one further finite portion of
Granville's unstated outer-frequency “small error”; the range beyond
`3*pi/(2*log(y))` remains unclaimed.

## Release 3.96 source note

No new external source is introduced. The square-root scale, its rounding
bounds, the shifted CEP alphabet, and the phase-window calculation are proved
internally. Prime population uses only the already pinned qualitative PNT.
This establishes a second finite portion of Granville's omitted
outer-frequency estimate; divergence and integration of its explicit loss
are not yet claimed.

## Release 3.97 source note

No new external source is introduced. The comparison with the `2/5` power
of the Rankin ratio, divergence of `u^(2/5)/log(u)`, exponential absorption,
and symmetric-shell integration are formal internal consequences of the
release-3.96 loss and earlier curvature bounds. This completes the second
finite shell of Granville's unstated outer-frequency “small error”; the
range beyond `3*pi/log(y)` and the infinite outer line remain unclaimed.

## Release 3.98 source note

No new external source is introduced. The iterated square-root scale,
rounding bounds, shifted CEP alphabet, and phase-window inequalities are
proved internally; prime population again uses only the pinned qualitative
PNT. This establishes the next finite portion of Granville's omitted
outer-frequency estimate. Divergence and integration of its explicit loss
remain unclaimed.

## Release 3.99 source note

No new external source is introduced. The `1/5` Rankin-ratio comparison,
divergence, exponential absorption, and symmetric-shell integration are
internal consequences of release 3.98 and the existing curvature bounds.
This completes the third finite shell of Granville's unstated
outer-frequency “small error”; frequencies beyond `6*pi/log(y)` and the
infinite outer line remain unclaimed.

## Release 4.05 source note

No new external source is introduced. The exact iterated-square-root
threshold and its eventual critical-regime consequences are elementary
formal deductions from the existing indexed scale definitions and the
already proved divergence of `y` and `log(y)`. This certifies fixed finite
shell prefixes only; growing-depth aggregation remains unclaimed.

## Release 4.06 source note

No new external source is introduced. The fixed-index cofactor estimate is
an internal consequence of the previously formalized critical Rankin-ratio
power bound and the indexed logarithmic scale lower bound. Prime population
uses the already pinned qualitative PNT threshold. Growing-index uniformity
and infinite outer-line aggregation remain unclaimed.

## Release 4.07 source note

No new external analytic source is introduced. The passage from all fixed
finite prefixes to one growing prefix uses the already frozen and audited
countable-diagonal theorem from `GafniTao.CountableDiagonal`. The result is a
logical uniformization of the internal shell estimates; summed integral and
post-terminal tail estimates remain unclaimed.

## Release 4.08 source note

No new external source is introduced. The indexed exponent, power transfer,
cofactor penalty, and divergence theorem abstract the already formalized
second-, third-, and fourth-shell calculations. They use only the internal
saddle identities, CEP cutoff estimate, and critical-regime limits. Generic
shell integration and aggregation remain unclaimed.

## Release 4.09 source note

No new external source is introduced. The generic exponential absorption,
signed envelope, shell-width identity, and symmetric integral estimate are
internal abstractions of the previously certified concrete shell integrals.
Moving-prefix summation and the residual infinite tail remain unclaimed.

## Release 4.10 source note

No new external source is introduced. Finite-sum convergence and the second
slow diagonal are internal topological consequences of the fixed-index
integral theorems and the frozen countable-diagonal principle. The exact
contiguous-segment identity and post-terminal infinite-tail estimate remain
unclaimed.

## Release 4.11 source note

No new external source is introduced. The telescoping identity is an exact
formal consequence of interval-integral additivity and the common saddle
normalization. It converts the internal finite shell sum to a contiguous
physical Perron segment. The post-terminal infinite-tail estimate remains
unclaimed.
