# Tao 2026 Sources

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

## Current limits

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
