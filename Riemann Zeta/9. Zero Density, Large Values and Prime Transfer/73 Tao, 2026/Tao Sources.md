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
- Tao-facing use: equality of two factorial squarefree components would make
  a product of at least two consecutive positive integers a square; excluding
  that case leaves at most two consecutive factorial indices in each fiber.
- Formalization warning: the online `formal-conjectures` declaration is
  explicitly unfinished (`sorry`) and cannot be imported or copied as proof.

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
