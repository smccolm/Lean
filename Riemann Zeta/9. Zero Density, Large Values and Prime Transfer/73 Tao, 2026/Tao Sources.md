# Tao 2026 Sources

`Sources/` is the provenance authority for node 73. It currently contains the
exact v2 PDF and TeX source archive for the target paper, the Baker--Harman--
Pintz paper used in Proposition 2.3(ii), plus pin and hash records.

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
row-by-row source crosswalk. The Baker--Harman--Pintz artifact is pinned, but
pinning a paper is not a Lean proof of Proposition 2.3(ii).
