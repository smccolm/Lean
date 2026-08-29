# GM foundation source freeze

Status date: 29 August 2026
Contract identifier: `GM-PUBLICATION-CONTRACT-v1`

This file fixes the source editions and statement conventions used by
`RiemannZeta/PublicationContract.lean`. It is a reproducibility record, not an
independent referee report. The exact Lean declarations and the canonical
verifier remain authoritative for what the repository proves.

## Primary Guth--Maynard source

- Larry Guth and James Maynard, “New large value estimates for Dirichlet
  polynomials,” *Annals of Mathematics* **203** (2026), no. 2, 623--675,
  DOI [`10.4007/annals.2026.203.2.6`](https://doi.org/10.4007/annals.2026.203.2.6).
  The journal records publication on 1 March 2026.
- Accepted manuscript: [`arXiv:2405.20552v2`](https://arxiv.org/abs/2405.20552v2),
  revised 7 April 2026. This is the version used for equation and section
  navigation where the journal HTML does not expose the display text.

The publication-facing Lean contracts deliberately distinguish two source
conventions:

- Theorem 1.1's displayed polynomial is the closed sum `N <= n <= 2N`, with
  positive phase, a one-separated finite set in `[0,T]`, and `|b_n| <= 1` only
  on the polynomial support. `PublishedGuthMaynardLargeValues` states that
  contract. The internal large-values theorem uses `(N,2N]` and a global
  coefficient bound; `guthMaynardLargeValues_published_native` proves the
  endpoint/support bridge rather than identifying the two definitions.
- Theorem 1.2 is stated for `1/2 <= sigma <= 1`. The internal Section 13.1
  interface `GuthMaynardZeroDensity` starts at `sigma = 7/10`.
  `guthMaynardZeroDensity_published_native` proves the full range by using the
  native Ingham theorem below `7/10`, the native Guth--Maynard theorem above
  it, and an explicit exponent comparison.

## Classical and downstream sources

- A. E. Ingham, “On the estimation of N(sigma,T),” *Quarterly Journal of
  Mathematics* os-11 (1940), 201--202,
  DOI [`10.1093/qmath/os-11.1.201`](https://doi.org/10.1093/qmath/os-11.1.201).
- M. N. Huxley, the classical density estimate used in the Guth--Maynard
  full-range comparison. The project freezes its exact exponent in
  `PublishedHuxleyZeroDensity`; external reviewers should check the historical
  bibliographic edition independently.
- D. R. Heath-Brown, “A large values estimate for Dirichlet polynomials,”
  *Journal of the London Mathematical Society* (2) **20** (1979), no. 1,
  8--18, DOI [`10.1112/jlms/s2-20.1.8`](https://doi.org/10.1112/jlms/s2-20.1.8).
  This, not Heath-Brown's fourth-moment paper, is the `[HB]` source cited by
  Guth--Maynard for the difference-set double-sum estimate.
- James Maynard and Kyle Pratt, “Half-isolated zeros and zero-density
  estimates,” *International Mathematics Research Notices* **2024** (2024),
  no. 19, 12978--13014,
  DOI [`10.1093/imrn/rnae191`](https://doi.org/10.1093/imrn/rnae191).
- C. P. Hughes and Matthew P. Young, “The twisted fourth moment of the Riemann
  zeta function,” *Journal für die reine und angewandte Mathematik* **641**
  (2010), 203--236, DOI
  [`10.1515/CRELLE.2010.034`](https://doi.org/10.1515/CRELLE.2010.034),
  [`arXiv:0709.2345`](https://arxiv.org/abs/0709.2345).
- W. Duke, J. B. Friedlander, and H. Iwaniec, “A quadratic divisor problem,”
  *Inventiones Mathematicae* **115** (1994), 209--217,
  DOI [`10.1007/BF01231758`](https://doi.org/10.1007/BF01231758).

## ANTEDB/Expdb snapshot

The online blueprint is pinned to Git commit
[`2b1aea3de263996c4da3042c115126bff601c618`](https://github.com/teorth/expdb/tree/2b1aea3de263996c4da3042c115126bff601c618).
Use stable source labels rather than unversioned prose such as “ANTEDB Lemma
11.5,” because some numeric references in the blueprint point to Ivić rather
than to an ANTEDB lemma. The relevant labels at this snapshot are:

- `blueprint/src/chapter/zero_density.tex`:
  `thm:ingham_zero_density2`, `huxley-bound`, `guth-maynard-density`;
- `blueprint/src/chapter/additive_energy.tex`:
  `reflect`, `hb-double`, `guth-maynard-lvt`;
- `blueprint/src/chapter/large_values.tex`: `huxley-lv`.

## Machine and dependency freeze

- Lean: `leanprover/lean4:v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- PrimeNumberTheoremAnd:
  `4ecb950126c4290293c5662dfe0e884123171df5`.
- GitHub Actions are pinned to immutable commit SHAs in
  [`../../.github/workflows/riemann-zeta-ci.yml`](../../.github/workflows/riemann-zeta-ci.yml):
  `actions/checkout` v7.0.1 at
  `3d3c42e5aac5ba805825da76410c181273ba90b1`, `leanprover/lean-action`
  v1.5.0 at `38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9`, and
  `actions/upload-artifact` v7.0.1 at
  `043fb46d1a93c77aae656e7c1c64a875d1fc6a0a`.
- CI first primes the DFI-heavy proof prefix into the exact-SHA Lake cache and
  then runs the unchanged canonical verifier in a dependent job. The split
  addresses runner termination risk and does not weaken the verified scope.
- The release verifier is `scripts/verify_release.ps1 -Mode release`; it writes
  a SHA-bound log and JSON manifest and refuses a dirty tree.

## Claim boundary

The freeze establishes a versioned source comparison, exact Lean proposition
contracts, kernel/audit coverage, and reproducible verification. It does not
establish independent semantic review, journal publication of this
formalization, or community canonicalization. Those remain external #20 gates.
