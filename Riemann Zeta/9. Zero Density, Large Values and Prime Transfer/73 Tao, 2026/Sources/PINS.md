# Tao 2026 source pins

## Primary paper

- Author: Terence Tao
- Title: *Products of consecutive integers with unusual anatomy*
- arXiv: `2603.27990v2`
- Version date: 22 April 2026
- Abstract record: <https://arxiv.org/abs/2603.27990v2>
- PDF origin: <https://arxiv.org/pdf/2603.27990v2>
- TeX source origin: <https://arxiv.org/e-print/2603.27990v2>
- Retrieved for this scaffold: 7 September 2026

## Baker--Harman--Pintz prime-interval input

- Authors: R. C. Baker, G. Harman, and J. Pintz
- Title: *The Difference Between Consecutive Primes, II*
- Journal: *Proceedings of the London Mathematical Society* 83 (2001),
  532--562
- DOI: <https://doi.org/10.1112/plms/83.3.532>
- Publisher record: <https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/plms/83.3.532>
- Archived PDF origin:
  <https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf>
- Retrieved: 8 September 2026
- Local artifact: `baker-harman-pintz-2001.pdf`
- Source locator: Theorem 1, journal page 532 (PDF page 1), states the
  sufficiently-large backward interval result with exponent `0.525 = 21/40`.
  The quantitative lower bound completing the proof is on journal page 561
  (PDF page 30). Section 2, beginning on journal page 535 (PDF page 4), invokes
  Watt's mean-value theorem; Lemma 2 is on journal page 536 (PDF page 5).

The publisher and ResearchGate endpoints rejected non-browser retrieval. The
local artifact is therefore the byte-identical identity recorded here from the
accessible University of Maryland archival mirror; the DOI above remains the
bibliographic authority.

## Matomäki--Radziwiłł--Shao--Tao--Teräväinen prime-equidistribution input

- Authors: Kaisa Matomäki, Maksym Radziwiłł, Xuancheng Shao, Terence Tao, and
  Joni Teräväinen
- Title: *Singmaster's conjecture in the interior of Pascal's triangle*
- arXiv: `2106.03335v1` (the sole arXiv version)
- Version date: 7 June 2021
- Journal: *The Quarterly Journal of Mathematics* 73 (2022), 1137--1177
- DOI: <https://doi.org/10.1093/qmath/haac006>
- Abstract record: <https://arxiv.org/abs/2106.03335v1>
- PDF origin: <https://arxiv.org/pdf/2106.03335v1>
- TeX source origin: <https://arxiv.org/e-print/2106.03335v1>
- Retrieved: 8 September 2026
- Local artifacts: `singmaster-2106.03335v1.pdf` and
  `singmaster-2106.03335v1.tar`
- Source locator: Proposition 1.12(i)--(ii) in `main.tex`. Part (i) gives the
  prime exponential-sum estimate for the phase `N/p + M/p^j`; part (ii)
  obtains the smooth two-periodic weight estimate by Fourier expansion. Tao's
  Theorem 2.5 restates part (ii), and the later argument only consumes its
  specialization `M=N`, `j=2`.
- Proof locator: the proof of Proposition 1.12 in `main.tex` reduces the
  periodic-weight statement to the exponential-sum statement, treats small
  frequencies by the prime number theorem, and treats the remaining
  frequencies through Vaughan's identity, the paper's Vinogradov derivative
  estimate, and its Type I/II bounds.

This pin establishes the exact cited source and statement. It does not import
the paper as a Lean dependency or claim that Proposition 1.12 has already been
formalized.

## Erdős--Selfridge factorial-fiber input

- Authors: P. Erdős and J. L. Selfridge
- Title: *The Product of Consecutive Integers Is Never a Power*
- Journal: *Illinois Journal of Mathematics* 19 (1975), 292--301
- MR: `MR51 #12692`
- Archived PDF origin: <https://combinatorica.hu/~p_erdos/1975-46.pdf>
- Bibliographic authority: <https://renyi.hu/en/node/4094>
- Retrieved: 8 September 2026
- Local artifact: `erdos-selfridge-1975.pdf`
- Source locator: Theorem 1 is the full assertion that
  `(n+1)⋯(n+k)=x^l` has no solutions for `n≥0`, `k≥2`, and `l≥2`.
  Tao uses its square case after Theorem 1.10 to show that, for fixed
  `(a₂,a₃)`, at most two values of `a₁` share the required factorial
  squarefree component.

No completed Lean proof was located. The Google DeepMind
`formal-conjectures` entry for the corresponding consecutive-integer theorem
contains a `sorry` body and is research metadata only; it is not a permissible
dependency for this project.

The local filenames and SHA-256 values are authoritative in
`SHA256SUMS.txt`. These third-party artifacts retain their original rights and
are not covered by the repository's MIT-0 grant.
