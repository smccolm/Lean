# Frozen source pins

- Gafni--Tao: arXiv `2505.24017v1` (PDF and source archive saved locally).
- Guth--Maynard: arXiv `2405.20552v2` (PDF saved locally).
- Tao--Trudgian--Yang: arXiv `2501.16779v1` (PDF saved locally).
- Ford zeta-growth bound: author PDF `zetabd.pdf` (saved locally).
- Ford zero-free region: arXiv `1910.08205v4` (PDF and TeX source saved locally).
- Bourgain--Demeter--Guth, *Proof of the main conjecture in Vinogradov's
  mean value theorem for degrees higher than three*: arXiv `1512.01565v2`
  (PDF and TeX source saved locally).  This is the exact deep input cited by
  Heath--Brown's derivative estimate; the local proof branch targets its
  critical-endpoint consequence rather than treating the citation as proof.
- Wooley, *Nested efficient congruencing and relatives of Vinogradov's mean
  value theorem*: arXiv `1708.01220v2` (PDF and the arXiv gzip-compressed TeX
  source saved locally).  This is the arithmetic proof selected for the
  all-degree critical VMVT dependency; Bourgain--Demeter--Guth remains the
  independently pinned proof cited by Heath--Brown and Pintz.
- Pintz, *On the density theorem of Halasz and Turan*, Acta Mathematica
  Hungarica 166 (2022), 48--56, DOI `10.1007/s10474-021-01204-z`
  (author manuscript `PJ_Halasz_Turan0505.pdf` saved locally from the
  Hungarian Academy of Sciences repository).
- D. R. Heath--Brown, *The twelfth power moment of the Riemann-function*,
  Quarterly Journal of Mathematics 29 (1978), 443--462, DOI
  `10.1093/qmath/29.4.443` (publicly accessible scan saved locally from the
  Norwegian University of Science and Technology course archive).
- D. R. Heath--Brown, *A new k-th derivative estimate for exponential sums
  via Vinogradov's mean value*, arXiv `1601.04493v3` (PDF and source archive
  saved locally).
- J. Pintz, 2023 near-one zero-density manuscript used for the
  `sigma <= 23/24` cutoff (downloaded PDF saved as
  `pintz-density-near-one-2023.pdf`; bibliographic identification and theorem
  crosswalk are recorded in `Gafni-Tao Sources.md`).
- Aleksandar Ivić source scans used during the zero-density source audit:
  `ivic-zero-density-1984.pdf` and `ivic-zeta-book-scan.pdf`. These are
  intentional research-source captures; extracted page images and temporary
  PDF tooling are not retained.
- ANTEDB/expdb: commit `2b1aea3de263996c4da3042c115126bff601c618`
  (repository archive saved locally).
- Frozen Lean foundation: tag `gm-foundation-freeze-v1.0.1`, peeled commit
  `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`.
- Foundation Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Foundation PNT+: `4ecb950126c4290293c5662dfe0e884123171df5`.
- Lean: `v4.30.0`.

The build uses `Dependencies/PrimeNumberTheoremAndClean`, a source-derived
83-file transitive closure of that exact PNT+ revision. Its
`SOURCE_SHA256SUMS.txt` records upstream and retained hashes: 82 source files
are byte-identical, while `Wiener.lean` differs only by deletion of an
unreachable four-declaration block containing two admitted declarations.

`SHA256SUMS.txt` records the pinned downloaded bytes. The 1978 Heath--Brown
twelfth-moment and Ivić scans are pinned above. Davenport, Turán, and the 1979
Heath--Brown paper remain bibliographic dependencies not redistributed here
until legally accessible versioned artifacts are located.
