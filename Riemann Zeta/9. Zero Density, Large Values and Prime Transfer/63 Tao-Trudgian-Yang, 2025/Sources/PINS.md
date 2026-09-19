# Source pins

## Primary paper

- arXiv identifier: `2501.16779v1`
- submission timestamp: 2025-01-28 08:03:12 UTC
- title: *New exponent pairs, zero density estimates, and zero additive energy
  estimates: a systematic approach*
- authors: Terence Tao, Tim Trudgian, Andrew Yang
- PDF: `tao-trudgian-yang-2501.16779v1.pdf`
- source archive: `tao-trudgian-yang-2501.16779v1.tar`
- extracted source: `TaoTrudgianYang-v1-source/`

The archive's main TeX filename contains `v2`; this is an upstream internal
filename and does not change the arXiv version pin.

## ANTEDB snapshots

- `antedb-expdb-paper-time-9953003.zip` archives commit
  `9953003a48f46fe8075ccf9534321f98f656032e`, the final commit before the
  primary paper submission timestamp.
- `antedb-expdb-current-0880406.zip` archives commit
  `088040634e8300f87e80f431d8bdc38c42cc8e11`, the current Lean-enabled commit
  inspected on 2026-09-19.

The paper-time archive is for computation reproduction. The current archive is
for Lean API study and potential attributed porting. Neither archive should be
silently refreshed.

## Supporting arXiv inputs

- Trudgian--Yang `2306.05599v3`: exponent-pair tables and prior hull.
- Matomäki--Teräväinen `2403.13157v1`: zero density implies large values.
- Heath--Brown `1601.04493v3`: kth-derivative estimate.
- Guth--Maynard `2405.20552v1`: PDF and the arXiv-served single-file
  `guth-maynard-2405.20552v1.tex.gz` source cited by the 2025 paper.
- Guth--Maynard `2405.20552v2`: current PDF used for comparison; consult the
  local Guth--Maynard source freeze for the exact v1/v2 theorem crosswalk used
  by the formalization.

All hashes are recorded in `SHA256SUMS.txt` after acquisition.
