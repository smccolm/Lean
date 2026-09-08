# Tao 2026 Sources

`Sources/` is the provenance authority for node 73. It currently contains the
exact v2 PDF and TeX source archive for the target paper, plus pin and hash
records.

## Primary paper

Terence Tao, *Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`, revised 22 April 2026.

- `Sources/tao-unusual-anatomy-2603.27990v2.pdf`
- `Sources/tao-unusual-anatomy-2603.27990v2.tar`

See `Sources/PINS.md` for origin URLs and `Sources/SHA256SUMS.txt` for exact
artifact identities.

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
row-by-row source crosswalk.
