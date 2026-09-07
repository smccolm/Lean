# Frozen foundation adapter

The tag `gm-foundation-freeze-v1.0.1` peels to commit
`2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, but that commit's checked-in
Lake manifest still names the package `EllipsePerimeter` and pins Lean
`v4.30.0-rc2`. It therefore does not export the `RiemannZeta` library as a
Lake dependency.

To keep the proof source frozen while making the boundary reproducible,
`FrozenFoundation/RiemannZeta/` and `FrozenFoundation/RiemannZeta.lean` are
extracted byte-for-byte with `git archive` from the peeled commit. The
isolated `lakefile.toml` supplies only the missing library adapter and pins the
known foundation dependencies:

- Lean `v4.30.0`;
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- PNT+ `4ecb950126c4290293c5662dfe0e884123171df5`.

`FrozenFoundation/SHA256SUMS.txt` records the deterministic `git archive` used
to populate the vendored files. The isolated integrity runner compares the
extracted tree against that archive. No file below
`FrozenFoundation/RiemannZeta/` may be edited.
