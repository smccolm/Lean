# Minimal clean PNT+ dependency

This directory is a reproducible, source-minimal derivative of
`AlexKontorovich/PrimeNumberTheoremAnd` commit
`4ecb950126c4290293c5662dfe0e884123171df5`. It contains exactly the 83-file
internal PNT+ import closure used jointly by the frozen foundation and the
Gafni–Tao extension.

Eighty-two retained files are byte-for-byte copies of that commit. In
`PrimeNumberTheoremAnd/Wiener.lean`, one unreachable four-declaration block was
removed: `prelim_decay_2`, `AbsolutelyContinuous`, `prelim_decay_3`, and
`decay_alt`. The two preliminary decay declarations were incomplete in the
pinned source and caused build warnings even though neither they nor their two
local consumers occur in the dependency graph of `WeakPNT` or
`chebyshev_asymptotic`.

No theorem consumed by `Consequences` was edited. In particular, `WeakPNT`,
`WeakPNT'`, `WeakPNT''`, and `chebyshev_asymptotic` are copied verbatim. The
isolated runner checks the retained-file hashes, the patched `Wiener.lean`
hash, the absence of the removed declarations, the exact source closure, and
the dependency build before building Gafni–Tao.

`SOURCE_SHA256SUMS.txt` records both the upstream and retained hashes. The
package keeps the parent experiment's exact Lean, Mathlib, and LeanArchitect
pins. Its checked-in `lake-manifest.json` resolves Mathlib to
`c5ea00351c28e24afc9f0f84379aa41082b1188f` and LeanArchitect to
`b72ae37b08d264cf371f164f4ba60c5257c17727`.
