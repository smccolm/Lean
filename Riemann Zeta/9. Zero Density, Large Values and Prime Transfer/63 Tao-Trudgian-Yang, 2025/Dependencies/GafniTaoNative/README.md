# Pinned Gafni–Tao derivative-theorem dependency

This package contains the complete 460-module local import closure of
`GafniTao.WooleyNative` from node 74, plus two proved PNT source prefixes.
It imports the canonical repository foundation and its existing dependency
pins. It does not include or shadow a frozen `RiemannZeta` library.

The intended boundary declarations are
`GafniTao.heathBrownVMVTMainConjecture_native` and
`GafniTao.heathBrownKthDerivativeTheorem_native`.
Installing this dependency does not by itself prove EPZAE-12's beta bound.

## Adaptations

The 460 mathematical source files retain every declaration and proof.
Line endings and terminal whitespace are normalized. Seven files replace
the neighboring frozen-foundation module paths by canonical module paths:
`RiemannZeta.PublicationContract` becomes `PublicationContract`;
`RiemannZeta.GuthMaynard.*` becomes `GuthMaynard.*`;
`RiemannZeta.External.PNT.*` becomes `GuthMaynardExternal.PNT.*`.
Declaration namespaces are unchanged.

`FordPrimePacketEventually` imports `GafniTao.PrimeConsequences`.
That module is the exact prefix through `chebyshev_asymptotic`
(lines 1–185) of node 74's clean PNT `Consequences.lean`), changing
only the Wiener import. `GafniTao.WienerSource` retains lines 1–2397
of the neighboring clean `Wiener.lean`, ending after `WeakPNT`;
its existing header-linter suppression is removed. The prefix is
self-contained and has no admitted declaration. The neighboring source's
documented omission of four unused preliminary declarations is preserved.
These are proved source excerpts, not assumptions or replacements of the
prime-number theorem.

The first compatibility build exposed the two unrelated admitted Wiener
declarations in the monolithic external checkout. That warning-producing
build is not release evidence. The local proved prefixes avoid importing
that monolithic module; the canonical PNT checkout is not edited.

## Provenance and verification

`PROVENANCE.json` records original paths, hashes, exact prefix boundaries,
module-path adaptations, and toolchain pins. `SOURCE_SHA256SUMS.txt`
records the installed source, package configuration, provenance and license.
Treat the installed source as pinned input. Do not refresh it implicitly.

The principal `run_tao_trudgian_yang_build.bat` must verify this ledger,
the complete import closure, zero Lean diagnostics and transitive theorem
dependencies. Both it and the foundation `run_lake_build.bat` remain
mandatory after proof, import, audit, package or runner changes.

`PNT-LICENSE` is the upstream Apache-2.0 license for the two PNT excerpts.
The Gafni–Tao sources retain their existing notices; no new license is
asserted for the owner's local formalization.
