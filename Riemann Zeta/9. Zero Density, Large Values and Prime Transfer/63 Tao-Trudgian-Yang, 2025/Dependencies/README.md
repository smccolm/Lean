# Dependency record

The compatibility experiment selected one Lean 4.30/mathlib graph and vendored
the ten ANTEDB modules needed by the current asymptotic and exponential-
sum layers. The later Heath--Brown beta deduction also uses the pinned native
Gafni--Tao derivative-proof closure described below. The attributed subset is in `ANTEDBFrozen/`; it is compiled as a
separate local Lake package and imported from source by the extension.

## Intended dependencies

| Dependency | Role | Current version boundary | Decision needed |
|---|---|---|---|
| local `RiemannZeta` / Guth--Maynard | zeta analytic foundations, large values, Ingham/Huxley/GM density | Lean 4.30, pinned local mathlib | imported as a local source dependency |
| frozen ANTEDB subset | asymptotics, phase functions, exponential sums | upstream `0880406...`, backported to Lean 4.30 | imported from `ANTEDBFrozen/` |
| pinned `GafniTaoNative` | proved native VMVT and Heath--Brown kth derivative | local node-74 snapshot; same canonical foundation and pins | imported from `GafniTaoNative/`; 469 ledger files, 463 reachable Lean modules |
| paper-time ANTEDB | Python/blueprint reproduction | Lean placeholder only; Python is relevant | run separately, never use as Lean proof dependency |
| Mathlib | analysis, finite sums, convexity, rationals | must be a single revision in the target graph | inherit from selected unified package |
| `PrimeNumberTheoremAnd` | transitive local zeta/PNT infrastructure | local root pin | inherit through local foundation |

## Compatibility decision

The narrow backport succeeded. Two compatibility-only edits are recorded in
`ANTEDBFrozen/README.md`; `SOURCE_SHA256SUMS.txt` pins the resulting source.
The root package remains the authority for the shared mathlib and
`PrimeNumberTheoremAnd` pins.

Do not point a production Lake dependency at ANTEDB `main`. Do not let Lake
resolve two independent mathlib revisions in one proof graph. Do not treat
prebuilt oleans from a different Lean version as compatible.

## Frozen dependency gates

Any vendored dependency must include:

- upstream URL, commit, license, and source hash;
- an unmodified-source hash ledger plus a documented patch series;
- exact toolchain and manifest;
- a boundary README naming which modules are imported;
- a scan for prohibited proof shortcuts under this repository's policy; and
- a focused build/audit invoked by the principal runner.

## Native derivative-proof boundary

`GafniTaoNative/` preserves the complete 460-module local import closure of
`GafniTao.WooleyNative`, with canonical foundation module-path adaptations.
Two additional proved PNT prefixes retain the source through `WeakPNT`
and `chebyshev_asymptotic`; they avoid the unrelated admitted preliminaries
in the monolithic external Wiener module. The canonical PNT checkout is
unchanged. No frozen `RiemannZeta` library or second Mathlib/PNT revision is
introduced.

The package README, `PROVENANCE.json`, installed hash ledger and upstream
PNT license record this exact boundary. Installation alone is not a proof
of the target beta estimate. The target bridge must derive the signed
physical derivative, interval/tail convention and uniform scale losses
from the actual ANTEDB model phase, then consume the native theorem.

`Tools/verify_gafnitao_sources.ps1`, invoked by
`run_tao_trudgian_yang_build.bat`, rejects changed, missing, extra and
unreachable pinned files. The target dependency audit checks nonprivate
theorems by their defining pinned module, including globally named PNT
theorems. Both build BATs remain mandatory after implementation changes.

## Byte preservation

Scoped `.gitattributes` rules preserve the exact bytes of pinned Sources,
ANTEDB/native dependency files, the generated certificate and the permanent
counterexample across Git checkouts. The runner requires this policy file.
No repository Git configuration was changed. A read-only comparison of
509 protected files against HEAD found 507 byte-identical; the only two
differences are the documented native README correction and its ledger.
