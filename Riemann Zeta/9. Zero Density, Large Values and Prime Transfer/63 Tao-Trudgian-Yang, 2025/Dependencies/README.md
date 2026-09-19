# Dependency record

The compatibility experiment selected one Lean 4.30/mathlib graph and vendored
only the ten ANTEDB modules needed by the current asymptotic and exponential-
sum layers. The attributed subset is in `ANTEDBFrozen/`; it is compiled as a
separate local Lake package and imported from source by the extension.

## Intended dependencies

| Dependency | Role | Current version boundary | Decision needed |
|---|---|---|---|
| local `RiemannZeta` / Guth--Maynard | zeta analytic foundations, large values, Ingham/Huxley/GM density | Lean 4.30, pinned local mathlib | imported as a local source dependency |
| frozen ANTEDB subset | asymptotics, phase functions, exponential sums | upstream `0880406...`, backported to Lean 4.30 | imported from `ANTEDBFrozen/` |
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
