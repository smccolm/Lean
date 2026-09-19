# Dependency plan

No dependency source tree is copied here during planning. The completed Tao
project shows why: indiscriminately freezing transitive packages can add
gigabytes without resolving semantic compatibility.

## Intended dependencies

| Dependency | Role | Current version boundary | Decision needed |
|---|---|---|---|
| local `RiemannZeta` / Guth--Maynard | zeta analytic foundations, large values, Ingham/Huxley/GM density | Lean 4.30, pinned local mathlib | import as source dependency after EPZAE-01 |
| ANTEDB current Lean modules | asymptotics, phase functions, exponential sums | Lean 4.32, moving upstream now frozen in `Sources/` | backport selected modules or upgrade target graph |
| paper-time ANTEDB | Python/blueprint reproduction | Lean placeholder only; Python is relevant | run separately, never use as Lean proof dependency |
| Mathlib | analysis, finite sums, convexity, rationals | must be a single revision in the target graph | inherit from selected unified package |
| `PrimeNumberTheoremAnd` | transitive local zeta/PNT infrastructure | local root pin | inherit through local foundation |

## Recommended compatibility experiment

Create a temporary package on the local Lean 4.30/mathlib pin and copy only
the selected current ANTEDB modules plus their Apache-2.0 notices. Attempt to
build, recording every API incompatibility. If the patch is small, keep a
clearly attributed frozen port. If it is large, evaluate upgrading the local
foundation in a separate, fully verified branch.

Do not point a production Lake dependency at ANTEDB `main`. Do not let Lake
resolve two independent mathlib revisions in one proof graph. Do not treat
prebuilt oleans from a different Lean version as compatible.

## Future frozen dependency requirements

Any vendored dependency must include:

- upstream URL, commit, license, and source hash;
- an unmodified-source hash ledger plus a documented patch series;
- exact toolchain and manifest;
- a boundary README naming which modules are imported;
- a scan for prohibited proof shortcuts under this repository's policy; and
- a focused build/audit invoked by the principal runner.
