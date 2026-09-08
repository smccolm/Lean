# Tao 2026 formalization

This directory is the active formalization project for Terence Tao,
*Products of consecutive integers with unusual anatomy*, arXiv
`2603.27990v2`. The paper and its TeX source are pinned under `Sources/`.

**Status:** Proposition 2.3(i),(iii) milestone. Bertrand's clause (i) and the
exact Guth--Maynard application in clause (iii) are proved and audited; none of the four main
Theorems 1.7--1.10 is proved or claimed. The isolated `Extension/` package
contains the compiled arithmetic-anatomy, interval, counting, and
asymptotic-language definitions required to state the source results, plus a
kernel-checked proof of Tao's global constant-length prime-free endpoint
measure bound, derived from the frozen Guth--Maynard/Gafni--Tao chain. It also
proves the exact unique `p²m` representation of `B¹` and Tao's finite
prime-indexed smooth-number sum. It also proves the unique `a²b³`
representation of positive powerful numbers and the exact finite squarefree-
cube sum for `VB¹`; neither one-term asymptotic is claimed yet.
The source's `H≥1` convention is enforced in every interval predicate, and the
exact type-`F₃` right-endpoint correspondence with the three-factorial square
equation is proved. The finite largest-index projection is also proved to hit
exactly `F₃∩[1,x]`, yielding the lower cardinal direction for Theorem 1.10.
The one-term `F₃¹` square-multiple characterization and its distinct-square
subfamily give an unconditional `⌊√x⌋-1` lower bound first for `F₃¹`, then
for `F₃` and factorial solutions; the corresponding triple is explicit.
These finite bounds have been lifted to the complete reverse-big-O half of
the square-root `PowerScale` contracts for Theorems 1.9 and 1.10.

Node 73 keeps the human-readable location assigned by the RH Map. The exact
1,226-module Lean import closure of `GafniTao.Theorem11` is frozen under this
node with per-file SHA-256 hashes. The first Tao-facing quantitative bridge is
proved. The literal variable-length dyadic prime-free set has now been shown
measurable and eventually contained in Gafni--Tao's discrepancy exceptional
set, with the higher-prime-power tail retained and bounded. The finite dyadic
assembly and the `theta >= 1` monotonicity case are also proved, yielding the
full source range `theta > 2/15`.

## Layout

- `Sources/`: exact paper artifacts, version pins, provenance, and hashes.
- `Dependencies/GafniTaoFrozen/`: immutable, hashed source closure of the
  Gafni--Tao theorem input, including its frozen Guth--Maynard foundation and
  PNT+ dependencies.
- `Extension/`: isolated Lean package named `Tao2026`, pinned to the exact
  Mathlib revision used by node 74.
- `Tools/`: reproducible snapshot refresh tooling and the evolving
  warning-failing project verifier. It is not yet the final proof-release
  verifier.

## Current verification

From this directory, run:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The runner checks all pinned source hashes, all 1,226 frozen dependency hashes and the exact
frozen file set, the raw Mermaid contract, toolchain/dependency pins, direct
production-root coverage, forbidden proof shortcuts in both production and
frozen source, the axiom audit, and the warning-free Lake build. Its current
success certifies Proposition 2.3(i),(iii), the exact one-term sums, and the
factorial endpoint/counting bridges; it does not certify a main theorem.

## Project-control documents

The node follows the useful role separation established in node 74:

- `README.md`: public status, layout, and entry points.
- `Tao Architecture.md`: raw Mermaid planning dashboard; no Markdown wrapper.
- `Tao Checklist.md`: detailed readiness and future completion ledger.
- `Tao Goal Prompt.md`: activation contract for the future implementation
  agent.
- `Tao Research Agenda.md`: source-first sequencing and scope controls.
- `Tao Crosswalk.md`: active paper-to-Lean mapping and semantic-gap ledger.
- `Tao Sources.md` and `Sources/`: source policy, artifacts, pins, and hashes.
- `Tao Reproduction Manifest.md`: what can truthfully be reproduced now.

## Next legitimate step

The Baker--Harman--Pintz paper and exact theorem locator are now pinned and
hashed, but its analytic proof is not formalized. Formalize that input in
Proposition 2.3(ii) and proceed to
the earliest downstream Section 3/4/6 consumer of clause (iii), recording its exact source
statement in the crosswalk before implementation.

## Deliberate non-claims

This development milestone does not claim any of Theorems 1.7--1.10,
publication readiness, external review, or a route to the Riemann Hypothesis.
The formal connection to nodes 71 and 74 is limited to the frozen, hashed
dependency closure and the audited quantitative bridge described above.

## Repository synchronization

`push_to_github.bat` is the existing owner-operated repository synchronization
script. It is not called by the build or development verifier.
