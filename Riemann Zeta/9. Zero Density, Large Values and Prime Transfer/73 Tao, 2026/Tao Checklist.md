# Tao 2026 Checklist

This is the detailed readiness and future completion ledger for node 73.
Checked groundwork items do not imply that any mathematics from the paper has
been formalized.

## Groundwork completed

- [x] Preserve the human-readable RH-map node `73 Tao, 2026/`.
- [x] Identify the intended paper from the local inference agenda and verify
  it against arXiv.
- [x] Pin arXiv `2603.27990v2` as both PDF and TeX source archive.
- [x] Record SHA-256 hashes and provenance under `Sources/`.
- [x] Create distinct README, Architecture, Checklist, Goal Prompt, Research
  Agenda, Crosswalk, Sources, and Reproduction Manifest roles.
- [x] Reserve `Dependencies/`, `Extension/`, `Sources/`, and `Tools/`.
- [x] Create a minimal isolated `Tao2026` Lake package shell.
- [x] Add a local scaffold runner that produces no persistent logs.

## Source study - initial survey complete; authoritative crosswalk pending

- [ ] Extract the v2 source into an intentional, documented source directory
  if direct TeX navigation is needed.
- [ ] Record every definition used by the principal statements.
- [ ] Record exact theorem, proposition, lemma, and equation numbers.
- [ ] Separate elementary arithmetic inputs from analytic-number-theory inputs.
- [ ] Identify all uses of exceptional-interval estimates and their exact
  quantifiers, uniformity, and numerical thresholds.
- [ ] Determine whether the RH Map's node-71 and node-74 arrows correspond to
  literal source dependencies, replaceable estimates, or only conceptual
  ancestry.
- [ ] Populate `Tao Crosswalk.md` with source-accurate rows.

## Dependency boundary - candidates identified; immutable freeze pending

- [ ] List the exact public declarations required from Guth-Maynard.
- [ ] List the exact public declarations required from Gafni-Tao.
- [ ] Decide whether node 74 should be consumed as an immutable source snapshot,
  a tagged package dependency, or a smaller extracted interface.
- [ ] Pin all chosen revisions and record hashes before importing them.
- [ ] Ensure node 73 does not import mutable development files accidentally.
- [x] Add the exact node-74 Mathlib revision justified by the source-object
  and analytic-infrastructure audit; keep later packages crosswalk-driven.

## Formalization - active

- [ ] Freeze exact Lean statement contracts before proving helper machinery.
- [ ] Design the production module graph from the source proof, not filenames
  guessed from the abstract.
- [ ] Implement definitions without changing the paper's conventions silently.
- [ ] Prove the selected release scope without `sorry`, `admit`, project
  postulates, or unsafe proof bypasses.
- [ ] Add an executable `Audit.lean` only when public theorem endpoints exist.
- [ ] Replace the scaffold runner with a release verifier only when it has real
  source, import, diagnostic, and axiom contracts to enforce.

## Release acceptance - future

- [ ] Every claimed result has an exact source crosswalk.
- [ ] Every vendored or copied dependency has immutable provenance.
- [ ] The production root builds with zero project diagnostics.
- [ ] Public endpoints pass a transitive axiom audit.
- [ ] Source hashes and frozen dependency boundaries pass.
- [ ] README claims match the executable audit and reproduction manifest.
- [ ] The architecture dashboard reflects actual, not aspirational, status.

## Current stop line

The groundwork campaign ends before paper formalization. The next agent must
not mark any source-study, dependency, proof, or release item complete merely
because the directory skeleton and minimal Lake package build.
