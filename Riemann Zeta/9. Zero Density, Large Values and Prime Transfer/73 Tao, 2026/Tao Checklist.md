# Tao 2026 Checklist

This is the detailed readiness and future completion ledger for node 73.
Checked groundwork and input items do not imply that a public theorem from the
paper has been formalized.

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
- [x] Compile source-faithful arithmetic-anatomy, interval, counting, and
  asymptotic-language definitions and exact conclusion contracts for
  Theorems 1.7--1.10.

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

## Dependency boundary - first analytic boundary frozen

- [x] Identify `GafniTao.Theorem11` as the root of the first required
  Guth--Maynard/Gafni--Tao analytic boundary.
- [x] Freeze its exact recursive source import closure: 852 Gafni--Tao, 291
  Guth--Maynard foundation, and 83 PNT+ modules.
- [x] Pin the selected revisions and record every copied Lean source hash.
- [x] Ensure node 73 imports the frozen package rather than mutable sibling
  development files.
- [x] Add a deterministic refresh tool that follows both `import` and
  `public import` declarations.
- [x] Add the exact node-74 Mathlib revision justified by the source-object
  and analytic-infrastructure audit; keep later packages crosswalk-driven.
- [ ] Freeze any additional dependency closure only when a later crosswalk row
  demonstrates that it is required.

## Formalization - active

- [x] Freeze exact Lean conclusion contracts for Theorems 1.7--1.10, with
  literal counting functions and distinct quantified asymptotic predicates.
- [x] Establish the initial production module graph from the source proof.
- [x] Implement the principal definitions without silently changing the
  paper's conventions.
- [x] Prove existence and uniqueness of the positive square-times-squarefree-
  cube parameterization of powerful numbers used before Corollary 2.11.
- [x] Prove the exact finite `VB¹` identity
  `∑_{b≤x, squarefree} ⌊√(x/b³)⌋`, with representation injectivity.
- [ ] Derive the `ζ(3/2)/ζ(3) √x` asymptotic for `VB¹` from the exact sum.
- [x] Prove and audit a uniform fixed-power bound below one for the frozen
  dyadic Gafni--Tao discrepancy exceptional measures when `2/15 < θ < 1`.
- [x] Formalize the literal closed prime-free endpoint set and its measurable
  variable-length dyadic counterpart.
- [x] Control the full higher-prime-power tail and transfer the discrepancy
  estimate to a fixed-power bound for the genuine dyadic prime-free measure.
- [x] Assemble the dyadic estimates into Tao's constant-length `[0,x]`
  exceptional-measure statement and prove the full `theta > 2/15` range of
  Proposition 2.3(iii).
- [x] Prove Proposition 2.3(i) with Tao's `N/2 < p <= N` endpoints from
  Mathlib's Bertrand theorem.
- [x] Prove the exact unique `n=p²m` characterization of `B¹` and the finite
  identity `#(B¹∩[1,x]) = ∑_{p≤√x} Ψ(⌊x/p²⌋,p)`.
- [ ] Formalize Proposition 2.1's analytic smooth-number estimates and use
  them to prove Lemma 1.6; the exact finite identity alone is not the
  asymptotic.
- [x] Pin and hash the Baker--Harman--Pintz primary source, with exact theorem
  and proof locators.
- [ ] Formalize the Baker--Harman--Pintz bound in Proposition 2.3(ii). The
  pinned paper is provenance only and is not proof evidence.
- [ ] Prove the selected release scope without `sorry`, `admit`, project
  postulates, or unsafe proof bypasses.
- [x] Add an executable development `Audit.lean` covering every current Tao
  theorem declaration.
- [x] Extend the development verifier with real source, import, diagnostic,
  frozen-hash, file-set, and axiom contracts.
- [ ] Promote the development verifier to a proof-release verifier only when
  all four public theorem endpoints exist.

## Release acceptance - future

- [ ] Every claimed result has an exact source crosswalk.
- [ ] Every vendored or copied dependency has immutable provenance.
- [ ] The production root builds with zero project diagnostics.
- [ ] Public endpoints pass a transitive axiom audit.
- [ ] Source hashes and frozen dependency boundaries pass.
- [ ] README claims match the executable audit and reproduction manifest.
- [ ] The architecture dashboard reflects actual, not aspirational, status.

## Current stop line

The current verified stop line is Proposition 2.3(i) and (iii). It does not prove any
of Theorems 1.7--1.10. Do not mark a later crosswalk, proof, or release item
complete merely because this upstream power-saving estimate builds.
