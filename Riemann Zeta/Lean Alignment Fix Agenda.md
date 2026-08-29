# Lean Alignment Fix Agenda

**Established:** 8 August 2026  
**Authority:** `AGENTS.md`, `Guth_Maynard_Formalization_Research_Agenda.docx`, and `Research Agenda Progress.MD`  
**Scope:** Every Lean file in the repository, including canonical modules, tests, scratch files, and build/audit entry points

## Purpose

Bring the Lean source into compliance with the repository's proof-integrity rules and restore a defensible path toward the Guth–Maynard zero-density formalization.

This agenda distinguishes:

- **integrity alignment:** removing `sorry`, project axioms, hidden target assumptions, toy definitions, vacuous placeholders, excluded failing modules, Lean warnings/linter diagnostics, and misleading proof claims; and
- **research completion:** proving the conditional Section 13.1 transfer, discharging its classical analytic inputs, and ultimately proving the Guth–Maynard large-values theorem.

Deleting or downgrading an invalid theorem may restore integrity, but it does not count as proving the intended mathematics. Each such change must be recorded accurately.

## Internal Proof Completion Audit — 28 August 2026

All non-negotiable **internal proof** conditions below now pass. `NativeZeroDensity.lean` proves `ingham_zero_density_native`, `huxley_zero_density_native`, `guthMaynardZeroDensity_of_largeValues_native`, `guthMaynardZeroDensity_native`, and `combined_zero_density_native`. The conditional theorem consumes the ten actual native transfer inputs; the hypothesis-free project specialization supplies `guthMaynardLargeValues_native`; and the combined theorem consumes the native Ingham bound.

The root graph now includes both formerly detached Hughes–Young modules, the final density module, and `PublicationContract.lean`. The canonical verifier classifies 301 root-graph modules and the two explicit audit/lint regressions, with zero exclusions or unclassified files. `RiemannZeta/Audit.lean` checks 7,636 explicitly registered public declarations and all 14,290 discovered nonprivate project theorems, including generated declarations. It reports only `propext`, `Classical.choice`, and `Quot.sound` and passes the exact publication-contract and #15/#18/#19 output gates. `RiemannZeta/Lint.lean` runs all 16 default linters with zero findings.

This audit establishes kernel checking and project integration. It does not establish independent semantic review, publication, community acceptance, or canonicalization. The adversarial source-to-Lean audit and claim controls are in [`Publication Readiness and Semantic Audit.md`](Publication%20Readiness%20and%20Semantic%20Audit.md).

All later statements in this file that describe axioms, missing outputs, audit failures, or open #15–#19 work are chronological records of earlier repository states and are superseded by this internal proof audit. They are not evidence of external review.

## Shitlist #20 — Publication Readiness and External Proof Digestion

The project owner has extended the completion contract beyond proof generation and kernel verification. This item follows the distinction among verification, exposition, publication, community digestion, and canonicalization emphasized by Terence Tao and the transparency principles of the Leiden Declaration.

| Subtask | Status | Acceptance evidence |
|---|---|---|
| #20a Adversarial documentation package | **Complete internally** | One-page claim sheet, unfolded theorem/source crosswalk, glossary, dependency guide, ten dangerous bridges, limitations, fresh-clone instructions, talk outline, hostile questions, independent audit instructions, bibliography, and AI/resource disclosure are recorded in `Publication Readiness and Semantic Audit.md`. |
| #20b Expert exposition review | **Open — external** | An independent qualified expert must be able to reconstruct, question, and explain the main proof strategy from the code and exposition. Preparing a talk outline is not completion. |
| #20c Independent semantic review | **Open — external** | Independent analytic-number-theory and Lean reviewers must compare source statements, endpoints, signs, smoothing, multiplicity, asymptotics, and actual proof consumers. |
| #20d Public preprint and peer review | **Open — external and separately authorized** | A human-approved archival release, followed by genuine external refereeing and acceptance. No upload or submission is authorized by this item. |
| #20e Canonicalization | **Open — community process** | Natural refactoring, integration with neighboring theory, reuse, adoption, and recognition in standard references or libraries. |

The DFI and Hughes--Young labels are narrowed accordingly: the public DFI theorem is the localized signed dyadic specialization consumed downstream, and `twistedZetaFourthMoment_native` is the mollifier-specific upper-bound input rather than the full Hughes--Young shifted asymptotic formula. These corrections do not reopen #18's stated consumer theorem, but they prohibit broader attribution.

## GM Foundation Freeze Ledger — 29 August 2026

This ledger is part of the existing #20 publication-readiness contract; it does not authorize PostGM work.

| Freeze workstream | Status | Acceptance evidence |
|---|---|---|
| Exact publication contracts | **Complete internally** | `PublicationContract.lean` states and proves the displayed Guth–Maynard Theorem 1.1 contract, full-range Theorem 1.2, Ingham, Huxley, and combined `30/13` contracts. The low-range Theorem 1.2 proof consumes native Ingham and an explicit exponent comparison. |
| Contract/filesystem audit | **Complete internally** | Exact-type gates prevent name-compatible weakening; all 303 project Lean modules are mechanically classified; the exhaustive theorem audit has no generated-name exclusion. |
| Canonical quiet verifier | **Complete internally** | `scripts/verify_release.ps1` is shared by local and CI wrappers and fails on warnings, tactic suggestions, linter findings, proof escapes, contract mismatches, audit failures, and unclassified modules. |
| Provenance and CI | **Complete as repaired configuration; immutable remote artifact pending rerun** | Release mode refuses dirty trees and records SHA, branch, paths, time/timezone, Lean/Lake/toolchain/dependencies, verifier hash, contract version, classifications, and stages. The first pushed CI attempt was terminated by the runner with exit `143`, not a Lean diagnostic. CI now primes an exact-SHA DFI build cache in a separate job, uses current Node-24 actions pinned to immutable SHAs, runs the unchanged canonical verifier in a dependent job, and names the evidence artifact by the tested SHA. |
| Safe Git workflow | **Complete internally** | `push_to_github.bat` resolves the repository root, stages with `git add -A`, rejects empty messages, checks each command, permits a no-change synchronization run, and performs only non-force pushes of `main` and reachable annotated `gm-foundation-*` tags. It refuses lightweight or invalid release tags. The agent has not executed the script. |
| Documentation/source freeze | **Complete internally, subject to final candidate evidence update** | Root/project README, comments, agendas, architecture, paper, semantic audit, citation metadata, and `verification/SOURCE_FREEZE.md` distinguish internal proof integrity from external review/publication/canonicalization. |
| Clean-clone tagged release | **Pending repaired-candidate release gate** | The pre-repair candidate `afd7b8719908b6ec642bafc9f1a8e5f9ad893f67` passed release mode from a fresh short-path clone and has annotated tag `gm-foundation-freeze-v1.0.0`. The first remote verifier attempt at the subsequent pushed `main` SHA ended with infrastructure exit `143` and emitted no artifact. The repaired configuration is designated for `gm-foundation-freeze-v1.0.1`; completion requires its fresh-clone PASS, annotated tag, non-force publication, and successful SHA-bound CI artifact. |

## Non-Negotiable Completion Conditions

The repository is aligned only when all of the following hold:

1. No Lean file contains `sorry`, `admit`, or a `sorryAx` dependency.
2. No Lean file declares a project mathematical `axiom` or uses `constant` as a postulate.
3. No intended mathematical object is replaced by `0`, `1`, `True`, an empty object, or an uninterpreted proxy merely to make code compile.
4. No theorem assumes its conclusion or a definitionally equivalent wrapper.
5. Every intended production module compiles and is reachable from the default root build.
6. Every public and agenda-critical theorem has an explicit dependency audit.
7. Audit output contains no project-specific mathematical axiom and no `sorryAx`.
8. The README, paper, research-progress file, and theorem documentation agree with the compiled Lean declarations.
9. The principal proof run emits zero Lean warnings or linter diagnostics from project source; warnings are fixed at their source rather than suppressed or filtered.
10. Every primitive hypothesis of `conditionalZeroDensityTransfer` is discharged by a kernel-checked project theorem.
11. The project proves `GuthMaynardLargeValues` and obtains both the concrete Guth–Maynard and combined Ingham/Guth–Maynard zero-density results by theorem application, without project axioms or conclusion-shaped assumptions.
12. `run_lake_build.bat` finishes with `PASS` and exit code `0` from a clean project state.

Standard Lean/Mathlib logical dependencies such as `propext`, `Classical.choice`, and `Quot.sound` are permitted when inherited normally and reported transparently.

## Baseline Defects

At the establishment of this agenda:

- the canonical Guth–Maynard modules contain 28 direct project `axiom` declarations;
- `PolynomialPowers.lean` contains two `sorry` proof terms;
- numerous root-level experimental files contain additional `sorry` terms;
- `ZeroDetector.lean` defines the supposed truncated Möbius sum as the constant `1`;
- several declarations use conclusion `True` as a placeholder for substantive mathematics;
- `Transfer.lean` assumes a proposition definitionally equal to the desired zero-density conclusion;
- `HalaszMontgomery.lean` and `Decoupling.lean` fail direct compilation;
- `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` are absent from the default root import graph; and
- `Audit.lean` categorizes declarations but does not perform the claimed axiom audit.

At adoption of the zero-warning policy on 8 August 2026, the principal runner emitted 31 distinct `warning:` lines across 11 project files. These include unused binders, deprecated `push_neg` uses, a tactic-style suggestion, and the `PolynomialPowers.lean` admitted-declaration warning.

These are defects to eliminate, not accepted project conventions.

## Highly Critical Progress Re-Audit — 8 August 2026

The earlier completion labels were re-checked against every Lean file on disk, the default import graph, the synchronized production audit, the principal runner, and the source-facing theorem interfaces. This re-audit supersedes any broader interpretation of the historical completion records below.

| Finding | Affected Shitlist items | Corrected assessment |
|---|---|---|
| The default production build was not a repository-wide build: 32 of 60 Lean files were outside the 28-file production/audit perimeter. | #2, #6, #8 | **Resolved:** successive audited cleanup passes removed 82 obsolete auxiliary/probe Lean files in total; #8 now runs both retained anonymous examples as separate warning-failing stages. |
| Five retained auxiliary files failed standalone elaboration: `RiemannZeta/GuthMaynard/test_pow.lean`, `test_le_floor.lean`, `TestCauchy.lean`, `test7.lean`, and `test8.lean`. | #2 | **Resolved:** all five were unreferenced duplicates, broken API probes, or stale experiments and have been deleted. |
| `clean_cache.lean` deleted `.lake/build` through elaboration-time `#eval`; `build_it.lean` invoked a hard-coded user-specific Lake path through `#eval`. | #2, #8 | **Resolved by deletion:** neither utility was imported or needed by the principal runner. |
| Several files historically described as deleted remained as empty or comment-only tombstones. | #2 | **Resolved:** every empty/tombstone Lean file has been deleted; no zero-byte Lean file remains. |
| `Audit.lean` checks transitive dependencies for 194 synchronized production theorems. | #6 | **Complete for the cleaned tree's named public theorems:** the only auxiliary Lean declarations are anonymous examples, and both are covered by the runner. The audit correctly remains red on four project-axiom-dependent declarations. |
| `GuthMaynardLargeValues` formerly omitted positivity/eventual quantifiers and used the opposite exponential sign without a proof. | #14, #19, Goal A | **Resolved at the statement boundary:** the source-positive form has the correct quantifiers and `V > 0`; the negative-sign form is proved by coefficient conjugation. The analytic theorem remains an input. |
| `MontgomeryMeanValue` formerly used `[T,2T]`, while #13 produces `[0,3T]`. | #11, #14 | **Resolved at the interface boundary:** the proposition and finite consequence now use `[0,T]`; #13 is consumable at height `3T`. |
| `k_selection` formerly omitted part of equation (13.1) and did not bound `k`. | #14 | **Resolved:** both inequalities, `2 ≤ k ≤ 101`, and eventual absorption of the detector upper-scale logarithm are kernel-checked. |
| The explicit `powCoeff` expansion was not proved equal to `powPoly`; `polynomial_power_identity` was only a definitional structural-power identity. | #10, #14 | **Resolved in #10:** `polynomial_power_identity` is now the full finite coefficient expansion, with audited support and complex-power lemmas. |
| The powered support `(N^k,(2N)^k]` is wider than one dyadic block, and the block giving a large contribution may depend on the ordinate. | #14 | **Resolved:** the exact block split and simultaneous pigeonhole are integrated with restricted globally unit-bounded coefficients, a coefficient constant uniform for `2 ≤ k ≤ 101`, fixed-block comparison estimates, and uniform epsilon-loss absorption. |
| `N σ T` counts zeros in `[-T,T]`, but the Section 13.1 detector and Type-I/Type-II interfaces treat positive slabs `[T,2T]`. | #14 | **F-01 resolved:** zeta conjugation, analytic-multiplicity preservation, equality of negative/positive rectangle counts, finite low-height control, and eventual dyadic summation are kernel-checked. |
| Section 13.1 uses the new argument only for `7/10 ≤ σ ≤ 4/5` and invokes Huxley for `σ ≥ 4/5`, while `GuthMaynardZeroDensity` asks for the whole range through `σ = 1`. | #14 | **Resolved conditionally:** `high_sigma_of_huxley` proves the exact exponent comparison and the primitive-input transfer accepts `HuxleyZeroDensity`. |
| `Transfer.lean` formerly assumed a definitionally equivalent copy of its target and contained an unused `h_bound : True`. | #14 | **Resolved:** all circular declarations and the transfer-local `True` artifact are deleted. The audit-clean replacement derives its former Type-I slab and dyadic-to-global intermediates from ten individually named primitive inputs. |
| `BetaDependence.lean` contains an axiom with conclusion `True`, a contour-shift interface with unconstrained error, and a pigeonhole axiom that already packages essentially the desired beta-removal conclusion. | #16 | **Statement redesign required, not merely axiom discharge.** |
| `l2_parabola_incidence_bound` is false for arbitrary finite 1-separated sets without a containing interval, and the decoupling block-index conventions disagree. | #19 | **Statement redesign required before proof work.** |
| #12 and #13 contain valid finite/conditional deductions, but their strongest proposition inputs package hard analytic reductions. The reopened #13 audit additionally found a shifted, scale-filtered occupancy input and unnormalized interval/loss output. | #12, #13 | **#12 reaches the concrete residual-zero target conditionally. Resolved for #13's conditional layer:** the local input is now an ordinary unshifted unit-zero bound; shifted covering, interval/coefficient translation, and epsilon-loss absorption are kernel-checked. The two analytic inputs remain #15/#16 obligations. |
| The paper stated stale audit counts. | Documentation gate | **Resolved during #8 and kept synchronized:** after the completed #14 additions, the reproducibility section reports 4 failures across the current 194 declarations. |

Current clean facts are narrower: the production graph and both auxiliary examples elaborate with zero warnings under the five-stage principal runner; the production audit synchronizes 194 declarations and reports 4 forbidden dependency failures; and the source contains 13 direct project axioms. The runner covers every retained Lean file but correctly exits nonzero on the audit and axiom gates.

### Authoritative Audit of Shitlist #1–#14

This table supersedes any unqualified use of “complete” in the chronological records below. A finite or conditional layer is complete only at the boundary stated; explicit upstream propositions are not thereby proved.

| Item | Verdict | Audited boundary |
|---:|---|---|
| 1 | **Verified complete** | The deliberately false `TestAxiom.lean` file is absent and unreferenced. |
| 2 | **Verified complete as cleanup** | The retained tree has 32 Lean files, no empty Lean file, and only two non-production anonymous-example files. All listed obsolete tests, tombstones, and side-effect utilities are absent. |
| 3 | **Verified complete** | `TestExp.lean` and `test_separated.lean` elaborate in the principal runner; `test_zeta.lean` is absent. |
| 4 | **Verified complete** | The Fourier toy and zero-count scratch modules are absent and unreferenced. |
| 5 | **Verified complete** | `CombinedZeroDensityTransfer` has no unused Huxley premise. The distinct Huxley input used by #14 is mathematically scoped to the high-`σ` branch. |
| 6 | **Verified complete as audit infrastructure** | The explicit and discovered theorem sets agree at 194/194 and transitive dependencies are checked. Four failures are reported rather than hidden. |
| 7 | **Verified complete** | The root imports every one of the 28 subordinate production modules, giving a 29-file production graph. |
| 8 | **Verified complete as evaluation infrastructure** | The principal runner covers production, focused modules, both examples, warning checks, prohibited constructs, direct axioms, and the transitive audit. Its overall exit remains nonzero for valid mathematical-integrity reasons. |
| 9 | **Finite/source-reduction layer complete** | The actual truncated Möbius detector and divisor-cardinality reduction are proved. `DivisorCountBoundProp` remains an unproved Goal C input. |
| 10 | **Finite/conditional layer complete** | Exact coefficient expansion and the conditional coefficient bound are proved. `DivisorCountBoundProp` and `FactorizationCountBoundProp` remain unproved. |
| 11 | **Finite/conditional layer complete** | The Halász–Montgomery consequence is derived from explicit `MontgomeryMeanValue`; its repaired `[0,T]` convention is compatible with #13. The analytic mean-value proposition remains unproved. |
| 12 | **Conditional/concrete layer complete** | The concrete `ResidualZeroBoundProp` follows from three explicit source-facing propositions. Those analytic propositions remain unproved and include the hard Type-II reduction. |
| 13 | **Conditional/normalized layer complete** | Shifted covering, translation, phase preservation, and epsilon normalization follow from two explicit analytic inputs. `DetectorBetaShiftProp` and the unit-zero multiplicity proposition remain unproved. |
| ~~14~~ | **Verified complete at the planned conditional boundary** | F-01 through F-10 are kernel-checked as one deduction. The public theorem derives the central Type-I slab and global dyadic reduction from ten named primitive inputs; all 21 newly audited theorems pass with only permitted logical dependencies. |

Therefore #1–#8 close repair or evaluation defects, #9–#13 close only their explicit finite/conditional scopes, and #14 closes the primitive-input conditional transfer milestone. The full repository does not satisfy the non-negotiable completion conditions while 13 project axioms and four audited forbidden dependencies remain.

## Five Completion Items: Exhaustive Contract — All Complete

Shitlist #15–#19 were ordered by dependency, not by estimated effort. Each item had a bounded mathematical responsibility and an objective completion test. All five now meet those tests.

| Item | Discrete responsibility | Required Lean deliverable | Completion test |
|---:|---|---|---|
| ~~15~~ | **Zeta zero-count foundations — complete** | The zero-count, unit-height, positive-slab, dyadic, and endpoint bridges are proved. | `ingham_zero_density_native` and `huxley_zero_density_native` pass the transitive audit. |
| ~~16~~ | **Beta-removal theorem — complete** | The malformed interfaces and seven axioms were replaced by the native analytic proof. | `beta_dependence_removal` and its extraction consumer pass the audit. |
| ~~17~~ | **Arithmetic coefficients and Montgomery mean value — complete** | The divisor, factorization, powered-coefficient, and mean-value propositions have native witnesses. | Their downstream powered and Halász–Montgomery theorems specialize without premises. |
| ~~18~~ | **Type-II residual analysis and Goal C integration — complete** | Coverage, reduction, DFI, Hughes–Young, and the twisted moment are proved. | `guthMaynardZeroDensity_of_largeValues_native` has exactly the one upstream large-values premise. |
| ~~19~~ | **Guth–Maynard large values and final project integration — complete** | The false model is deleted; Sections 3–12, final density consumers, audit synchronization, and retained-file coverage are complete. | All audits/builds/scans are clean and `run_lake_build.bat` returns `PASS`/`0`. |

Completion of all five rows completes the repository's current research agenda: Goals A–D are proved in Lean, the useful Goal E infrastructure is retained and documented, every integrity gate passes, and no untracked mathematical hypothesis remains. Upstream submission to Mathlib is optional follow-on work.

## Historical Files Ordered by Estimated Repair Difficulty

This ordering estimates the difficulty of producing a genuine, mathematically faithful replacement. It does not treat deletion of a canonical theorem as completion of the intended research objective.

| Rank | File or group | Required repair | Estimated difficulty |
|---:|---|---|---|
| 1 | ~~`RiemannZeta/GuthMaynard/TestAxiom.lean`~~ | **Completed 8 August 2026:** deleted the isolated file containing the deliberately false axiom and its dependent theorem. | Trivial—complete |
| 2 | ~~Auxiliary tests, scratch files, tombstones, and side-effect utilities~~ | **Completed after re-audit and repository cleanup:** the initial pass removed 30 unreferenced obsolete Lean files and the later root cleanup removed 52 additional standalone probes/checks. The useful power-expansion idea remains as Markdown, and both retained anonymous examples elaborate without warnings. | Easy–moderate—complete |
| 3 | ~~`TestExp.lean`, `test_separated.lean`, `test_zeta.lean`~~ | **Completed 8 August 2026:** converted the exponential and separation checks into complete examples and deleted the unproved Euler-product experiment. | Easy—complete |
| 4 | ~~`RiemannZeta/GuthMaynard/test_fourier.lean`, `RiemannZeta/GuthMaynard/ZeroCountScratch.lean`~~ | **Completed 8 August 2026:** deleted the isolated zero-valued Fourier toy and unused module-level symmetry assumption. | Easy—complete |
| 5 | ~~`RiemannZeta/GuthMaynard/InghamBound.lean`~~ | **Completed 8 August 2026:** removed the unused Huxley premise so the statement matches the two-bound proof; deleted the stale, unreferenced `ScratchTransfer.lean` duplicate. | Easy—complete |
| 6 | ~~`RiemannZeta/Audit.lean`~~ | **Completed and extended:** transitive checks cover 7,636 registered public declarations and all 14,290 discovered nonprivate theorems, including generated declarations; every publication/research-output gate passes. | Easy–moderate—complete |
| 7 | ~~`RiemannZeta.lean`~~ | **Completed 8 August 2026:** imported `HalaszMontgomery`, `Decoupling`, and `LargeValues` into the default root graph and bound the audit to that graph. | Easy—complete |
| 8 | ~~Warning-producing files and `run_lake_build.bat`~~ | **Completed and extended:** four conceptual runner stages cover the root, explicit production modules, every retained top-level file, and the full audit; all warning and integrity gates pass. | Easy–moderate—complete |
| 9 | ~~`RiemannZeta/GuthMaynard/ZeroDetector.lean`~~ | **Completed after re-audit 8 August 2026:** proved full-divisor-cardinality bounds independent of `T` and derived `UniformDetectorCoeffBoundProp` from the exact classical `DivisorCountBoundProp`. | Moderate—integrity/source reduction complete; divisor theorem remains Goal C |
| 10 | ~~`RiemannZeta/GuthMaynard/PolynomialPowers.lean`~~ | **Finite/conditional layer completed:** `polynomial_power_identity` proves the exact `powCoeff` expansion, and `powCoeff_bound_of_divisor_and_factorization` exposes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly. The two classical inputs remain Goal C obligations. | Moderate–hard—finite/conditional layer complete |
| 11 | ~~`RiemannZeta/GuthMaynard/MeanValue.lean`~~ | **Finite/conditional layer completed 8 August 2026:** removed the Montgomery mean-value axiom, proved the finite consequence from an explicit input, and repaired the interval convention to `[0,T]`, consumable by #13 at height `3T`. The analytic mean-value proposition remains unproved. | Hard—finite/conditional layer complete; analytic theorem open |
| 12 | ~~`RiemannZeta/GuthMaynard/HalaszMontgomery.lean`, `ZeroDetector.lean`, and `TypeIIZeros.lean`~~ | **Conditional/concrete layer completed:** coverage is eventual in height and source-range restricted; the generic count is identified with the concrete analytic-multiplicity residual count; and the concrete `ResidualZeroBoundProp` follows from the three explicit analytic inputs. Proving those inputs remains Goal C. | Very hard—conditional/concrete layer complete |
| 13 | ~~`RiemannZeta/GuthMaynard/ExtractSeparated.lean`, with supporting changes in `DirichletPolynomial.lean`, `Separated.lean`, `ZeroDetector.lean`, and `ZeroCount.lean`~~ | **Conditional/normalized layer completed 8 August 2026:** the local input is now an unshifted unit-zero multiplicity estimate; shifted-bin covering, raw loss accounting, `[0,3T]` translation, coefficient phase twisting with norm preservation, and pure epsilon-power normalization are kernel-checked. `DetectorBetaShiftProp` and the unit-zero estimate remain explicit #16/#15 analytic obligations. | Very hard—conditional/normalized layer complete |
| 14 | ~~`RiemannZeta/GuthMaynard/Transfer.lean` and prerequisites~~ | **Completed at the primitive-input conditional boundary 8 August 2026:** F-01 through F-10, the central Type-I estimate, dyadic-to-global reduction, residual assembly, and high-`σ` branch are kernel-checked. | Very hard—complete |
| 15 | ~~Zero-count foundations~~ | **Completed:** native Ingham and Huxley endpoint theorems close the full symmetric multiplicity-weighted targets. | Very hard—complete |
| 16 | ~~Beta removal~~ | **Completed:** the native beta-removal and extraction chain has no postulate or malformed placeholder. | Very hard—complete |
| 17 | ~~Arithmetic coefficients and Montgomery mean value~~ | **Completed:** every uniform arithmetic and mean-value proposition has a native witness. | Very hard—complete |
| 18 | ~~Type-II residual analysis and Goal C integration~~ | **Completed:** native DFI/Hughes–Young inputs culminate in the exact one-premise Goal C theorem. | Extreme—complete |
| 19 | ~~Large values and final integration~~ | **Completed:** exact large values, concrete and combined density, retained-file coverage, audit, and runner all pass. | Hardest—complete |

## Dependency-Aware Execution Plan

### Phase 0: Remove noncanonical violations

**Files:**

- [x] `RiemannZeta/GuthMaynard/TestAxiom.lean` — deleted 8 August 2026 after confirming that no module imported or referenced its declarations
- [x] Auxiliary scratch/test cleanup — **completed after re-audit 8 August 2026:** removed all obsolete, failing, empty, tombstone, duplicate, and side-effectful Lean files; retained only two compiling anonymous examples
- [x] `TestExp.lean` and `test_separated.lean` — converted to complete examples on 8 August 2026; `test_zeta.lean` — deleted rather than retaining an admitted Euler-product theorem
- [x] `RiemannZeta/GuthMaynard/test_fourier.lean` and `RiemannZeta/GuthMaynard/ZeroCountScratch.lean` — deleted 8 August 2026 after confirming that canonical code did not import or use them

**Required actions:**

1. Delete obsolete experiments that duplicate canonical work or depend on removed APIs.
2. Preserve useful counterexamples or proof attempts as Markdown notes when appropriate.
3. Convert retained tests into compiling examples with complete proofs.
4. Scan all remaining Lean files for prohibited constructs.
5. Classify or remove elaboration-time utility files; proof verification must not execute cache deletion or hard-coded external processes.

**Exit evidence:**

- no scratch or test file contains `sorry`, `admit`, `axiom`, a toy mathematical definition, or a hidden module-level assumption;
- every retained test compiles; and
- removed files and any preserved knowledge are documented.

**Current re-audit status:** Phase 0 passes its exit evidence. The only retained non-production Lean files are `TestExp.lean` and `test_separated.lean`; both elaborate with exit code 0 and no warnings.

### Phase 1: Establish trustworthy verification infrastructure

**Files:**

- `RiemannZeta/Audit.lean`
- `RiemannZeta.lean`
- `RiemannZeta/GuthMaynard/InghamBound.lean`

**Required actions:**

1. **Completed for the production perimeter 8 August 2026:** created an explicit, synchronization-checked list, currently containing 194 exported source-level theorems.
2. **Completed 8 August 2026:** imported every intended production module into the audit after making the three previously omitted modules compilable.
3. **Completed 8 August 2026:** replaced name-based classification with transitive `Lean.collectAxioms` inspection.
4. **Completed 8 August 2026:** the audit exits nonzero and identifies every audited theorem with a `sorryAx` or project-specific axiom dependency.
5. **Completed 8 August 2026:** removed the unused Huxley premise from the canonical combined-transfer signature, corrected the documentation, and deleted the stale, unreferenced `ScratchTransfer.lean` duplicate.
6. **Completed 8 August 2026:** extended the root import graph to all intended production modules after their compilation repairs.
7. **Completed during reopened #2 and the later root cleanup:** removed every obsolete auxiliary named declaration and standalone development probe. The two retained auxiliary files contain only anonymous examples and both elaborate directly.

**Exit evidence:**

- the audit accurately reports the current noncompliant baseline;
- its audited declaration count matches its explicit list; and
- successful results are distinguished from specifications and conditional theorems.

The audit may initially report failures. It must not suppress them merely to keep the default build green.

The synchronized audit covers every named public theorem in the cleaned tree. The retained auxiliary files contain anonymous examples rather than audit-list declarations.

### Phase 1A: Enforce a warning-free proof run

**Files:**

- `RiemannZeta/GuthMaynard/ZeroCount.lean`
- `RiemannZeta/GuthMaynard/ZeroDetector.lean`
- `RiemannZeta/GuthMaynard/Decoupling.lean`
- `RiemannZeta/GuthMaynard/DirichletPolynomial.lean`
- `RiemannZeta/GuthMaynard/ExponentArithmetic.lean`
- `RiemannZeta/GuthMaynard/ExtractSeparated.lean`
- `RiemannZeta/GuthMaynard/MeanValue.lean`
- `RiemannZeta/GuthMaynard/HalaszMontgomery.lean`
- `RiemannZeta/GuthMaynard/InghamBound.lean`
- `RiemannZeta/GuthMaynard/Pigeonhole.lean`
- `RiemannZeta/GuthMaynard/PolynomialPowers.lean`
- `run_lake_build.bat`

**Required actions:**

1. **Completed 8 August 2026:** eliminated the 31 distinct warning lines recorded in `logs/overall_proof_20260808_045030.log` by correcting their source.
2. **Completed 8 August 2026:** removed unused hypotheses and deleted malformed vacuous declarations rather than disguising them with binder names.
3. **Completed 8 August 2026:** replaced deprecated tactics with supported `push Not` syntax.
4. **Completed 8 August 2026:** removed the admitted coefficient theorem and implemented the actual detector definition rather than disabling proof-integrity diagnostics.
5. **Completed 8 August 2026:** added a runner gate that makes any Lean `warning:` line fail its build/audit stage.
6. **Completed 8 August 2026:** used no linter-disable option, warning filter, or output suppression.
7. **Completed after reopened #2:** deleted `clean_cache.lean`, `build_it.lean`, and all failing auxiliary tests; added separate warning-failing runner stages for `TestExp.lean` and `test_separated.lean`.
8. **Completed after re-audit:** strengthened warning detection to find `warning:` anywhere in Lean output and strengthened Lean-source integrity scans with `--no-ignore`.

**Exit evidence:**

- focused compilation of every affected module emits no Lean warning;
- the principal runner log contains no project `warning:` line; and
- an intentionally introduced warning in a temporary verification fixture is detected by the runner gate before that fixture is removed.

**Current re-audit status:** Phase 1A passes its all-retained-file and zero-warning exit evidence. The runner's overall status remains `FAIL` for mathematical integrity reasons, not warning or coverage defects.

### Phase 2: Repair finite and arithmetic infrastructure

**Files:**

- `RiemannZeta/GuthMaynard/ZeroDetector.lean`
- `RiemannZeta/GuthMaynard/PolynomialPowers.lean`

**Required actions:**

1. **Completed 8 August 2026:** defined the actual truncated Möbius sum and detector coefficients.
2. **Completed 8 August 2026:** proved exact divisor-variable support, cutoff cardinality, exponential-smoothing zero equivalence, a cutoff norm bound uniform in `n`, and `DetectorCoeffBoundProp` with its encoded fixed-`T` constant dependency.
3. **Completed 8 August 2026:** proved `powCoeff_bound_of_uniform_detector_and_factorization` with complete finite-product and convolution-sum arguments from two explicit narrower inputs.
4. **Completed 8 August 2026:** removed `powCoeffBound_unconditional`.
5. **Completed 8 August 2026:** isolated `FactorizationCountBoundProp` with its constant uniform in the positive target `m`, and isolated the stronger `T`-uniform `UniformDetectorCoeffBoundProp` required by the source argument.
6. **Completed 8 August 2026:** removed `k_divisor_function_bound` and exposed the two unproved classical inputs only as explicit parameters of the genuinely conditional coefficient theorem.
7. **Completed after re-audit:** bounded the truncated support by `n.divisors`, proved the Möbius sum and detector coefficient are bounded by `n.divisors.card` uniformly in `T`, and derived `UniformDetectorCoeffBoundProp` from `DivisorCountBoundProp`.
8. **Completed after re-audit:** proved `powCoeff_bound_of_divisor_and_factorization`, exposing the classical divisor-count and factorization-count inputs directly rather than treating the uniform detector bound as independent.
9. **Completed 8 August 2026:** proved the equality between structural power and the explicit `powCoeff` convolution expansion for all `k`, with product support and complex-power multiplicativity proved separately.
10. **Goal C boundary after completed #14 integration:** the transfer now consumes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly; proving those two propositions remains open arithmetic work.

**Exit evidence:**

- no `sorry` or axiom remains in either file;
- the detector is not a constant proxy;
- `#print axioms` for each public theorem is clean of project postulates; and
- powered-polynomial documentation distinguishes definitional identities from coefficient expansions.

The first three exit conditions hold for these two modules. The fourth is a documentation distinction, not completion of the missing expansion theorem; Phase 2 is therefore only partially complete for downstream research purposes.

### Phase 3: Build honest conditional analytic layers

**Files:**

- `RiemannZeta/GuthMaynard/MeanValue.lean`
- `RiemannZeta/GuthMaynard/HalaszMontgomery.lean`
- `RiemannZeta/GuthMaynard/ExtractSeparated.lean`
- `RiemannZeta/GuthMaynard/BetaDependence.lean`

**Required actions:**

1. Remove every project axiom and every `True` placeholder.
2. Retain unproved analytic results as precise proposition specifications, not axiom declarations.
3. When a downstream theorem is conditional, pass each upstream result explicitly in its signature.
4. Ensure the proof performs a real deduction and does not return a definitionally equivalent parameter.
5. Repair standalone compilation of `HalaszMontgomery.lean`.
6. Prove the finite combinatorial and algebraic portions independently of the analytic inputs.
7. Rename the current complement-of-Type-I predicate and count as residual-zero objects; do not identify them definitionally with the source's Type II zeros.
8. State the genuine Type II contour-integral condition from Maynard–Pratt Definition 22 and isolate the twisted fourth-moment estimate used in Lemma 24 as a precise upstream proposition.
9. Prove the residual-to-genuine-Type-II inclusion from an explicit Type-I/Type-II covering input, then derive the count bound from local multiplicity control, Gamma decay, Hölder, separated extraction, and the twisted fourth moment.
10. Keep the generic finite theorem independent of `riemannZeta_finite_zeros_in_rect`; defer its concrete zeta instantiation until the zero-set interface is repaired.
11. Redesign `BetaDependence.lean`: remove the `True` axiom, constrain the contour-shift error, and replace the conclusion-shaped pigeonhole interface with genuinely upstream Fourier/integral estimates.

**Exit evidence:**

- all four modules compile;
- none contains an axiom, `sorry`, or vacuous theorem;
- every conditional theorem exposes its exact assumptions; and
- dependency audits distinguish genuine proofs from statement-only interfaces.

**Current re-audit status:** the mean-value, residual/Type-II semantic, and extraction sublayers made real progress, but this phase fails because `BetaDependence.lean` still contains seven axioms, a `True` placeholder, and malformed interfaces.

### Phase 4: Goal B—the conditional Section 13.1 transfer (completed at the primitive-input boundary)

**File:** `RiemannZeta/GuthMaynard/Transfer.lean`

**Required actions:**

1. Delete `AlgebraicCombinationProp` if it remains equivalent to the target conclusion.
2. Delete `algebraic_combination_unconditional`.
3. State the transfer theorem with the precise large-values, Huxley high-`σ`, Type II, beta-removal, local-zero-count, mean-value, divisor-count, factorization-count, and any provisional conjugation/multiplicity inputs required by the source.
4. Implement the positive-slab bound first, then the conjugation and dyadic reduction to the global `N σ T` count.
5. Implement detector normalization, powered-coefficient phase translation, finite dyadic block decomposition, block-and-ordinate pigeonholing, the complete equation (13.1) choice, and the large-values/mean-value case split.
6. Prove the central `7/10 ≤ σ ≤ 4/5` transfer separately and use the explicit Huxley input for `4/5 ≤ σ ≤ 1`.
7. Demonstrate that no input is equivalent to `GuthMaynardZeroDensity`.
8. Before assembly, repair `GuthMaynardLargeValues` to match the source quantifiers/sign convention, repair the mean-value interval interface, and prove the complete equation (13.1) `k`-selection step. The structural-power/explicit-coefficient expansion is already complete.

**Exit evidence:**

- `conditionalZeroDensityTransfer` is kernel-checked;
- its only nonstandard assumptions are explicit theorem parameters narrower than the conclusion;
- the proof contains the actual downstream Section 13.1 deduction; and
- the paper and progress document permit the Goal B success claim and no stronger claim.

### Phase 5: Discharge classical auxiliary hypotheses—Goal C

This phase is exactly Shitlist #15–#18:

1. **#15:** finish the zeta zero-count foundations, local unit-height bound, and Huxley/Ingham inputs.
2. **#16:** prove the beta-removal theorem after replacing the malformed Fourier/contour interfaces.
3. **#17:** prove the divisor-count, factorization-count, and Montgomery mean-value inputs.
4. **#18:** prove the three Type-II inputs and specialize the completed transfer to a theorem whose only premise is `GuthMaynardLargeValues`.

**Exit evidence:**

- the transfer theorem assumes only the Guth–Maynard large-values theorem;
- every removed hypothesis is replaced by a kernel-checked theorem; and
- Goal C is stated accurately in all documentation.

### Phase 6: Formalize the large-values theorem—Goal D

**Files:**

- `RiemannZeta/GuthMaynard/Decoupling.lean`
- `RiemannZeta/GuthMaynard/LargeValues.lean`
- additional focused modules introduced only when they represent real mathematical responsibilities

**Required actions—Shitlist #19:**

1. **Compilation completed; statement review reopened:** repair the false interval-free incidence proposition and reconcile the two block-index conventions.
2. Replace the incidence and final decoupling axioms with actual proofs only after their corrected statements are source-faithful.
3. Formalize the matrix, singular-value, Fourier, Poisson, affine-transformation, cancellation, and additive-energy arguments required by Guth–Maynard Theorem 1.1.
4. Prove the exact `GuthMaynardLargeValues` statement used by the transfer.
5. Instantiate the Goal C transfer with the proved theorem.

**Exit evidence:**

- `LargeValues.lean` contains a kernel-checked proof rather than a module-level assumed variable;
- the full large-values dependency chain has no project axioms or `sorryAx`;
- the final zero-density result is obtained by theorem application; and
- the Goal D completion claim passes the complete audit.

### Phase 7: Final integration and publication gate

**Files:**

- `RiemannZeta.lean`
- `RiemannZeta/Audit.lean`
- `README.md`
- `Paper_Riemann_Zeta.md`
- `Research Agenda Progress.MD`

**Required actions—final acceptance portion of Shitlist #19:**

1. Import every production module through the root library.
2. Run the full build and standalone checks for any remaining non-root Lean files.
3. Run the repository-wide prohibited-construct scan.
4. Run the explicit axiom audit for every public theorem.
5. Confirm that all builds and the audit emit zero Lean warnings or linter diagnostics from project source.
6. Synchronize all documentation with the exact final result.
7. Ensure ignored directories such as `scratch/` are included in the all-Lean-file inventory rather than relying on `rg`'s default ignore behavior.

**Exit evidence:**

```powershell
rg --no-ignore -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg --no-ignore -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg --no-ignore -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
lake build
```

The prohibited-construct scans return no code matches, the build succeeds without omitted production modules or Lean warnings, the explicit theorem audits contain no project-specific assumptions, and `run_lake_build.bat --no-pause` returns exit code `0` with final status `PASS`.

## Per-Iteration Record

Every completed repair iteration must record:

| Field | Required information |
|---|---|
| Target | Exact file and declaration repaired |
| Mathematical source | Source theorem, section, and any intentional reformulation |
| Previous defect | `sorry`, axiom, toy model, circular assumption, build failure, or audit omission |
| Result | Definition, statement, conditional theorem, or unconditional theorem |
| Dependencies | Mathlib results and explicit theorem parameters |
| Verification | Exact build and `#print axioms` commands and outputs, including the count and text of any remaining Lean warnings |
| Documentation | README, paper, progress, and audit changes |
| Remaining obstruction | Next precise theorem or library gap |

### Completed Iteration: Shitlist #1

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/TestAxiom.lean` |
| Mathematical source | None; this was an isolated negative test, not project mathematics. |
| Previous defect | The file declared `axiom my_unproven_theorem (x : ℝ) : x = x + 1` and used it to prove the false theorem `my_test`. |
| Result | Deleted the file. No replacement theorem was introduced. |
| Dependencies | None. Repository search confirmed that no Lean module imported the file or referenced either declaration. |
| Verification | Confirmed that the path no longer exists and that repository-wide searches find no code references to `TestAxiom`, `my_unproven_theorem`, or `my_test`. The default `lake build` completed successfully; it still reports the pre-existing `powCoeffBound_native` `sorry` warning and other unrelated warnings. A repository scan reports 28 remaining direct project axiom declarations, none associated with the deleted test. |
| Documentation | Marked rank 1 and the corresponding Phase 0 item complete in this agenda. |
| Remaining obstruction | Proceed to Shitlist #2: remove or repair the stale admitted representative-selection experiments. |

### Completed Iteration: Shitlist #2

| Field | Record |
|---|---|
| Target | `ExtractSeparated_scratch.lean`, `Test.lean`, and `test2.lean` through `test6.lean` |
| Mathematical source | Experimental attempts at a representative-selection argument: construct an integer-spaced grid in `[T, 2T]`, control unit-interval occupancy, and sum local zero counts using `zeroCountRect_split`. The canonical project now uses different zero-count and extraction interfaces. |
| Previous defect | All seven files depended on removed declarations such as `ZetaZeroCountModel`, `LocalZeroCountHypothesis`, and `RepresentativeSelectionHypothesis`; collectively they contained thirteen `sorry` proof terms and were outside the default build. |
| Result | Deleted all seven stale Lean experiments. No mathematical theorem was claimed or replaced. The high-level grid, occupancy, and interval-splitting strategy is retained in this record for possible reuse when `ExtractSeparated.lean` is repaired. |
| Dependencies | None. Repository search found no imports of these files and no canonical theorem depending on their declarations. |
| Verification | Confirmed all seven paths are absent and no Lean file references `ExtractSeparated_scratch` or `representative_selection`. The remaining code-level `sorry` scan now finds five terms: one each in the three Shitlist #3 tests and two in `PolynomialPowers.lean`. The default `lake build` completed successfully with the previously documented `powCoeffBound_native` `sorry` warning and unrelated linter warnings. |
| Documentation | Marked rank 2 and its Phase 0 entry complete in this agenda. |
| Remaining obstruction | Proceed to Shitlist #3: repair or remove `TestExp.lean`, `test_separated.lean`, and `test_zeta.lean`. |

### Completed Iteration: Shitlist #3

| Field | Record |
|---|---|
| Target | `TestExp.lean`, `test_separated.lean`, and `test_zeta.lean` |
| Mathematical source | Mathlib's complex-exponential norm simplification and the canonical project theorem `separated_selection`. The Euler-product lower bound remains a later analytic obligation in `ZeroCount.lean`. |
| Previous defect | Each file contained one `sorry`. The separation file duplicated `IsSeparated`, and the zeta file claimed the still-unproved uniform lower bound. |
| Result | Replaced `test_norm_cexp` with a complete `simp`-proved example; replaced the duplicated separation theorem with an example applying canonical `separated_selection`; deleted `test_zeta.lean` without replacing or claiming the Euler-product result. |
| Dependencies | `TestExp.lean` uses Mathlib complex exponential facts. `test_separated.lean` imports `RiemannZeta.GuthMaynard.Separated` and applies its axiom-clean selection theorem. |
| Verification | `lake env lean TestExp.lean` and `lake env lean test_separated.lean` both completed successfully. `#print axioms separated_selection` reports only `propext`, `Classical.choice`, and `Quot.sound`. A code-level scan now finds exactly two remaining `sorry` proof terms, both in `PolynomialPowers.lean`; `test_zeta.lean` is absent. The principal runner logged to `logs/overall_proof_20260808_042042.log`: the default build passed, the known omitted production modules failed, the current audit module executed, and the global result correctly remained `FAIL` because of later Shitlist defects. |
| Documentation | Marked rank 3 and its Phase 0 entry complete in this agenda. |
| Remaining obstruction | Proceed to Shitlist #4: remove or repair `RiemannZeta/GuthMaynard/test_fourier.lean` and `RiemannZeta/GuthMaynard/ZeroCountScratch.lean`. |

### Completed Iteration: Shitlist #4

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/test_fourier.lean` and `RiemannZeta/GuthMaynard/ZeroCountScratch.lean` |
| Mathematical source | The canonical `BetaDependence.lean` already contains the non-toy Fourier-transform definition and its integrand-norm lemma. A future zero-count symmetry theorem must be proved from zeta symmetry and multiplicity preservation rather than introduced as an unused module variable. |
| Previous defect | `test_fourier.lean` defined `fourierTransformΦ` to be the constant `0`, making its test mathematically vacuous. `ZeroCountScratch.lean` introduced an unused module-level parameter asserting the desired zero-count symmetry. Both files were outside the production import graph. |
| Result | Deleted both isolated scratch files. No theorem, assumption, or claimed mathematical result replaced them. |
| Dependencies | None. Repository search confirmed that no canonical Lean module imported either file or used `zeroCountRect_symm`; the only other `fourier_inversion_integrand_bound` is the canonical declaration in `BetaDependence.lean`. |
| Verification | Confirmed both paths are absent, no Lean file references either scratch module or `zeroCountRect_symm`, and no zero-valued `fourierTransformΦ` definition remains. The code-level `sorry` scan still finds only the two terms in `PolynomialPowers.lean`. The principal runner logged to `logs/overall_proof_20260808_042738.log`: the default build passed; omitted production modules, prohibited-proof/axiom gates, and audit-quality gate correctly failed for later Shitlist items; the overall result remained `FAIL`. |
| Documentation | Marked rank 4 and its Phase 0 entry complete in this agenda. |
| Remaining obstruction | Proceed to Shitlist #5: align the unused Huxley premise and documentation in `RiemannZeta/GuthMaynard/InghamBound.lean`. |

### Completed Iteration: Shitlist #5

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/InghamBound.lean`; obsolete duplicate `RiemannZeta/GuthMaynard/ScratchTransfer.lean` |
| Mathematical source | The exponent comparison used by the proof splits at `σ = 7/10`: Ingham supplies the low-σ range and Guth–Maynard supplies the high-σ range. Huxley's estimate is not required for this combined `30(1-σ)/13` implication. |
| Previous defect | `CombinedZeroDensityTransfer` required `HuxleyZeroDensity`, but `combined_zero_density_transfer_native` ignored that premise. The comments incorrectly described a three-bound combination. |
| Result | Removed the Huxley premise from the canonical combined-transfer proposition, updated its proof to accept exactly the two used hypotheses, and rewrote its documentation as a kernel-checked conditional implication. Deleted the unimported `ScratchTransfer.lean`, which redundantly redeclared the transfer framework and had become incompatible with current Mathlib. The standalone canonical `HuxleyZeroDensity` specification remains available but is not presented as a dependency of this theorem. |
| Dependencies | Explicit `InghamZeroDensity` and `GuthMaynardZeroDensity` hypotheses plus the axiom-clean exponent comparison and `EpsilonPowerBound_mono`. |
| Verification | `lake env lean RiemannZeta/GuthMaynard/InghamBound.lean` completed successfully (with only deprecation/style warnings). `#print axioms RiemannZeta.GuthMaynard.combined_zero_density_transfer_native` reports only `propext`, `Classical.choice`, and `Quot.sound`. Repository search confirmed that no code references the deleted scratch module and no documentation still describes the transfer as using three bounds. The principal runner logged to `logs/overall_proof_20260808_043258.log`: the default build and current audit-module execution passed; omitted production modules, the global `sorry`/axiom gates, and the audit-quality gate correctly failed for later Shitlist items; the overall result remained `FAIL`. |
| Documentation | Updated `Research Agenda Progress.MD`, rank 5, and the Phase 1 action in this agenda. |
| Remaining obstruction | Proceed to Shitlist #6: replace `RiemannZeta/Audit.lean` with a genuine dependency audit. |

### Completed Iteration: Shitlist #6

| Field | Record |
|---|---|
| Target | `RiemannZeta/Audit.lean`, with compilation-enabling repairs in `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` required for complete import coverage |
| Previous defect | The audit categorized declarations by spelling and `isTheorem`, omitted production modules, did not inspect transitive dependencies, and always exited successfully despite known project axioms and `sorryAx`. |
| Result | Replaced the categorizer with an explicit list of 110 exported source-level theorems. The audit imports the root plus all three non-root production modules, checks its list against discovered public theorems, detects duplicates and stale entries, computes dependencies with `Lean.collectAxioms`, permits only `propext`, `Classical.choice`, and `Quot.sound`, and exits nonzero on any violation. It currently reports 22 dependency failures rather than concealing them. |
| Supporting repairs | Corrected multiplication grouping and real-power cancellation in `halasz_montgomery_lemma_native`; added the required real/complex power imports and casts in `Decoupling.lean`; converted its unused block-decomposition module parameter into a proposition specification; removed the dangling `LargeValues.lean` variable that merely assumed the target. These changes make all three modules compile but do not discharge their analytic axioms or placeholder obligations. |
| Verification | Direct builds of `HalaszMontgomery`, `Decoupling`, and `LargeValues` succeed with warnings. Direct execution of `RiemannZeta/Audit.lean` finds exactly 110 listed and 110 discovered source-level theorems, then exits `1` after reporting 22 theorems with forbidden transitive dependencies. The principal runner logged to `logs/overall_proof_20260808_044517.log`: the default build, all three formerly omitted production-module builds, unsafe-bypass scan, and audit-quality gate passed; the genuine audit, existing `sorry` scan, and existing project-axiom scan failed; overall exit code `1`. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, rank 6, and the Phase 1 audit actions in this agenda. |
| Remaining obstruction | Proceed to Shitlist #7: add the now-compiling production modules to the default `RiemannZeta` root import graph. |

### Completed Iteration: Shitlist #7

| Field | Record |
|---|---|
| Target | `RiemannZeta.lean`, `RiemannZeta/Audit.lean`, and the production-coverage stage in `run_lake_build.bat` |
| Previous defect | `HalaszMontgomery.lean`, `Decoupling.lean`, and `LargeValues.lean` compiled only through the runner's supplemental stage and were absent from the default library root. The audit redundantly imported them itself instead of proving that the root covered them. |
| Result | Added all three modules to `RiemannZeta.lean`; simplified `Audit.lean` to obtain the entire production environment from the root import; retained the runner's explicit module builds as a redundant coverage check and renamed that stage accurately. |
| Verification | `lake build RiemannZeta` succeeds with warnings and compiles all three newly imported modules. Direct audit execution through the root finds exactly 110 listed and 110 discovered theorems, then correctly exits `1` on the same 22 dependency failures. Repository search confirms all three imports are explicit in `RiemannZeta.lean`. The principal runner logged to `logs/overall_proof_20260808_045030.log`: the default build, redundant explicit production coverage, unsafe-bypass scan, and audit-quality gate passed; the genuine audit, existing `sorry` scan, and existing project-axiom scan failed; overall exit code `1`. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, rank 7, and the Phase 1 root-coverage action in this agenda. |
| Remaining obstruction | Proceed to Shitlist #8: eliminate all Lean warnings and enforce the runner's zero-warning gate. |

### Completed Iteration: Shitlist #8

| Field | Record |
|---|---|
| Target | Eleven warning-producing production modules, `RiemannZeta/Audit.lean`, retained `scratch_pow.lean`, and `run_lake_build.bat` |
| Previous defect | The principal run emitted 31 distinct Lean warning lines. The runner treated warning-producing builds as passes; warning sources included unused hypotheses, deprecated tactics, vacuous `True` lemmas, a constant detector toy, and the admitted `powCoeffBound_native` declaration. |
| Result | Removed unused hypotheses, replaced deprecated tactics, deleted four vacuous `True` declarations and one unused malformed broad–narrow axiom, implemented the actual truncated Möbius divisor sum, and deleted the admitted coefficient theorem plus its unused standalone axiom. Updated the retained polynomial-power scratch file to the faithful `T`-dependent detector interface and removed its unfinished regrouping claim. The exact detector and coefficient bounds remain unproved specifications. The runner now rejects any build/audit stage containing a line beginning `warning:` even if Lean exits `0`. |
| Audit impact | The synchronized public-theorem list changed from 110 to 102 after removing invalid declarations. Direct audit execution reports 102 listed and 102 discovered theorems, with 21 project-axiom dependency failures and no `sorryAx`. Direct project-axiom declarations decreased from 28 to 26. |
| Warning-gate test | A temporary imported `WarningFixture.lean` produced an unused-variable warning while Lean exited `0`; the runner correctly reported `FAIL: 1/3 Default project build emitted Lean warnings despite exit 0` in `logs/overall_proof_20260808_050618.log`. The fixture and import were then removed. |
| Verification | `lake build RiemannZeta` and direct elaboration of `scratch_pow.lean` both succeed with no Lean warnings. The principal runner logged to `logs/overall_proof_20260808_051323.log`: the default build and explicit production coverage passed with zero Lean warnings; the synchronized audit found 102 listed and 102 discovered theorems and correctly failed on 21 project-axiom dependencies; the prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; the project-axiom scan correctly failed on 26 remaining declarations. The complete log contains no line beginning `warning:`. Overall exit code remains honestly `1` because the audit and project-axiom gates are not yet complete. Repository scans found no `sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `unsafe`, or linter-suppression matches in Lean source, and `git diff --check` found no whitespace errors. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, `Analytic Research Agenda.md`, rank 8, and the affected later Shitlist entries. |
| Remaining obstruction | Proceed to Shitlist #9: prove support and magnitude properties for the actual truncated Möbius detector. |

### Completed Iteration: Shitlist #9

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/ZeroDetector.lean` and its synchronized entries in `RiemannZeta/Audit.lean` |
| Previous defect | The truncated Möbius formula was defined, but its exact divisor-variable support, cutoff cardinality, smoothing zero behavior, and `DetectorCoeffBoundProp` magnitude theorem were unproved. |
| Result | Added `detectorCutoff` and `detectorDivisors`; proved exact membership, range support, and cutoff cardinality. Bounded each complex-cast Möbius value by one, bounded the full truncated sum and smoothed coefficient by `detectorCutoff T`, proved that exponential smoothing introduces no new zeros, and proved `detectorCoeff_bound : DetectorCoeffBoundProp`. The proof uses the explicit cutoff and Mathlib's `abs_moebius_le_one`; it introduces no assumption. |
| Constant dependency | The existing proposition orders its quantifiers as `∀ ε, ∀ T, ∃ C, ∀ n`, so the proved constant is uniform in positive `n` for each fixed `T` and may depend on `T`. A stronger constant uniform in `T` is not claimed and is tied to the general divisor-function obligation in Shitlist #10. |
| Audit impact | Added all eight new public theorems to the transitive audit. Direct audit execution finds 110 listed and 110 discovered production theorems; every new detector theorem passes with only permitted Lean/Mathlib logical axioms. The same 21 unrelated project-axiom dependency failures remain. |
| Verification | `lake build RiemannZeta.GuthMaynard.ZeroDetector`, `lake build RiemannZeta`, and direct elaboration of `scratch_pow.lean` all succeed with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_052739.log`: the default build and explicit production coverage passed with zero Lean warnings; the synchronized audit found 110 listed and 110 discovered theorems, passed every new detector theorem, and correctly failed on the same 21 unrelated project-axiom dependencies; the prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; the project-axiom scan correctly failed on 26 remaining declarations. The complete log contains no line beginning `warning:`. Overall exit code remains honestly `1` because the audit and project-axiom gates are not yet complete. Repository scans found no `sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `unsafe`, or linter-suppression matches in Lean source, and `git diff --check` found no whitespace errors. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, rank 9, and the Phase 2 detector action in this agenda. |
| Remaining obstruction | Proceed to Shitlist #10: prove the powered-coefficient estimate from faithful detector/divisor inputs and remove `k_divisor_function_bound`. |

### Completed Iteration: Shitlist #10

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/PolynomialPowers.lean`, its synchronized entries in `RiemannZeta/Audit.lean`, and the polynomial-power documentation. |
| Previous defect | The original coefficient bounds had incorrect constant order and depended on a divisor axiom. After the conditional estimate was repaired, `polynomial_power_identity` still proved only a reflexive structural identity, the explicit `powCoeff` expansion was absent, and `k_divisor_function_bound_one` checked only the irrelevant target `m = 1`. |
| Result | Corrected the coefficient-bound quantifiers and proved `powCoeff_bound_of_uniform_detector_and_factorization` plus `powCoeff_bound_of_divisor_and_factorization` from explicit narrower arithmetic inputs. Added `prod_natCast_cpow_eq` and `powCoeff_product_mem_support`, then replaced the reflexive `polynomial_power_identity` with the exact expansion `powPoly N k s T = ∑ m ∈ Icc (N^k) ((2*N)^k), powCoeff N k m T * m^(-s)`. The proof expands over `Fin k` tuples and regroups finite fibers by product. |
| Integrity change | Deleted the divisor axiom and its wrapper in the original repair, and removed the later boundary-only `k_divisor_function_bound_one` rather than presenting `m = 1` as progress on the general theorem. No replacement axiom, admitted proof, target-equivalent hypothesis, or toy model was introduced. |
| Source fidelity | The coefficient constants are uniform in the source variables, and the structural detector power is now connected to the explicit convolution coefficients used in F-07. The support proof includes `k = 0`; complex-power multiplicativity is justified specifically for natural-number factors. |
| Audit impact | The synchronized audit now contains 129 explicit and 129 discovered production theorems. `prod_natCast_cpow_eq`, `powCoeff_product_mem_support`, and the substantive `polynomial_power_identity` all pass with only permitted Lean/Mathlib logical axioms. The same 6 unrelated forbidden-dependency failures and 14 direct project axioms remain. |
| Verification | The focused `PolynomialPowers` build completed successfully with zero warnings. The principal runner logged to `logs/overall_proof_20260808_115701.log`: stages 1–4 passed warning-free; the transitive audit synchronized 129/129 declarations, passed `prod_natCast_cpow_eq`, `powCoeff_product_mem_support`, and the substantive `polynomial_power_identity`, and failed only on the same 6 unrelated project-axiom dependencies. Integrity scans found no admitted-proof or unsafe-bypass material and correctly reported 14 direct project axioms. The overall exit code remains honestly 1. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, `Analytic Research Agenda.md`, `Polynomial Power Expansion Notes.md`, rank 10, and the Phase 2 actions in this agenda. |
| Remaining obstruction | Shitlist #10 is complete at the honest finite/conditional boundary. Shitlist #14 now uses the completed expansion and bound; `DivisorCountBoundProp` and `FactorizationCountBoundProp` remain unproved Goal C inputs. |

### Completed Iteration: Shitlist #11

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/MeanValue.lean`, the mean-value-dependent theorem in `RiemannZeta/GuthMaynard/HalaszMontgomery.lean`, and their synchronized audit entries |
| Previous defect | `MontgomeryMeanValue` silently fixed the paper's implied constant to one. `montgomery_mean_value_unconditional` postulated that malformed statement, `montgomery_mean_value_native` merely returned the postulate, and `halasz_montgomery_lemma_native` depended on the same hidden module-level assumption. |
| Result | Restated `MontgomeryMeanValue` with one positive absolute constant chosen before `N`, `T`, the separated set, and the coefficients. Removed the project axiom and its wrapper without replacement. Restated the finite large-value cardinality consequence with the same constant and proved `halasz_montgomery_lemma_of_mean_value` from an explicit `MontgomeryMeanValue` parameter by squaring and summing the pointwise lower bounds, applying the supplied estimate, and cancelling the positive threshold. |
| Source and library check | Guth–Maynard Section 13.1 invokes the usual mean-value theorem with `≲`, so an absolute constant is required. A search of the pinned Mathlib source found no matching discrete Dirichlet-polynomial mean-value or large-sieve theorem. The analytic proof therefore remains the explicit `MontgomeryMeanValue` obligation rather than being claimed unconditionally. |
| Audit impact | Deleted the invalid mean-value wrapper from the public theorem set and replaced the Halász–Montgomery audit entry with the conditional theorem. Direct audit execution finds 109 listed and 109 discovered production theorems; `halasz_montgomery_lemma_of_mean_value` passes with only permitted Lean/Mathlib logical axioms. The audit's forbidden-dependency failures decreased from 20 to 18, and direct project-axiom declarations decreased from 25 to 24. |
| Verification | Focused builds of `RiemannZeta.GuthMaynard.MeanValue` and `RiemannZeta.GuthMaynard.HalaszMontgomery`, the full default `lake build`, and direct elaboration of `scratch_pow.lean` succeed with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_094027.log`: the default and explicit production builds passed with zero warnings; the synchronized audit correctly failed on 18 remaining project-axiom dependencies; the prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; and the project-axiom scan correctly failed on 24 remaining declarations. The complete run exited `1`, preserving the repository's honest overall `FAIL` status. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, `Analytic Research Agenda.md`, rank 11, and this Phase 3 record. |
| Remaining obstruction | Proceed to Shitlist #12: repair the Type II boundary and remove `typeII_bound_unconditional` while proving every finite consequence available from explicit inputs. The independent proof of `MontgomeryMeanValue` remains later Goal C work. |

### Pre-Implementation Source Audit: Shitlist #12

| Field | Finding |
|---|---|
| Source theorem | Guth–Maynard Section 13.1 cites Maynard–Pratt, *Half-isolated zeros and zero-density estimates*, Lemma 24 for the estimate `RII(σ,T) ≪ T^(2(1-σ)) (log T)^O(1)`. Maynard–Pratt Definition 22 defines Type II by a large contour integral involving the short Möbius polynomial `M`, `Γ`, and `ζ`; Lemma 23 proves that every relevant zero is Type I or Type II, possibly both. |
| Semantic defect | `ZeroDetector.lean` currently defines `IsTypeIIZero` as membership in the target zero rectangle together with `¬ IsTypeIZero`. This is the residual class needed for a partition identity, not the source's Type II predicate. Consequently `typeI_add_typeII_eq_total` is mathematically a Type-I-plus-residual filtering identity and is misnamed. |
| Incorrect dependency claim | `typeII_bound_of_halasz_montgomery_native` does not use `HalaszMontgomeryLemma`; it merely returns `typeII_bound_unconditional`. The Maynard–Pratt proof of Lemma 24 does not proceed from the discrete mean-value consequence proved in Shitlist #11. |
| Actual proof mechanism | Appendix C converts the contour detector into a lower integral bound, truncates with Gamma decay, takes fourth powers using Hölder, extracts a `(log T)^3`-separated family with local multiplicity control, compares translated local integrals with an integral over `[T/2,3T]`, and applies a twisted fourth-moment bound for `M(1/2+it) ζ(1/2+it)`. The resulting logarithmic loss must then be absorbed into `EpsilonPowerBound`. |
| Required interface repair | Rename the existing complement predicate/count to `IsResidualZero` and `residualZeroCount`; introduce the genuine contour-integral Type II predicate and count; state an explicit Type-I/Type-II covering proposition and an explicit `TwistedZetaFourthMomentProp`; and prove the residual count bound from these strictly upstream inputs rather than accepting `TypeIIBoundProp` itself. |
| Zero-set dependency | The current concrete count unfolds `zerosInRect`, whose construction depends on `riemannZeta_finite_zeros_in_rect`. A theorem concluding the present concrete `TypeIIBoundProp` therefore inherits that project axiom even if `typeII_bound_unconditional` is deleted. The audit-clean core must be parameterized by finite zero data and multiplicities until Shitlist #15 supplies a valid zeta-zero instantiation; the separated multiplicity step also overlaps Shitlist #13's local-zero-count work. |
| Completion threshold | Do not mark #12 complete for deleting the axiom alone. Completion requires removal of `typeII_bound_unconditional` and its wrapper, corrected residual/Type-II semantics, source-faithful analytic interfaces, a kernel-checked finite or asymptotic deduction that uses those inputs, synchronized audits and documentation, and an explicit record of any remaining fourth-moment or zeta-instantiation obligation. |
| Expected immediate audit effect | Deleting only the current axiom and failed wrapper was projected to reduce direct project axioms from 24 to 23 and the existing audit failures from 18 to 17. The completed iteration below confirms both changes while adding five audit-clean public theorems. |

### Completed Iteration: Shitlist #12

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/ZeroDetector.lean`, `ExtractSeparated.lean`, `HalaszMontgomery.lean`, `TypeIIZeros.lean`, `RiemannZeta.lean`, and `RiemannZeta/Audit.lean` |
| Previous defect | The original project called the complement of Type I “Type II,” postulated the complete residual-zero estimate, and falsely attributed the postulate to Halász–Montgomery. The first repair separated those semantics and proved a generic conditional deduction, but its `FiniteTypeICoverProp` demanded coverage for every height and every σ, so the eventual source coverage could not instantiate it; no theorem reached the concrete `ResidualZeroBoundProp`. |
| Semantic repair | Renamed the complement predicate and count to `IsResidualZero` and `residualZeroCount`, and defined the source-facing short Möbius polynomial, Gamma–zeta contour integral, and `IsContourTypeIIZero`. Corrected `FiniteTypeICoverProp` to require coverage eventually in height and only for `7/10 ≤ σ ≤ 4/5`, matching both the source statement and `EpsilonPowerBound`. |
| Conditional proof | Retained the audit-clean generic comparison and exponent composition. Added `finiteTypeICover_of_typeIContourTypeII`, which specializes source coverage to `zerosInRect σ 1 T (2*T)`; proved `weightedResidualCount_dyadicZetaZeros_eq`, including analytic multiplicity; and proved `residualZeroBound_of_contourTypeII_reduction_and_fourthMoment : ResidualZeroBoundProp` from the three explicit analytic inputs. |
| Honest analytic boundary | `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` remain unproved proposition specifications. The reduction records the Appendix C Gamma-decay, Hölder, separated-extraction, and local-multiplicity work. The new concrete theorem composes those inputs; it does not prove Maynard–Pratt Lemma 24. |
| Integrity impact | Deleted the original Type II postulate, misleading wrapper, and conclusion-shaped target input without replacement. The concrete bridge uses Mathlib-backed zeta-zero finiteness and introduces no axiom, admitted proof, hidden target hypothesis, or vacuous theorem. |
| Audit impact | The synchronized audit now contains 132 explicit and 132 discovered production theorems. The three new concrete bridge theorems pass with only `propext`, `Classical.choice`, and `Quot.sound`; the same 6 unrelated forbidden-dependency failures and 14 direct project axioms remain. |
| Verification | The focused `TypeIIZeros` build succeeds with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_121046.log`: stages 1–4 passed warning-free; the transitive audit synchronized 132/132 declarations and passed the corrected generic theorems plus all three concrete bridge theorems. Integrity scans found no admitted-proof or unsafe-bypass material and correctly reported 14 direct project axioms. The same 6 unrelated audit failures remain, so the overall exit code is honestly 1. |
| Remaining obstruction | Shitlist #12 is complete at the honest conditional/concrete boundary. Goal C must prove the source coverage, Appendix C reduction, and twisted fourth moment independently; #12 makes no unconditional claim for Maynard–Pratt Lemma 24. |

### Pre-Implementation Source and Interface Audit: Shitlist #13

| Field | Finding and planned treatment |
|---|---|
| Source chain | Guth–Maynard Section 13.1 first chooses one of `O(log T)` admissible dyadic detector scales, removes dependence on the real part of each Type-I zero by a shift of size `T^o(1)`, uses the classical `O(log T)` local zero-multiplicity bound, and extracts a 1-separated set of large values. The Lean repair must expose these as separate steps rather than postulating their composite conclusion. |
| False combinatorial axiom | `extract_1_separated_subset` claims that every finite real set has a 1-separated subset of at least half its size. This fails for arbitrarily many distinct points contained in an interval of length less than one. Delete it and `vitali_covering_lemma_1D`. Generalize the already kernel-checked `separated_selection` argument to a weighted theorem with a local-occupancy factor `L`, preserving analytic multiplicities. |
| Target quantifier defect | `ExtractSeparatedTarget` currently chooses `C` after `σ` and `T`, so `C` is not a uniform asymptotic constant. Restate the target with `∀ ε > 0, ∃ C > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀` and then choose the scale and separated set. Make the permitted dependence of `C` explicit and place `σ` in the intended compact range. |
| Small-`T` defect | The interval `[T^(1/100), T^(1/2) (log T)^2]` need not contain a dyadic integer for every `T ≥ 2`; the current existential `N` can therefore be impossible. Use a sufficiently-large-`T` threshold and prove nonemptiness/cardinality properties for a finite `admissibleDyadicIndices T`. |
| Interval defect | Beta removal supplies a shifted ordinate `γ'` with `|γ-γ'| ≤ H`, so a source ordinate in `[T,2T]` need not remain in that exact interval. Return the separated set in `[T-H, 2T+H]`, or in an interval of explicitly controlled length, and later split/translate it for the large-values theorem. Do not silently assert membership in `[T,2T]`. |
| Dyadic model | Add `IsAdmissibleDyadicScale`, `admissibleDyadicIndices`, and `IsTypeIZeroAtScale`; prove equivalence with the intended Type-I existential and prove the scale set has `O(log T)` cardinality. Assign each Type-I zero one scale witness, partition the weighted count into exact fibers, and derive the winning scale with finite weighted pigeonholing. This replaces `type_I_zeros_dyadic_sum_bound` and `dyadic_pigeonhole_lemma` without an analytic assumption. |
| Weighted shift and selection | For the winning scale, choose the beta-removal witness for each zero. Define each distinct shifted ordinate's weight as the sum of analytic multiplicities in its fiber and prove preservation of total weight. A shifted unit bin pulls back into an interval of length at most `2H+1`; cover it by finitely many original unit bins, apply the local-multiplicity input, and then apply weighted separated selection. |
| Legitimate analytic inputs | Retain only two strictly upstream proposition inputs: a uniform half-open-unit-interval `LocalZeroMultiplicityBoundProp`, and a pointwise `DetectorBetaShiftProp` giving the displacement and fixed-line detector threshold. The #13 theorem will be conditional on these inputs; their analytic proofs remain later Goal C/#15 and #16 work. |
| Zero-finiteness opportunity | The pinned Mathlib contains `IsCompact.inter_riemannZetaZeros_finite`, proving that a compact set meets the zeta-zero set finitely. Pull this narrow part of #15 forward: prove `ZeroRectangle` compact, derive `riemannZeta_finite_zeros_in_rect` as a theorem, and delete that project axiom before concrete extraction. This availability has been verified but not yet integrated, so current audit counts are unchanged. |
| Jensen route | Mathlib's `AnalyticOnNhd.sum_divisor_le` is a genuine Jensen inequality bounding the zero divisor in a smaller ball from analyticity, a nonzero center, and a boundary bound. It is the intended eventual route to `LocalZeroMultiplicityBoundProp`; #13 must not replace that work with the three current zeta/Jensen axioms. |
| Axiom disposition | Delete `zeta_upper_bound_disk`, `zeta_lower_bound_center`, `jensens_inequality_disk_zero_count`, `type_I_zeros_dyadic_sum_bound`, `dyadic_pigeonhole_lemma`, `vitali_covering_lemma_1D`, `extract_1_separated_subset`, and `extract_separated_lemma`. Replace the analytic portion with proposition inputs and the combinatorial portion with proved theorems. |
| Wrapper cleanup | Remove the misleading or redundant `local_zero_count_native`, `dyadic_pigeonhole_native`, `ExtractSeparatedProp := ExtractSeparatedTarget`, `extractSeparatedBound_native`, the positivity-only extraction helper, and the unrelated root-level `extractSeparated_k_selection` unless a genuine downstream use is identified. Check and remove the unreferenced `Separated_test.lean` duplicate if repository search confirms it has no role. |
| Planned exact theorem | Prove an audit-clean finite theorem that bounds the total Type-I multiplicity by the number of admissible scales times the shifted local-occupancy bound times the cardinality of a separated fixed-line large-value set. Then prove the corrected asymptotic extraction theorem by inserting the scale-count, local-zero, and beta-shift estimates and absorbing logarithmic and `T^δ` losses with a fraction of the requested epsilon. |
| Completion threshold | Mark #13 complete only when all eight current extraction axioms are gone; zero finiteness is derived from Mathlib; weighted selection and dyadic pigeonholing are kernel-checked; the corrected extraction theorem is conditionally proved from the two named analytic inputs; constants, multiplicities, large-`T` bounds, thresholds, and interval enlargement are faithful; audits/documentation are synchronized; and the principal runner remains warning-free while honestly reporting unrelated failures. |

### Completed Implementation Record: Shitlist #13

| Field | Completed result |
|---|---|
| Target | `RiemannZeta/GuthMaynard/ExtractSeparated.lean`, with supporting changes in `Separated.lean`, `ZeroDetector.lean`, `ZeroCount.lean`, and `Audit.lean` |
| Zero-set repair | Proved `isCompact_ZeroRectangle` and derived `riemannZeta_finite_zeros_in_rect` from Mathlib's `IsCompact.inter_riemannZetaZeros_finite`. The concrete finite zeta-zero and multiplicity counts no longer inherit a project finiteness axiom. |
| Dyadic repair | Added `IsAdmissibleDyadicScale`, finite `admissibleDyadicIndices`, exact membership and cardinality lemmas, an `O(log T)` scale-count bound, `IsTypeIZeroAtScale`, and chosen-scale witnesses. Proved exact natural-weight pigeonholing across the scale fibers. |
| Separation repair | Proved `weighted_separated_selection` by the even/odd unit-bin construction, preserving arbitrary natural weights and the necessary local-occupancy factor. Added shifted-multiplicity aggregation and the generic `finite_weighted_extract_separated` theorem. |
| Target repair | Restated `ExtractSeparatedTarget` with uniform `C,T₀` chosen before `σ,T`, the source range `7/10 ≤ σ ≤ 4/5`, an explicit empty-count branch, a finite admissible scale, analytic multiplicities, and the justified interval `[T-T^(ε/4),2T+T^(ε/4)]`. |
| Conditional theorem | Proved `extractSeparated_of_beta_shift_and_local_multiplicity : DetectorBetaShiftProp → LocalZeroMultiplicityBoundProp → ExtractSeparatedTarget`. Neither input contains a separated set or the final Type-I count bound. The proof performs the scale choice, shift aggregation, weighted selection, and loss calculation in Lean. |
| Axiom disposition | Deleted all eight former `ExtractSeparated.lean` axioms and the obsolete positivity/wrapper declarations. Together with the pulled-forward zero-finiteness theorem, direct project axioms decreased from 23 to 14. No replacement axiom, conclusion-shaped hypothesis, vacuous theorem, or linter suppression was introduced. |
| Audit impact | The synchronized audit now contains 123 explicit and 123 discovered production theorems. The previously global unweighted selection theorem was moved into the project namespace and added to the audit; it and every new #13 theorem pass with only `propext`, `Classical.choice`, and `Quot.sound`. Unrelated forbidden-dependency failures decreased from 17 to 6. |
| Verification | Focused builds of `ZeroCount`, `ZeroDetector`, `Separated`, and `ExtractSeparated`, the full default build, `lake env lean test_separated.lean`, and `lake env lean scratch_pow.lean` succeed with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_104536.log`: both build stages passed warning-free; the synchronized audit reported 123/123 declarations and the expected 6 unrelated failures; the prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; and the project-axiom scan correctly found 14 remaining declarations. Overall exit code remains honestly `1`. |
| Honest analytic boundary | `DetectorBetaShiftProp` and `LocalZeroMultiplicityBoundProp` remain unproved proposition specifications. The former belongs to the beta-removal/Fourier work; the latter requires the Jensen/growth/local-zero analysis. Consequently #13 completes the finite and conditional deduction, not those two analytic theorems and not the full Section 13.1 transfer. |

### Critical Re-Audit and Reopened Plan: Shitlist #13

The implementation record above remains accurate history, but the stronger completion language is superseded by this interface audit.

| Field | Current finding and required treatment |
|---|---|
| Current verdict | This historical finite layer was later superseded by the completed normalized #13 wrapper, which is consumed by the completed conditional #14 transfer. Its beta-shift and unit-zero premises remain unproved. |
| Local-input defect | `LocalZeroMultiplicityBoundProp` quantifies over every displacement function and directly returns the exact multiplicity sum in each shifted, scale-filtered unit bin. This packages the pullback and finite interval-covering step that the pre-implementation plan assigned to #13. Replace it with a uniform multiplicity-weighted bound for ordinary unit intervals of zeta zeros. |
| Required local deduction | Prove that a shifted unit bin with displacement at most `H` pulls back into `[z-H,z+1+H]`; cover that interval by at most `2⌈H⌉+3` ordinary unit bins; restrict to the selected Type-I scale; and derive an `O((H+1) log T)` shifted occupancy bound. This finite deduction belongs in `ExtractSeparated.lean`, not in an analytic hypothesis. |
| Beta-removal boundary | `DetectorBetaShiftProp` may remain the explicit input consumed by #13, but it is not a proved analytic result. Its eventual proof must be assembled in #16 from genuine smoothing/Fourier inversion, decay, contour or Mellin shift, truncation, integral averaging, and pigeonhole lemmas. The malformed current `BetaDependence.lean` interfaces are not acceptable evidence for it. |
| Raw extraction target | Separate the displacement exponent from the requested final epsilon. First prove a raw theorem with `H = T^δ`, enlarged interval `[T-H,2T+H]`, and an explicit bound of the form `C T^δ (log T)^2 |W|`. This prevents hidden or wasteful epsilon accounting. |
| Interval bridge | Translate by `T-H`, sending the selected set into `[0,T+2H]`, and prove preservation of separation and cardinality. Also prove the required Dirichlet-polynomial identity under translation by phase-twisting coefficients, together with equality of coefficient norms. Translation of the finite set alone does not preserve the stated polynomial values. For `δ ≤ 1` and sufficiently large `T`, bound the new interval length by `3T`. |
| Loss normalization | Allocate a strict fraction of the requested epsilon to `δ` and prove an eventual estimate such as `(log T)^2 ≤ T^(ε/2)`. The downstream-ready conclusion must have a pure `C T^ε |W|` or `EpsilonPowerBound` loss, rather than `T^ε (log T)^2`. |
| Downstream-ready target | Add a normalized extraction target exposing a nonempty 1-separated translated set, a base interval accepted by the large-values interface, the phase-twisted coefficient sequence, exact preservation of polynomial values, coefficient-norm preservation, and a pure epsilon-power multiplicity estimate. Retain the raw target if it remains useful for auditing intermediate losses. |
| Dependency ownership | The finite shifted-bin covering, translation identities, and epsilon absorption are #13 work. The analytic unit-zero theorem belongs to #15/Goal C. The beta-removal theorem belongs to #16/Goal C. #14 may consume these only through explicit, source-faithful proposition inputs until they are proved. |
| Implementation order | (1) narrow the local-zero input; (2) prove shifted-bin pullback and finite covering; (3) parameterize the raw extraction theorem; (4) prove interval and coefficient translation; (5) absorb logarithmic losses; (6) expose and audit the normalized target; (7) later discharge the #15 and #16 analytic inputs. |
| Revised completion threshold | Mark the **conditional/normalized layer** complete only when steps 1–6 are kernel-checked, audited, documented, and warning-free under `run_lake_build.bat`. Mark the analytic #13 result complete only after the #15 unit-zero and #16 beta-removal inputs are proved. Do not count either proposition specification itself as analytic completion. |

### Completed Reopened Iteration: Shitlist #13

| Field | Completed result |
|---|---|
| Target | `RiemannZeta/GuthMaynard/ExtractSeparated.lean`, `DirichletPolynomial.lean`, `Audit.lean`, and synchronized project documentation. |
| Local interface repair | Restated `LocalZeroMultiplicityBoundProp` as a uniform multiplicity-weighted `O(log T)` estimate for ordinary unshifted unit intervals of `typeIZeroSet`. It no longer quantifies over an arbitrary displacement or assumes a selected detector scale. |
| Shifted covering | Proved `shifted_bin_weight_le_of_unit_bin_weight`. Fiber decomposition converts the shifted-bin multiplicity sum back to original points; floors place those points in an integer interval of exactly `2⌈H⌉+1` unit bins; the input bound is then summed over that finite cover. |
| Raw theorem | Added `RawExtractSeparatedTarget` and proved `rawExtractSeparated_of_beta_shift_and_local_multiplicity`. It exposes the actual displacement exponent `δ`, interval `[T-T^δ,2T+T^δ]`, and loss `C T^δ (log T)^2 |W|` before normalization. |
| Polynomial translation | Added `phaseShiftCoeffs`, `dirichletPoly_translate`, and `norm_phaseShiftCoeffs`. Added detector-line and translated-detector coefficients plus exact detector/Dirichlet-polynomial identities. Translation changes coefficient phases but preserves every coefficient norm. |
| Normalized theorem | Restated `ExtractSeparatedTarget` as a downstream-ready target and proved `extractSeparated_of_beta_shift_and_local_multiplicity`. It chooses `δ = min (ε/4) (1/2)`, translates the set to `[0,3T]`, carries the phase-twisted polynomial values, and uses `Real.log_le_rpow_div` to absorb `T^δ (log T)^2` into a pure `T^ε` loss. |
| Assumption audit | The final theorem depends only on the explicit `DetectorBetaShiftProp` and the narrowed `LocalZeroMultiplicityBoundProp`. Neither contains a separated set, translated output, final Type-I count bound, or epsilon-normalized conclusion. No project axiom was added. |
| Audit impact | At the #13 iteration, eight public theorems were added and all passed. The completed #14 audit supersedes its counts: 194/194 declarations, 4 unrelated dependency failures, and 13 direct project axioms. |
| Verification | Focused `DirichletPolynomial` and `ExtractSeparated` builds and the full default build completed with zero Lean warnings. `run_lake_build.bat --no-pause` logged to `logs/overall_proof_20260808_124518.log`: stages 1–4 passed warning-free, the audit synchronized 140/140 and passed every #13 theorem, integrity scans found no admitted-proof or unsafe-bypass material, and the axiom scan correctly reported 14 existing declarations. The same 6 unrelated audit failures remain, so the overall exit code is honestly 1. |
| Remaining analytic boundary | The conditional/normalized #13 layer is complete. Proving `LocalZeroMultiplicityBoundProp` is #15/Goal C local-zero work; proving `DetectorBetaShiftProp` is #16/Goal C Fourier/contour work. The repository does not yet have an unconditional Type-I extraction theorem. |

### Completed Reopened Iteration: Shitlist #2

| Field | Record |
|---|---|
| Target | All 32 Lean files that lay outside the 28-file production/audit perimeter at the highly critical re-audit. |
| Previous defect | Five auxiliary files failed elaboration; 18 files were zero-byte or comment-only tombstones; several remaining files duplicated canonical theorems or stale APIs; `clean_cache.lean` and `build_it.lean` performed filesystem/process actions through `#eval`; and `scratch_pow.lean` contained a useful but unaudited proof plan. |
| Reference check | Repository-wide import and reference searches found no production import or canonical theorem dependency on any deletion target. `TestExp.lean` and `test_separated.lean` were the only useful theorem-free regression examples. |
| Result | Deleted 30 obsolete auxiliary Lean files: 21 under `RiemannZeta/GuthMaynard`, eight tracked root utilities/tests, and the ignored stale `scratch/Test.lean`. Retained only `TestExp.lean` and `test_separated.lean`. The tree now contains 30 Lean files total and no zero-byte Lean file. |
| Knowledge preservation | Converted the substantive `scratch_pow.lean` idea into `Polynomial Power Expansion Notes.md`, including the intended expansion statement, the distinction from the reflexive structural identity, boundary concerns, and a likely finite-fiber proof route. No theorem is claimed in that note. |
| Verification | Direct `lake env lean TestExp.lean` and `lake env lean test_separated.lean` each exited 0 with no warning or error output. Repository inventory confirms 30 Lean files total, exactly two auxiliaries, and no empty Lean files. Repository-wide scans report zero `sorry`/`admit`/`sorryAx` matches, zero unsafe-bypass matches, and the unchanged 14 direct project axioms. The principal runner logged to `logs/overall_proof_20260808_111318.log`: both production build stages passed warning-free, the audit synchronized 123/123 declarations and reported the same 6 axiom-dependent failures, and overall exit code remained honestly `1`. |
| Audit impact | The synchronized audit remains correctly scoped to 123 named production theorems. The retained auxiliary files contain anonymous `example` declarations only, so the cleaned tree has no named auxiliary theorem omitted from the audit. |
| Documentation | Updated this agenda and `Research Agenda Progress.MD`; preserved the power-expansion research content in its own Markdown note. Historical records remain as chronology, while this record is the current disposition. |
| Remaining obstruction | None for #2. Shitlist #8's runner-coverage follow-up is completed in the next record. |

### Completed Reopened Iteration: Shitlist #8

| Field | Record |
|---|---|
| Target | `run_lake_build.bat`, with status synchronization in README, paper, this agenda, and `Research Agenda Progress.MD`. |
| Previous defect | The runner's warning gate covered production builds and the audit but omitted the two retained Lean examples. Its `findstr /B` check only recognized `warning:` at the start of a line, and its integrity scans respected ignore rules that could hide ordinary ignored Lean files. |
| Result | Expanded the principal evaluation from three to five Lean stages: default production build, explicit production redundancy, `TestExp.lean`, `test_separated.lean`, and `Audit.lean`. Every stage uses the same nonzero-exit and warning-failure logic. Warning detection now finds `warning:` anywhere in stage output, and proof-integrity scans use `rg --no-ignore`. |
| Coverage | The current tree contains 32 Lean files. The root build covers its 29-file production import graph, the audit is executed explicitly, and the two remaining files are executed explicitly as examples. No retained Lean file is outside the human-facing evaluation. |
| Verification | `cmd /c run_lake_build.bat --no-pause` logged to `logs/overall_proof_20260808_112057.log`. Stages 1–4 passed with zero Lean warnings. Stage 5 synchronized 123 explicit and 123 discovered theorems and failed on the same 6 project-axiom dependencies. Integrity scans found no admitted-proof or unsafe-bypass material and correctly failed on 14 direct project axioms. Overall exit code was honestly `1`; the log contains no `warning:` diagnostic. |
| Documentation | Updated runner coverage in `README.md` and `Paper_Riemann_Zeta.md`, corrected the paper's stale expected audit count from 17 to 6, and synchronized both agenda documents. |
| Remaining obstruction | #8 has no remaining warning or retained-file coverage defect. At the current #14 revision, the overall runner cannot pass until later Shitlist items remove the 4 audited dependency failures and all 13 direct project axioms. |

### Completed Reopened Iteration: Shitlist #9

| Field | Record |
|---|---|
| Target | `RiemannZeta/GuthMaynard/ZeroDetector.lean`, `PolynomialPowers.lean`, and their synchronized audit/documentation entries. |
| Previous defect | `detectorCoeff_bound` proved only `∀ ε, ∀ T, ∃ C, ∀ n`; its constant could depend on `T`. The source-facing powered-polynomial step requires `∀ ε, ∃ C, ∀ n, ∀ T`. `UniformDetectorCoeffBoundProp` was merely stated in `PolynomialPowers.lean` and treated as an independent unproved input. |
| Mathlib check | The pinned Mathlib provides the coarse `Nat.card_divisors_le_self` but no epsilon-power theorem for `n.divisors.card`. The classical estimate therefore remains an explicit proposition rather than being claimed from a nonexistent library result. |
| Exact finite proof | Proved `detectorDivisors_subset_divisors`, `norm_mobius_sum_le_divisors_card`, and `norm_detectorCoeff_le_divisors_card`. These results discard the `T`-dependent cutoff in favor of the full positive-divisor set and use the exponential smoothing bound, so their right-hand side is independent of `T`. |
| Source-uniform deduction | Moved `UniformDetectorCoeffBoundProp` to the detector layer, introduced the exact classical `DivisorCountBoundProp`, and proved `uniformDetectorCoeffBound_of_divisorCount`. The theorem chooses its constant before both `n` and `T` and performs a genuine deduction from the divisor-cardinality estimate. |
| Downstream integration | Proved `powCoeff_bound_of_divisor_and_factorization`, which combines the new uniform-detector deduction with the existing finite convolution proof. The powered-coefficient layer now exposes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly. |
| Audit impact | Added five public theorems to the synchronized transitive audit. Direct audit execution reports 128 explicit and 128 discovered theorems; all five additions pass with only permitted Lean/Mathlib logical axioms. The same 6 unrelated dependency failures remain. |
| Verification | Focused builds of `ZeroDetector` and `PolynomialPowers` completed successfully with zero warnings. The principal runner logged to `logs/overall_proof_20260808_113250.log`: stages 1–4 passed warning-free; the audit synchronized 128/128 declarations, passed all five additions, and failed on the same 6 unrelated project-axiom dependencies; integrity scans found no admitted-proof or unsafe-bypass material and correctly reported 14 direct project axioms. Overall exit code remained honestly `1`. |
| Honest boundary | `DivisorCountBoundProp` is a classical theorem specification, not a proved theorem. #9 completes the exact finite bound and source-uniform conditional reduction; proving the epsilon-power divisor estimate remains Goal C/#10 arithmetic work. |

### Source and Interface Audit: Shitlist #14

At the pre-implementation audit, `Transfer.lean` was circular and supplied no part of the Section 13.1 deduction. The implementation results below supersede that baseline.

| F-step | Current status | Required #14 treatment |
|---|---|---|
| F-01 dyadic zero reduction | **Complete.** Zeta conjugation, analytic-order preservation, negative/positive rectangle equality, finite low-height control, and the eventual dyadic reduction are proved. | Implemented in `ZeroCount.lean` and `DyadicTransfer.lean`; no provisional parameter remains. |
| F-02 detector coefficients | **Complete conditionally.** The truncated Möbius detector, admissible scales, and source-uniform conditional coefficient bound are consumed by the central proof. | `DivisorCountBoundProp` remains an explicit primitive arithmetic input. |
| F-03 Type I/Type II | **Complete conditionally.** The exact partition is assembled and the residual bound is derived internally. | The three source-facing Type-II propositions remain explicit primitive analytic inputs. |
| F-04 beta removal | **Explicit conditional boundary only.** `DetectorBetaShiftProp` is source-facing but unproved. | Accept it explicitly for Goal B and keep its proof assigned to #16. Do not use the malformed conclusion-shaped declarations in `BetaDependence.lean`. |
| F-05 separated extraction | **Complete conditionally.** #13's normalized extraction is invoked from the beta-shift and ordinary unit-zero inputs. | Those two primitive inputs remain unproved. |
| F-06 normalize coefficients | **Complete.** Exact identities, restricted globally unit-bounded coefficients, threshold inversion, and uniform coefficient constants are integrated. | No #14 work remains. |
| F-07 polynomial powers | **Complete.** The block split and simultaneous pigeonhole feed the central proof, with all bounded losses absorbed. | No #14 work remains. |
| F-08 choose `k` | **Complete.** Both sides of equation (13.1), `2 ≤ k ≤ 101`, and detector-scale control are consumed. | No #14 work remains. |
| F-09 large-values case | **Complete conditionally.** The normalized fixed block is passed to the repaired large-values input and every loss is absorbed. | `GuthMaynardLargeValues` remains an explicit primitive analytic input. |
| F-10 mean-value case | **Complete conditionally.** The normalized-block mean-value case and its exponent comparison are assembled. | `MontgomeryMeanValue` remains an explicit primitive analytic input. |

#### Implemented order

1. Repair `GuthMaynardLargeValues`: positive constant, eventual threshold, source sign convention, `V > 0`, and a proved `n^{it}`/`n^{-it}` bridge.
2. Repair the mean-value interval interface and prove translation by coefficient phase twisting.
3. Replace `k_selection` with the complete, uniformly bounded equation (13.1) theorem, including absorption of the detector scale's `(log T)^2` upper loss.
4. Complete F-06 and F-07: exact `N^σ` normalization, powered phase identity, dyadic block split, coefficient normalization, and block/ordinate pigeonholing.
5. Prove F-09 and F-10 as independent case theorems with separately audited exponent lemmas.
6. Assemble a central positive-slab theorem for `7/10 ≤ σ ≤ 4/5` from `GuthMaynardLargeValues`, `MontgomeryMeanValue`, `ResidualZeroBoundProp`, `ExtractSeparatedTarget`, and `PowCoeffBoundProp`.
7. Prove F-01 and extend the slab theorem to the global `N σ T` convention, then use an explicit `HuxleyZeroDensity` input for `4/5 ≤ σ ≤ 1`.
8. Expose a public primitive-input `conditionalZeroDensityTransfer` that derives the #10, #12, and #13 intermediate propositions internally. Only after it elaborates, delete `AlgebraicCombinationProp`, `algebraic_combination_unconditional`, `algebraic_combination_native`, and the unused `h_bound : True`.
9. Add every new public theorem to `Audit.lean`, synchronize the paper, README, both agendas, and run the principal warning-failing evaluation.

#### Implemented public dependency boundary

The final theorem takes individually named `GuthMaynardLargeValues`, `MontgomeryMeanValue`, beta shift, ordinary unit-zero multiplicity, divisor-count, factorization-count, Type-I/contour-Type-II coverage, Type-II fourth-moment reduction, twisted fourth moment, and `HuxleyZeroDensity` hypotheses. It takes no conjugation/multiplicity parameter, `GuthMaynardZeroDensity`, `AlgebraicCombinationProp`, slab-bound premise, or dyadic-to-global premise.

The Huxley input belongs specifically to constructing the full-range `GuthMaynardZeroDensity` conclusion from the central Section 13.1 argument. It is not reintroduced into the already-correct F-12 combined-exponent theorem, which legitimately assumes that full-range Guth–Maynard result and then combines it only with Ingham.

#### Completion gate

Shitlist #14 is complete only when the real F-01 through F-10 deduction is kernel-checked; `conditionalZeroDensityTransfer` has only explicit narrower parameters and permitted Lean/Mathlib logical axioms; the circular axiom and every `True` artifact are absent; all changed modules and the synchronized audit emit zero warnings; and `run_lake_build.bat` reports the remaining repository failures honestly. Goal B must still be described as conditional until its analytic parameters are discharged.

### Shitlist #14 Implementation Audit — 8 August 2026

| Item | Verified result |
|---|---|
| Circularity | Deleted `AlgebraicCombinationProp`, `algebraic_combination_unconditional`, `algebraic_combination_native`, and `h_bound : True`. Lean-source search no longer finds those declarations. |
| Source interfaces | Repaired `GuthMaynardLargeValues`, proved its sign bridge, and changed the mean-value/Halász–Montgomery interval to `[0,T]`. |
| F-01 | Proved zeta conjugation away from the pole, preservation of iterated derivatives and analytic vanishing order, symmetry of multiplicity-weighted rectangle counts, finite low-height control, and the generic positive-slab-to-global dyadic theorem. |
| F-06/F-07 | Added lower-endpoint vanishing, exact wide-support decomposition, powered fixed-line and translation identities, normalized coefficient bounds, pointwise powered lower bounds, simultaneous fixed-block/ordinate-subset pigeonholing, globally restricted block coefficients, and uniform bounded-`k` loss control. |
| F-08 | Added the full bounded equation-(13.1) theorem and eventual detector upper-scale estimate. |
| F-09/F-10 | Proved and applied every displayed power-term comparison, including equation (13.2), normalized threshold inversion, fixed-block length comparison, and uniform epsilon-loss absorption. |
| Downstream transfer | `typeIPositiveSlabBound_of_section13_inputs` derives the Type-I slab from four source inputs. `conditionalZeroDensityTransfer` derives that theorem, the residual theorem, extraction, powered coefficients, dyadic reduction, and Huxley branch from ten named primitive inputs. |
| Audit | The synchronized audit discovers and explicitly checks 194 public theorems. All 21 newly registered #14 declarations pass. The audit still fails on four pre-existing project-axiom-dependent declarations in `ZeroCount.lean`, `BetaDependence.lean`, and `Decoupling.lean`. |
| Principal evaluation | `run_lake_build.bat --no-pause` logged the concluding run to `logs/overall_proof_20260808_154845.log`. Stages 1–4 passed with zero warnings; stage 5 synchronized 194/194 declarations and failed on exactly four pre-existing dependencies. The integrity gate correctly found 13 direct project axioms, so the overall exit code remains honestly `1`. |
| Honest remaining boundary | #14 is **complete conditionally, not unconditionally**. Its ten primitive inputs remain research obligations. `TypeIPositiveSlabBoundProp` is now a derived internal intermediate, and `DyadicToGlobalZeroCountProp` has been deleted. |

### Re-Audit Correction to Historical Completion Records

The iteration records above remain useful accounts of what each repair changed at that time, but their words “deleted,” “complete,” and “every” must be read subject to the highly critical re-audit near the top of this file. In particular:

- #2's initially incomplete deletion claim has now been repaired: every obsolete/tombstone path is absent and both retained examples elaborate cleanly;
- #6's synchronized transitive audit now covers every named public theorem in the cleaned tree; the two auxiliary declarations are anonymous examples;
- #8's initially production-only warning gate now covers both retained examples and uses ignore-resistant integrity scans;
- #9 now derives the source-uniform detector estimate from the explicit classical `DivisorCountBoundProp`; that classical estimate itself remains open;
- #10 now proves the structural-power/explicit-coefficient identity and exposes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly, but does not prove those classical growth inputs;
- #12 now reaches the concrete `ResidualZeroBoundProp` from honest source-facing inputs; those hard analytic inputs remain open. #13 now completes the conditional/normalized extraction layer from a narrow unshifted unit-zero input and `DetectorBetaShiftProp`; proving those two analytic inputs remains #15/#16 work.
- #14 removes the circular conclusion-equivalent assumption and completes the primitive-input conditional transfer; its ten source-facing hypotheses remain later research obligations.

These corrections do not invalidate the kernel-checked lemmas. They narrow the completion claims to exactly what those lemmas establish.

## Current Priority

The #15–#19 internal proof contract is satisfied. Shitlist #20 is now the active external-digestion layer: #20a is complete internally, while expert exposition review, independent semantic review, any separately authorized preprint/peer-review process, and canonicalization remain open. These gates cannot be closed by another runner PASS or by project-internal prose alone.
