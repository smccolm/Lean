# Lean Alignment Fix Agenda

**Established:** 8 August 2026  
**Authority:** `AGENTS.md`, `Guth_Maynard_Formalization_Research_Agenda.docx`, and `Research Agenda Progress.MD`  
**Scope:** Every Lean file in the repository, including canonical modules, tests, scratch files, and build/audit entry points

## Purpose

Bring the Lean source into compliance with the repository's proof-integrity rules and restore a defensible path toward the Guth–Maynard zero-density formalization.

This agenda distinguishes:

- **integrity alignment:** removing `sorry`, project axioms, hidden target assumptions, toy definitions, vacuous placeholders, excluded failing modules, and misleading proof claims; and
- **research completion:** proving the conditional Section 13.1 transfer, discharging its classical analytic inputs, and ultimately proving the Guth–Maynard large-values theorem.

Deleting or downgrading an invalid theorem may restore integrity, but it does not count as proving the intended mathematics. Each such change must be recorded accurately.

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

These are defects to eliminate, not accepted project conventions.

## Files Ordered by Estimated Repair Difficulty

This ordering estimates the difficulty of producing a genuine, mathematically faithful replacement. It does not treat deletion of a canonical theorem as completion of the intended research objective.

| Rank | File or group | Required repair | Estimated difficulty |
|---:|---|---|---|
| 1 | ~~`RiemannZeta/GuthMaynard/TestAxiom.lean`~~ | **Completed 8 August 2026:** deleted the isolated file containing the deliberately false axiom and its dependent theorem. | Trivial—complete |
| 2 | ~~`ExtractSeparated_scratch.lean`, `Test.lean`, `test2.lean`–`test6.lean`~~ | **Completed 8 August 2026:** deleted seven unreferenced, admitted experiments written against the removed zero-count-model API. | Trivial–easy—complete |
| 3 | ~~`TestExp.lean`, `test_separated.lean`, `test_zeta.lean`~~ | **Completed 8 August 2026:** converted the exponential and separation checks into complete examples and deleted the unproved Euler-product experiment. | Easy—complete |
| 4 | ~~`RiemannZeta/GuthMaynard/test_fourier.lean`, `RiemannZeta/GuthMaynard/ZeroCountScratch.lean`~~ | **Completed 8 August 2026:** deleted the isolated zero-valued Fourier toy and unused module-level symmetry assumption. | Easy—complete |
| 5 | ~~`RiemannZeta/GuthMaynard/InghamBound.lean`~~ | **Completed 8 August 2026:** removed the unused Huxley premise so the statement matches the two-bound proof; deleted the stale, unreferenced `ScratchTransfer.lean` duplicate. | Easy—complete |
| 6 | ~~`RiemannZeta/Audit.lean`~~ | **Completed 8 August 2026:** replaced name-based categorization with a synchronized 110-theorem list and transitive dependency checks across every production module. | Easy–moderate—complete |
| 7 | `RiemannZeta.lean` | Import the three now-compiling production modules into the default root graph. | Easy |
| 8 | `RiemannZeta/GuthMaynard/ZeroDetector.lean` | Implement the actual truncated Möbius coefficients and prove their support and magnitude properties. | Moderate |
| 9 | `RiemannZeta/GuthMaynard/PolynomialPowers.lean` | Remove two `sorry`s and two axioms; prove the finite-product algebra and address the general k-divisor bound faithfully. | Moderate–hard |
| 10 | `RiemannZeta/GuthMaynard/MeanValue.lean` | Remove the Montgomery mean-value axiom and either prove the theorem or expose it only as a legitimate explicit upstream parameter. | Hard |
| 11 | `RiemannZeta/GuthMaynard/HalaszMontgomery.lean` | **Compilation repaired during #6.** Still prove the large-value consequence from an explicit mean-value input, replace the `True` dyadic lemma, and remove the Type II axiom. | Hard |
| 12 | `RiemannZeta/GuthMaynard/ExtractSeparated.lean` | Replace the Jensen `True` placeholder and eight axioms with genuine combinatorial extraction and explicit, narrower analytic inputs. | Hard–very hard |
| 13 | `RiemannZeta/GuthMaynard/Transfer.lean` | Remove the assumed conclusion and implement F-01 through F-10 from separately named upstream hypotheses. | Very hard |
| 14 | `RiemannZeta/GuthMaynard/ZeroCount.lean` | Prove or faithfully refactor zero finiteness with multiplicity, growth bounds, Phragmén–Lindelöf, and the Euler-product lower bound. | Very hard |
| 15 | `RiemannZeta/GuthMaynard/BetaDependence.lean` | Replace seven axioms with genuine Schwartz/Fourier inversion, decay, contour-shift, truncation, and pigeonhole arguments. | Very hard |
| 16 | `RiemannZeta/GuthMaynard/Decoupling.lean` | **Compilation repaired during #6.** Still replace the `True` block decomposition and formalize the broad–narrow and incidence bounds without axioms. | Extreme |
| 17 | `RiemannZeta/GuthMaynard/LargeValues.lean` | **Module-level target assumption removed during #6.** Still assemble and prove the full Guth–Maynard large-values theorem. | Hardest; long-term Goal D |

## Dependency-Aware Execution Plan

### Phase 0: Remove noncanonical violations

**Files:**

- [x] `RiemannZeta/GuthMaynard/TestAxiom.lean` — deleted 8 August 2026 after confirming that no module imported or referenced its declarations
- [x] `ExtractSeparated_scratch.lean`, `Test.lean`, and `test2.lean` through `test6.lean` — deleted 8 August 2026 after confirming that they were unreferenced, admitted experiments against stale APIs
- [x] `TestExp.lean` and `test_separated.lean` — converted to complete examples on 8 August 2026; `test_zeta.lean` — deleted rather than retaining an admitted Euler-product theorem
- [x] `RiemannZeta/GuthMaynard/test_fourier.lean` and `RiemannZeta/GuthMaynard/ZeroCountScratch.lean` — deleted 8 August 2026 after confirming that canonical code did not import or use them

**Required actions:**

1. Delete obsolete experiments that duplicate canonical work or depend on removed APIs.
2. Preserve useful counterexamples or proof attempts as Markdown notes when appropriate.
3. Convert retained tests into compiling examples with complete proofs.
4. Scan all remaining Lean files for prohibited constructs.

**Exit evidence:**

- no scratch or test file contains `sorry`, `admit`, `axiom`, a toy mathematical definition, or a hidden module-level assumption;
- every retained test compiles; and
- removed files and any preserved knowledge are documented.

### Phase 1: Establish trustworthy verification infrastructure

**Files:**

- `RiemannZeta/Audit.lean`
- `RiemannZeta.lean`
- `RiemannZeta/GuthMaynard/InghamBound.lean`

**Required actions:**

1. **Completed 8 August 2026:** created an explicit, synchronization-checked list of all 110 exported source-level theorems.
2. **Completed 8 August 2026:** imported every intended production module into the audit after making the three previously omitted modules compilable.
3. **Completed 8 August 2026:** replaced name-based classification with transitive `Lean.collectAxioms` inspection.
4. **Completed 8 August 2026:** the audit exits nonzero and identifies every audited theorem with a `sorryAx` or project-specific axiom dependency.
5. **Completed 8 August 2026:** removed the unused Huxley premise from the canonical combined-transfer signature, corrected the documentation, and deleted the stale, unreferenced `ScratchTransfer.lean` duplicate.
6. Extend the root import graph only as repaired modules become compilable.

**Exit evidence:**

- the audit accurately reports the current noncompliant baseline;
- its audited declaration count matches its explicit list; and
- successful results are distinguished from specifications and conditional theorems.

The audit may initially report failures. It must not suppress them merely to keep the default build green.

### Phase 2: Repair finite and arithmetic infrastructure

**Files:**

- `RiemannZeta/GuthMaynard/ZeroDetector.lean`
- `RiemannZeta/GuthMaynard/PolynomialPowers.lean`

**Required actions:**

1. Define the actual truncated Möbius sum and detector coefficients.
2. Prove exact support and smoothing properties.
3. Prove the two finite-product steps currently replaced by `sorry`.
4. Remove `powCoeffBound_unconditional`.
5. Isolate the precise general divisor-function statement required by the coefficient bound.
6. Prove it or expose it only as an explicit, source-faithful parameter of a genuinely conditional coefficient theorem.

**Exit evidence:**

- no `sorry` or axiom remains in either file;
- the detector is not a constant proxy;
- `#print axioms` for each public theorem is clean of project postulates; and
- powered-polynomial documentation distinguishes definitional identities from coefficient expansions.

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

**Exit evidence:**

- all four modules compile;
- none contains an axiom, `sorry`, or vacuous theorem;
- every conditional theorem exposes its exact assumptions; and
- dependency audits distinguish genuine proofs from statement-only interfaces.

### Phase 4: Complete Goal B—the conditional Section 13.1 transfer

**File:** `RiemannZeta/GuthMaynard/Transfer.lean`

**Required actions:**

1. Delete `AlgebraicCombinationProp` if it remains equivalent to the target conclusion.
2. Delete `algebraic_combination_unconditional`.
3. State the transfer theorem with the precise large-values, Type II, local-zero-count, mean-value, and other legitimate classical inputs required by the source.
4. Implement dyadic reduction, detector classification, beta removal, separated extraction, normalization, powering, the case split, and exponent arithmetic.
5. Demonstrate that no input is equivalent to `GuthMaynardZeroDensity`.

**Exit evidence:**

- `conditionalZeroDensityTransfer` is kernel-checked;
- its only nonstandard assumptions are explicit theorem parameters narrower than the conclusion;
- the proof contains the actual downstream Section 13.1 deduction; and
- the paper and progress document permit the Goal B success claim and no stronger claim.

### Phase 5: Discharge classical auxiliary hypotheses—Goal C

**Files:**

- `RiemannZeta/GuthMaynard/ZeroCount.lean`
- `RiemannZeta/GuthMaynard/MeanValue.lean`
- `RiemannZeta/GuthMaynard/HalaszMontgomery.lean`
- `RiemannZeta/GuthMaynard/BetaDependence.lean`
- `RiemannZeta/GuthMaynard/ExtractSeparated.lean`

**Required actions:**

1. Construct and prove finite zeta-zero counts in compact rectangles with analytic multiplicity.
2. Prove the unit-height local zero-count estimate.
3. Prove the required Montgomery mean-value theorem.
4. Derive the Type II bound.
5. Complete the Fourier smoothing and contour-shift infrastructure.
6. Re-run the transfer audit after removing each explicit hypothesis.

**Exit evidence:**

- the transfer theorem assumes only the Guth–Maynard large-values theorem;
- every removed hypothesis is replaced by a kernel-checked theorem; and
- Goal C is stated accurately in all documentation.

### Phase 6: Formalize the large-values theorem—Goal D

**Files:**

- `RiemannZeta/GuthMaynard/Decoupling.lean`
- `RiemannZeta/GuthMaynard/LargeValues.lean`
- additional focused modules introduced only when they represent real mathematical responsibilities

**Required actions:**

1. Repair all current compilation errors in `Decoupling.lean`.
2. Replace broad–narrow, incidence, and final decoupling axioms with actual proofs.
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

**Required actions:**

1. Import every production module through the root library.
2. Run the full build and standalone checks for any remaining non-root Lean files.
3. Run the repository-wide prohibited-construct scan.
4. Run the explicit axiom audit for every public theorem.
5. Synchronize all documentation with the exact final result.

**Exit evidence:**

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
lake build
```

The prohibited-construct scans return no code matches, the build succeeds without omitted production modules, and the explicit theorem audits contain no project-specific assumptions.

## Per-Iteration Record

Every completed repair iteration must record:

| Field | Required information |
|---|---|
| Target | Exact file and declaration repaired |
| Mathematical source | Source theorem, section, and any intentional reformulation |
| Previous defect | `sorry`, axiom, toy model, circular assumption, build failure, or audit omission |
| Result | Definition, statement, conditional theorem, or unconditional theorem |
| Dependencies | Mathlib results and explicit theorem parameters |
| Verification | Exact build and `#print axioms` commands and outputs |
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

## Current Priority

The next infrastructure step is Shitlist #7: extend the default root import graph to the now-compiling production modules. The trustworthy audit will continue to fail until the separately ranked proof defects are removed.

The first major research milestone remains a kernel-checked conditional Section 13.1 transfer from explicit, individually named hypotheses. The final large-values theorem remains the hardest long-term objective.
