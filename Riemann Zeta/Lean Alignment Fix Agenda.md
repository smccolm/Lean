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
| 7 | ~~`RiemannZeta.lean`~~ | **Completed 8 August 2026:** imported `HalaszMontgomery`, `Decoupling`, and `LargeValues` into the default root graph and bound the audit to that graph. | Easy—complete |
| 8 | ~~Warning-producing production files and `run_lake_build.bat`~~ | **Completed 8 August 2026:** eliminated all 31 warning lines at their sources and made every runner build/audit stage fail on any future Lean warning. | Easy–moderate—complete |
| 9 | ~~`RiemannZeta/GuthMaynard/ZeroDetector.lean`~~ | **Completed 8 August 2026:** proved exact divisor-variable support, smoothing zero equivalence, the cutoff magnitude bound, and the encoded fixed-`T` epsilon-power property. | Moderate—complete |
| 10 | ~~`RiemannZeta/GuthMaynard/PolynomialPowers.lean`~~ | **Completed 8 August 2026:** corrected constant dependencies, proved the powered-coefficient theorem from two explicit uniform arithmetic inputs, and removed the general divisor axiom. | Moderate–hard—complete |
| 11 | ~~`RiemannZeta/GuthMaynard/MeanValue.lean`~~ | **Completed 8 August 2026:** removed the Montgomery mean-value axiom and exact-constant wrapper, corrected the statement to one absolute implied constant, and proved the finite large-value count from that explicit input. | Hard—integrity alignment complete; analytic theorem remains open |
| 12 | ~~`RiemannZeta/GuthMaynard/HalaszMontgomery.lean`, `ZeroDetector.lean`, and `TypeIIZeros.lean`~~ | **Completed 8 August 2026:** separated residual zeros from the source's contour-integral Type II condition, removed the Type II axiom and false Halász–Montgomery wrapper, and proved the generic residual bound from explicit coverage, Type II reduction, and twisted-fourth-moment inputs. | Very hard—integrity/source alignment complete; three analytic inputs and concrete zeta instantiation remain open |
| 13 | `RiemannZeta/GuthMaynard/ExtractSeparated.lean`, with supporting changes in `Separated.lean`, `ZeroDetector.lean`, and `ZeroCount.lean` | **Source/interface audit completed 8 August 2026:** the unweighted half-size extraction axiom is false, the final target has nonuniform constant order and an invalid exact interval after beta shifting, and its small-`T` scale claim can be impossible. Replace all eight axioms with weighted finite selection, exact dyadic pigeonholing, corrected asymptotic quantifiers, and a conditional theorem from explicit local-multiplicity and beta-shift inputs. | Hard–very hard; combinatorial core is tractable, analytic inputs remain Goal C work |
| 14 | `RiemannZeta/GuthMaynard/Transfer.lean` | Remove the assumed conclusion and implement F-01 through F-10 from separately named upstream hypotheses. | Very hard |
| 15 | `RiemannZeta/GuthMaynard/ZeroCount.lean` | Prove or faithfully refactor zero finiteness with multiplicity, growth bounds, Phragmén–Lindelöf, and the Euler-product lower bound. | Very hard |
| 16 | `RiemannZeta/GuthMaynard/BetaDependence.lean` | Replace seven axioms with genuine Schwartz/Fourier inversion, decay, contour-shift, truncation, and pigeonhole arguments. | Very hard |
| 17 | `RiemannZeta/GuthMaynard/Decoupling.lean` | **Compilation repaired during #6; vacuous recursive lemma and unused broad–narrow axiom removed during #8.** Still prove the stated block decomposition and formalize incidence and decoupling without axioms. | Extreme |
| 18 | `RiemannZeta/GuthMaynard/LargeValues.lean` | **Module-level target assumption removed during #6.** Still assemble and prove the full Guth–Maynard large-values theorem. | Hardest; long-term Goal D |

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
6. **Completed 8 August 2026:** extended the root import graph to all intended production modules after their compilation repairs.

**Exit evidence:**

- the audit accurately reports the current noncompliant baseline;
- its audited declaration count matches its explicit list; and
- successful results are distinguished from specifications and conditional theorems.

The audit may initially report failures. It must not suppress them merely to keep the default build green.

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

**Exit evidence:**

- focused compilation of every affected module emits no Lean warning;
- the principal runner log contains no project `warning:` line; and
- an intentionally introduced warning in a temporary verification fixture is detected by the runner gate before that fixture is removed.

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
7. Rename the current complement-of-Type-I predicate and count as residual-zero objects; do not identify them definitionally with the source's Type II zeros.
8. State the genuine Type II contour-integral condition from Maynard–Pratt Definition 22 and isolate the twisted fourth-moment estimate used in Lemma 24 as a precise upstream proposition.
9. Prove the residual-to-genuine-Type-II inclusion from an explicit Type-I/Type-II covering input, then derive the count bound from local multiplicity control, Gamma decay, Hölder, separated extraction, and the twisted fourth moment.
10. Keep the generic finite theorem independent of `riemannZeta_finite_zeros_in_rect`; defer its concrete zeta instantiation until the zero-set interface is repaired.

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
5. Confirm that all builds and the audit emit zero Lean warnings or linter diagnostics from project source.
6. Synchronize all documentation with the exact final result.

**Exit evidence:**

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
lake build
```

The prohibited-construct scans return no code matches, the build succeeds without omitted production modules or Lean warnings, and the explicit theorem audits contain no project-specific assumptions.

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
| Target | `RiemannZeta/GuthMaynard/PolynomialPowers.lean`, its synchronized entry in `RiemannZeta/Audit.lean`, and the unreferenced duplicate `TestPiFinset.lean` |
| Previous defect | `k_divisor_function_bound` was a project axiom; `divisor_bound_native` merely wrapped it. Both `FactorizationCountBoundProp` and `PowCoeffBoundProp` chose their constants after the coefficient target, so their bounds did not encode the uniformity used in Section 13.1. No theorem derived the powered coefficient estimate from narrower arithmetic inputs. |
| Result | Corrected `FactorizationCountBoundProp` so its constant depends on `k` and epsilon but is uniform in positive `m`. Added `UniformDetectorCoeffBoundProp` with a constant uniform in `n` and `T`. Corrected `PowCoeffBoundProp` so its constant is uniform in `N`, positive `m`, and `T`. Proved `powCoeff_bound_of_uniform_detector_and_factorization` by splitting epsilon in half, multiplying the per-factor detector bounds, rewriting the product of real powers using `∏ p_i = m`, bounding the convolution sum termwise, and applying the uniform factorization count. |
| Integrity change | Deleted `k_divisor_function_bound` and its wrapper `divisor_bound_native`; introduced no replacement axiom. Deleted the unreferenced root-level `TestPiFinset.lean`, which duplicated the canonical `m = 1` lemma with an unused hypothesis. The two remaining classical arithmetic obligations are proposition specifications passed explicitly to the conditional theorem, not asserted facts. |
| Source fidelity | Guth–Maynard Section 13.1 applies the large-values and mean-value estimates to a bounded power of the normalized detector polynomial. The corrected constant order and the two uniform arithmetic inputs represent the coefficient-growth requirement without allowing a new constant for each coefficient. The separate equality between structural `powPoly` and the explicit coefficient expansion remains future F-07 work. |
| Audit impact | Replaced `divisor_bound_native` in the synchronized audit with the new conditional theorem. Direct audit execution finds 110 listed and 110 discovered production theorems; the new theorem passes with only permitted Lean/Mathlib logical axioms. Removing the divisor axiom reduces the unrelated forbidden-dependency failures from 21 to 20 and the direct project-axiom declarations from 26 to 25. |
| Verification | `lake build RiemannZeta.GuthMaynard.PolynomialPowers`, `lake build RiemannZeta`, and direct elaboration of `scratch_pow.lean` all succeed with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_055216.log`: the default build and explicit production coverage passed with zero Lean warnings; the synchronized audit found 110 listed and 110 discovered theorems, passed the new conditional coefficient theorem, and correctly failed on 20 remaining project-axiom dependencies; the prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; the project-axiom scan correctly failed on 25 remaining declarations. The complete log contains no line beginning `warning:`. Overall exit code remains honestly `1` because the audit and project-axiom gates are not yet complete. Repository scans found no `sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, `unsafe`, or linter-suppression matches in Lean source, and `git diff --check` found no whitespace errors. |
| Documentation | Updated `README.md`, `Paper_Riemann_Zeta.md`, `Research Agenda Progress.MD`, `Analytic Research Agenda.md`, rank 10, and every Phase 2 arithmetic action in this agenda. |
| Remaining obstruction | Proceed to Shitlist #11: remove the Montgomery mean-value axiom while retaining a source-faithful theorem boundary. Separately, prove the two explicit arithmetic inputs and the coefficient-expansion identity in later F-07 work. |

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
| Target | `RiemannZeta/GuthMaynard/ZeroDetector.lean`, `ExtractSeparated.lean`, `HalaszMontgomery.lean`, the new production module `TypeIIZeros.lean`, `RiemannZeta.lean`, and `RiemannZeta/Audit.lean` |
| Previous defect | The project called the complement of Type I “Type II,” postulated the complete residual-zero estimate as `typeII_bound_unconditional`, and exposed a wrapper whose name falsely attributed that postulate to the Halász–Montgomery argument. |
| Semantic repair | Renamed the complement predicate and count to `IsResidualZero` and `residualZeroCount`, and renamed the partition theorem to `typeI_add_residual_eq_total`. Defined the source-facing short Möbius polynomial, Gamma–zeta contour integrand and integral, `IsContourTypeIIZero`, and the explicit Type-I/contour-Type-II coverage proposition in `TypeIIZeros.lean`. Residual and genuine Type II are no longer definitionally conflated. |
| Conditional proof | Introduced a generic finite weighted-zero interface independent of `zerosInRect`. Proved `weightedResidualCount_le_weightedCount_of_cover`, lifted this comparison to `EpsilonPowerBound`, proved the power-scaling lemma for epsilon bounds, derived the required scaled exponent from `TwistedZetaFourthMomentProp`, and combined these steps in `residual_zero_bound_of_cover_reduction_and_fourth_moment`. Every hypothesis is strictly upstream of the conclusion. |
| Honest analytic boundary | `TypeIContourTypeIICoverProp`, `TypeIIFourthMomentReductionProp`, and `TwistedZetaFourthMomentProp` are explicit unproved proposition specifications. The second records the Appendix C Gamma-decay/Hölder/separation/local-multiplicity reduction; it is not the final residual-zero bound. A concrete application to zeta zeros remains blocked on #13's multiplicity/extraction work and #15's nonaxiomatic zero-set construction. |
| Integrity impact | Deleted `typeII_bound_unconditional`, its misleading wrapper, and the old conclusion-shaped `TypeIIBoundProp`. Direct project axioms decreased from 24 to 23. No replacement axiom, hidden target hypothesis, or vacuous theorem was introduced. |
| Audit impact | The synchronized audit now contains 113 explicit and 113 discovered production theorems. All five new public Type II deductions pass with only `propext`, `Classical.choice`, and `Quot.sound`. Forbidden-dependency failures decreased from 18 to 17; the renamed concrete partition identity still honestly reports its inherited `riemannZeta_finite_zeros_in_rect` dependency. |
| Verification | Focused and full builds, plus `lake env lean scratch_pow.lean`, succeed with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_100245.log`: both build stages passed warning-free; the synchronized audit reported 113/113 declarations and the expected 17 failures; prohibited-placeholder, unsafe-bypass, and audit-quality scans passed; and the project-axiom scan correctly found 23 remaining declarations. Overall exit code remains honestly `1`. |
| Remaining obstruction | Proceed to Shitlist #13. Proving the three Type II analytic propositions and instantiating the generic theorem for the concrete zeta-zero family remain separate Goal C work; #12 does not claim Maynard–Pratt Lemma 24 unconditionally. |

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

## Current Priority

Proceed to Shitlist #13 in dependency order: first pull forward Mathlib's compact-set zeta-zero finiteness theorem; then correct the scale, constant, large-`T`, multiplicity, and shifted-interval interfaces; prove weighted selection and exact dyadic pigeonholing; and finally assemble the conditional extraction theorem from `LocalZeroMultiplicityBoundProp` and `DetectorBetaShiftProp`. Do not attempt to prove the current malformed target verbatim.

The first major research milestone remains a kernel-checked conditional Section 13.1 transfer from explicit, individually named hypotheses. The final large-values theorem remains the hardest long-term objective.
