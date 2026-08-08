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
| 3 | `TestExp.lean`, `test_separated.lean`, `test_zeta.lean` | Reuse existing proved lemmas where possible; otherwise remove the admitted experiments until their mathematics is proved. | Easy |
| 4 | `RiemannZeta/GuthMaynard/test_fourier.lean`, `RiemannZeta/GuthMaynard/ZeroCountScratch.lean` | Remove the zero Fourier-transform toy model and unused module-level symmetry assumption, or delete the scratch files. | Easy |
| 5 | `RiemannZeta/GuthMaynard/InghamBound.lean` | Remove or justify the unused Huxley premise and synchronize the statement with the actual proof. | Easy |
| 6 | `RiemannZeta/Audit.lean` | Replace name-based categorization with complete import coverage and actual axiom-dependency checks. | Easy–moderate |
| 7 | `RiemannZeta.lean` | Import every intended production module once those modules compile. | Easy but dependency-blocked |
| 8 | `RiemannZeta/GuthMaynard/ZeroDetector.lean` | Implement the actual truncated Möbius coefficients and prove their support and magnitude properties. | Moderate |
| 9 | `RiemannZeta/GuthMaynard/PolynomialPowers.lean` | Remove two `sorry`s and two axioms; prove the finite-product algebra and address the general k-divisor bound faithfully. | Moderate–hard |
| 10 | `RiemannZeta/GuthMaynard/MeanValue.lean` | Remove the Montgomery mean-value axiom and either prove the theorem or expose it only as a legitimate explicit upstream parameter. | Hard |
| 11 | `RiemannZeta/GuthMaynard/HalaszMontgomery.lean` | Repair compilation, prove the large-value consequence from an explicit mean-value input, replace the `True` dyadic lemma, and remove the Type II axiom. | Hard |
| 12 | `RiemannZeta/GuthMaynard/ExtractSeparated.lean` | Replace the Jensen `True` placeholder and eight axioms with genuine combinatorial extraction and explicit, narrower analytic inputs. | Hard–very hard |
| 13 | `RiemannZeta/GuthMaynard/Transfer.lean` | Remove the assumed conclusion and implement F-01 through F-10 from separately named upstream hypotheses. | Very hard |
| 14 | `RiemannZeta/GuthMaynard/ZeroCount.lean` | Prove or faithfully refactor zero finiteness with multiplicity, growth bounds, Phragmén–Lindelöf, and the Euler-product lower bound. | Very hard |
| 15 | `RiemannZeta/GuthMaynard/BetaDependence.lean` | Replace seven axioms with genuine Schwartz/Fourier inversion, decay, contour-shift, truncation, and pigeonhole arguments. | Very hard |
| 16 | `RiemannZeta/GuthMaynard/Decoupling.lean` | Repair syntax and type errors, replace the `True` block decomposition, and formalize the broad–narrow and incidence bounds without axioms. | Extreme |
| 17 | `RiemannZeta/GuthMaynard/LargeValues.lean` | Remove the module-level assumption and ultimately assemble the full Guth–Maynard large-values theorem. | Hardest; long-term Goal D |

## Dependency-Aware Execution Plan

### Phase 0: Remove noncanonical violations

**Files:**

- [x] `RiemannZeta/GuthMaynard/TestAxiom.lean` — deleted 8 August 2026 after confirming that no module imported or referenced its declarations
- [x] `ExtractSeparated_scratch.lean`, `Test.lean`, and `test2.lean` through `test6.lean` — deleted 8 August 2026 after confirming that they were unreferenced, admitted experiments against stale APIs
- `TestExp.lean`
- `test_separated.lean`
- `test_zeta.lean`
- `RiemannZeta/GuthMaynard/test_fourier.lean`
- `RiemannZeta/GuthMaynard/ZeroCountScratch.lean`

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

1. Create an explicit list of every public and agenda-critical declaration.
2. Import every intended production module into the audit.
3. Inspect dependencies rather than classifying declarations by name or declaration kind.
4. Make `sorryAx` and project-specific axioms visible as audit failures.
5. Correct the unused Huxley premise or its documentation.
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

## Current Priority

Begin with Phase 0 and Phase 1. After the repository is free of admitted scratch/test declarations and has a trustworthy audit, proceed through the Goal B dependency chain rather than attempting the full large-values theorem prematurely.

The first major research milestone remains a kernel-checked conditional Section 13.1 transfer from explicit, individually named hypotheses. The final large-values theorem remains the hardest long-term objective.
