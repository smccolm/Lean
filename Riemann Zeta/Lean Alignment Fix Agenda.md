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
| The default production build was not a repository-wide build: 32 of 60 Lean files were outside the 28-file production/audit perimeter. | #2, #6, #8 | **Resolved:** #2 removed 30 obsolete auxiliary files; #8 now runs both retained anonymous examples as separate warning-failing stages. |
| Five retained auxiliary files failed standalone elaboration: `RiemannZeta/GuthMaynard/test_pow.lean`, `test_le_floor.lean`, `TestCauchy.lean`, `test7.lean`, and `test8.lean`. | #2 | **Resolved:** all five were unreferenced duplicates, broken API probes, or stale experiments and have been deleted. |
| `clean_cache.lean` deleted `.lake/build` through elaboration-time `#eval`; `build_it.lean` invoked a hard-coded user-specific Lake path through `#eval`. | #2, #8 | **Resolved by deletion:** neither utility was imported or needed by the principal runner. |
| Several files historically described as deleted remained as empty or comment-only tombstones. | #2 | **Resolved:** every empty/tombstone Lean file has been deleted; no zero-byte Lean file remains. |
| `Audit.lean` checks transitive dependencies for the synchronized production theorem set. | #6 | **Complete as integrity infrastructure:** the current list is 1296/1296. It includes the actual-`X` Type-II, completed actual Type-I branch package, smooth `ζ²` AFE/diagonal and paired-Gamma declarations, finite DFI source-entry/Parseval/mean-square declarations, the periodic-Estermann/Mellin–Barnes contour chain, and reflection-core declarations. Every existing declaration passes with only the permitted logical dependencies; this does not make the missing output theorems complete. |
| `GuthMaynardLargeValues` formerly omitted positivity/eventual quantifiers and used the opposite exponential sign without a proof. | #14, #19, Goal A | **Resolved at the statement boundary:** the source-positive form has the correct quantifiers and `V > 0`; the negative-sign form is proved by coefficient conjugation. The analytic theorem remains an input. |
| `MontgomeryMeanValue` formerly used `[T,2T]`, while #13 produces `[0,3T]`. | #11, #14 | **Resolved at the interface boundary:** the proposition and finite consequence now use `[0,T]`; #13 is consumable at height `3T`. |
| `k_selection` formerly omitted part of equation (13.1) and did not bound `k`. | #14 | **Resolved:** both inequalities, `2 ≤ k ≤ 101`, and eventual absorption of the detector upper-scale logarithm are kernel-checked. |
| The explicit `powCoeff` expansion was not proved equal to `powPoly`; `polynomial_power_identity` was only a definitional structural-power identity. | #10, #14 | **Resolved in #10:** `polynomial_power_identity` is now the full finite coefficient expansion, with audited support and complex-power lemmas. |
| The powered support `(N^k,(2N)^k]` is wider than one dyadic block, and the block giving a large contribution may depend on the ordinate. | #14 | **Resolved:** the exact block split and simultaneous pigeonhole are integrated with restricted globally unit-bounded coefficients, a coefficient constant uniform for `2 ≤ k ≤ 101`, fixed-block comparison estimates, and uniform epsilon-loss absorption. |
| `N σ T` counts zeros in `[-T,T]`, but the Section 13.1 detector and Type-I/Type-II interfaces treat positive slabs `[T,2T]`. | #14 | **F-01 resolved:** zeta conjugation, analytic-multiplicity preservation, equality of negative/positive rectangle counts, finite low-height control, and eventual dyadic summation are kernel-checked. |
| Section 13.1 uses the new argument only for `7/10 ≤ σ ≤ 4/5` and invokes Huxley for `σ ≥ 4/5`, while `GuthMaynardZeroDensity` asks for the whole range through `σ = 1`. | #14 | **Resolved conditionally:** `high_sigma_of_huxley` proves the exact exponent comparison and the primitive-input transfer accepts `HuxleyZeroDensity`. |
| `Transfer.lean` formerly assumed a definitionally equivalent copy of its target and contained an unused `h_bound : True`. | #14 | **Resolved:** all circular declarations and the transfer-local `True` artifact are deleted. The audit-clean replacement derives its former Type-I slab and dyadic-to-global intermediates from ten individually named primitive inputs. |
| `BetaDependence.lean` contained an axiom with conclusion `True`, a contour-shift interface with unconstrained error, and a pigeonhole axiom that already packaged essentially the desired beta-removal conclusion. | #16 | **Resolved:** all seven malformed axioms were deleted; rational Phragmén–Lindelöf localization proves `beta_dependence_removal`, and `extractSeparated_native` is unconditional. |
| `l2_parabola_incidence_bound` is false for arbitrary finite 1-separated sets without a containing interval, and `DecouplingProp` has an off-by-one counterexample. | #19 | **Resolved by deletion:** the module, both false contracts, all wrappers, and both project axioms are gone. The replacement source-facing matrix/trace layer is underway. |
| #12 and #13 contain valid finite/conditional deductions, but their strongest proposition inputs package hard analytic reductions. The reopened #13 audit additionally found a shifted, scale-filtered occupancy input and unnormalized interval/loss output. | #12, #13 | **#12 reaches the concrete residual-zero target conditionally. #13 is now unconditional:** shifted covering, interval/coefficient translation, and epsilon-loss absorption are kernel-checked, while #15 and #16 discharge its two former analytic inputs. |
| The paper stated stale audit counts. | Documentation gate | **Resolved during #8 and kept synchronized:** the current audit passes across 1296 synchronized declarations. |

Current clean facts: the production graph elaborates with zero warnings; the dependency audit synchronizes and passes 1296 declarations; and the prohibited-proof and project-postulate scans are empty. The named output gate still reports seven absent end theorems; the overall result remains honestly `FAIL`/`1` until the remaining outputs exist.

### Authoritative Audit of Shitlist #1–#14

This table supersedes any unqualified use of “complete” in the chronological records below. A finite or conditional layer is complete only at the boundary stated; explicit upstream propositions are not thereby proved.

| Item | Verdict | Audited boundary |
|---:|---|---|
| 1 | **Verified complete** | The deliberately false `TestAxiom.lean` file is absent and unreferenced. |
| 2 | **Verified complete as cleanup** | The retained tree has 83 Lean files, no empty Lean file, an 80-file transitive production graph, `Audit.lean`, and exactly two non-production anonymous-example files. All listed obsolete tests, tombstones, and side-effect utilities are absent. |
| 3 | **Verified complete** | `TestExp.lean` and `test_separated.lean` elaborate in the principal runner; `test_zeta.lean` is absent. |
| 4 | **Verified complete** | The Fourier toy and zero-count scratch modules are absent and unreferenced. |
| 5 | **Verified complete** | `CombinedZeroDensityTransfer` has no unused Huxley premise. The distinct Huxley input used by #14 is mathematically scoped to the high-`σ` branch. |
| 6 | **Verified complete as audit infrastructure** | The explicit and discovered theorem sets agree at 1296/1296 and all transitive dependency checks pass. The separate completion gate fails on the seven absent #15/#18/#19 outputs. |
| 7 | **Verified complete** | The root import closure reaches all 79 subordinate production modules, giving an 80-file production graph. |
| 8 | **Verified complete as evaluation infrastructure** | The principal runner covers production, focused modules, both examples, warning checks, prohibited constructs, direct axioms, and the transitive audit. Its overall exit remains nonzero for valid mathematical-integrity reasons. |
| 9 | **Finite/source-reduction layer complete; input discharged in #17** | The actual truncated Möbius detector and divisor-cardinality reduction are proved, and `divisorCountBound_native` now supplies `DivisorCountBoundProp`. |
| 10 | **Finite/conditional layer complete; inputs discharged in #17** | Exact coefficient expansion and the conditional coefficient bound are proved; `powCoeffBound_native` is the unconditional downstream specialization. |
| ~~11~~ | **Verified complete** | `montgomery_mean_value_native` proves the `[0,T]` estimate, and `halasz_montgomery_lemma_native` supplies the unconditional consequence used downstream. |
| 12 | **Conditional/concrete layer complete** | The concrete `ResidualZeroBoundProp` follows from three explicit source-facing propositions. #18 now discharges `TypeIContourTypeIICoverProp` and `TypeIIFourthMomentReductionProp`; only the twisted fourth moment remains unproved. |
| ~~13~~ | **Verified complete** | Shifted covering, translation, phase preservation, and epsilon normalization are proved; #15 and #16 discharge the former unit-zero and beta-shift inputs, yielding `extractSeparated_native`. |
| ~~14~~ | **Verified complete at the planned conditional boundary** | F-01 through F-10 are kernel-checked as one deduction. The public theorem derives the central Type-I slab and global dyadic reduction from ten named primitive inputs; all 21 newly audited theorems pass with only permitted logical dependencies. |

Therefore #1–#8 close repair or evaluation defects, #9–#12 close their explicit finite/conditional scopes, #13 is now unconditional, and #14 closes the primitive-input conditional transfer milestone. The integrity defects are now eliminated, but the repository still lacks the three open items' required mathematical end theorems.

## Three Remaining Items: Exhaustive Completion Contract

Shitlist #15, #18, and #19 remain; #16 and #17 are complete. They are bounded work packages, not a strict serial order. Each open item has a discrete mathematical responsibility and an objective completion test. The list is exhaustive: every remaining primitive premise of #14, the Guth–Maynard large-values theorem, and final theorem integration are assigned below. Existing dependency checks, warning checks, and direct-postulate scans pass; the named research-output gate currently reports seven absent end theorems.

The canonical dependency view is [`Proof Architecture.md`](Proof%20Architecture.md). This table is authoritative for task numbering and acceptance tests; the diagram and `Research Agenda Progress.MD` must be updated in the same change whenever a status, obligation, or dependency changes.

| Item | Discrete responsibility | Required Lean deliverable | Completion test |
|---:|---|---|---|
| 15 | **Classical finite zero-density engine and endpoints — in progress** | The actual-`X` Type-II normalization/powering/MHH application is proved. The Type-I branch now has the correct `N^σ` source normalization, an epsilon-absorbed enlarged-interval MHH theorem, exact powered extraction, the weighted Weyl route, and both endpoint certificates in `actual_typeI_branch_resolution_native`. Remaining are the multiplicity-aware branch-to-slab reduction and the two endpoint theorems. | The item stays uncrossed until audit-clean theorems prove both `HuxleyZeroDensity (fun σ T => N σ T)` and `InghamZeroDensity (fun σ T => N σ T)`. |
| ~~16~~ | **Beta-removal theorem — complete** | Deleted all seven malformed `BetaDependence.lean` axioms. Proved polynomial coefficient-mass bounds, rational boundary decay, a right-half-plane Phragmén–Lindelöf transfer, the exact nearby fixed-line large-value theorem, `beta_dependence_removal : DetectorBetaShiftProp`, and `extractSeparated_native : ExtractSeparatedTarget`. This is a source-faithful alternative realization of F-04, not the agenda's suggested Fourier-cutoff implementation. | `BetaDependence.lean` contains no project axiom, `True` placeholder, unconstrained error, or conclusion-shaped premise; both final theorems pass the transitive audit; the principal runner builds the production graph warning-free. |
| ~~17~~ | **Arithmetic coefficient bounds — complete** | `divisorCountBound_native` proves `DivisorCountBoundProp`; `factorizationCountBound_native` proves `FactorizationCountBoundProp`; and `powCoeffBound_native` proves `PowCoeffBoundProp` without arithmetic premises. `MontgomeryMeanValue` remains discharged by `montgomery_mean_value_native`. | The five new public declarations are in the synchronized transitive audit with only permitted logical dependencies. Focused and root builds are warning-free, and the native mean-value and basic Halász–Montgomery results remain audit-clean. |
| 18 | **Type-II residual analysis and Goal C integration — in progress** | Completed: source-range contract repair; arbitrary-order Gamma decay; weighted whole-line Gamma and actual contour-integrand integrability; the complete native fourth-moment counting reduction; the full Appendix C coverage theorem; the exact `M²` arithmetic reduction; and the entire `AF` node. The finite shift/Kloosterman L2 layer is proved. `Estermann.lean` and `DivisorVoronoi.lean` additionally prove periodic continuation and reflection, exact Laurent main terms, pure-double-pole cancellation, finite/infinite contour shifts, and an assembled Mellin–Barnes Voronoi formula under explicit inversion/Fubini/integrability/tail hypotheses. Remaining are source-weight discharge of those hypotheses, delta-symbol localization, quantitative dual-transform/error summation yielding the DFI power saving, generic twisted moment/native specialization, and Goal C assembly after #15 supplies native Huxley. | `AF` is crossed off. `QD` remains open: its contour bridge is kernel-checked, but no theorem yet supplies the DFI error term. Overall acceptance still requires `twistedZetaFourthMoment_native` and the concrete full-range zero-density result from `GuthMaynardLargeValues` alone. |
| 19 | **Guth–Maynard large values and final project integration — in progress** | **Completed:** deletion of the false model; cutoff/derivative infrastructure; exact three-piece localization from the published sharp polynomial to one common smoothed matrix family; sampling-matrix and trace reductions; Fourier/Poisson foundations; the Hilbert–Schmidt first-trace expansion; uniform two-parameter Fourier decay; the exact cubic expansion and `S₁/S₂/S₃` partition; Proposition 5.1 for `S₁`; exact finite signed reflection identities; cancellation-preserving aggregate bounds; arbitrary Mellin decay; and pointwise uniform positive/negative core `T₀⁻¹ᐟ²` estimates. **Remaining:** the measurable core/tail integral split and complete summed omitted-frequency `T⁻¹⁰⁰` remainder of quantitative Lemma 6.2, native Heath–Brown, `S₂`, moment/energy bridge, `S₃`, affine/GCD estimates, Sections 3/12 assembly, and concrete transfers. | The large-values, concrete Guth–Maynard zero-density, and combined zero-density theorems are absent. The item is complete only when all three are kernel-checked, audited, documented, and the principal runner returns `PASS`/`0`. |

Completing the three open rows is, by definition, completion of the repository's current research agenda: Goals A–D are proved in Lean, the useful Goal E infrastructure is retained and documented, every integrity gate passes, and no untracked mathematical hypothesis remains. Upstream submission to Mathlib is optional follow-on work and is not a blocker for this repository-completion claim.

### Immediate Proof Queue — repository-wide audit, 10 August 2026

The dependency audit changes the most efficient implementation order without closing an owning Shitlist item. The following targets are ordered by estimated implementation difficulty, not by Shitlist number. Completed targets are recorded below the open queue rather than occupying a rank.

| Rank | Owning item | Complete closeout target | Why it is now reachable | Exact boundary |
|---:|---:|---|---|---|
| ~~1~~ | 15 | **Actual-`X` Type-II powered MHH application — complete** | `powered_actual_sharpMollified_block_large_values_bound` first normalizes the genuine `sharpMollifiedCoeff A X` block by #17's divisor bound, then performs exact finite powering, common dyadic extraction, coefficient normalization, and unrestricted MHH. `actual_typeII_powered_mhh_native` obtains the coefficient constant internally, so the result applies to `X = ⌊T^(δ₂/2)⌋₊` without an analytic premise. | Kernel-checked and audit-listed. This closes `IIE`, not the later branch-to-slab assembly. |
| ~~2~~ | 15 | **Actual Type-I finite absorption and endpoint routing — complete** | `normalizedClassicalTypeICoeff` supplies the missing `N^σ` normalization; `actual_typeI_dichotomy_witness_mhh_absorbed_native` absorbs the harmonic loss into `(3T)^ε`; `powered_actual_typeI_block_large_values_bound` realizes exact two/three-fold powering; and the weighted Weyl and endpoint-certificate routes are packaged by `actual_typeI_branch_resolution_native`. | Kernel-checked and included in the synchronized 1296-declaration audit. This closes `ZR`; threshold substitution, multiplicity, and the slab estimate remain the separate `FR` node. |
| ~~3~~ | 19 | **Source-to-matrix entry bridge — complete** | `sourceDirichletPoly_eq_three_gmSmooth` proves an exact three-piece source identity; `source_large_values_localize_to_matrix` selects one fixed scale/coefficient family on at least one third of the ordinates and applies the matrix bound. The published interval is already `(N,2N]`; a separate theorem records compatibility with the alternate closed convention. | Kernel-checked and included in the 1296-declaration audit. |
| 4 | 19 | **Quantitative smooth reflection** | Exact signed modes and cancellation-preserving aggregate bounds are now joined by arbitrary polynomial decay of the fixed Mellin weight, the elementary dual-polynomial tail bound, and uniform positive/negative `T₀⁻¹ᐟ²` core estimates. | Split and integrate the Mellin core/tail, sum both omitted Fourier-frequency tails with the required parameter-uniform `T⁻¹⁰⁰` loss, and prove the complete Lemma 6.2 inequality. |
| ~~5~~ | 18 | **Smooth `ζ²` approximate functional equation and diagonal bound — complete** | The exact completed-xi contour and ordinary-zeta normalization use a strength-100 even Gaussian. Finite Euler products prove the paired Gamma bound, the exact zero-line divisor factor is identified, and its archimedean norm has an integrable uniform Gaussian envelope. The concrete interval and Mellin-slice theorems feed that exact weight into the `hm = kn` harmonic majorant. | Kernel-checked in `GammaPairBound.lean` and `SmoothZetaAFE.lean`; `AF` is closed while `QuadraticDivisor.lean` now isolates the still-open DFI source theorem. |

Completed supporting layer: **#19 exact reflection identities and cancellation preservation.** `LargeValuesReflection.lean` proves `gmSmoothReflection_native`, identifies the old `norm_gmSmoothReflection_native_le` as a coarse factor-count estimate, and supplies replacement positive, negative, and signed bounds with no mode-cardinality loss. It now also proves arbitrary Mellin decay and the pointwise uniform positive/negative core `T₀⁻¹ᐟ²` estimates. The measurable core/tail integral split and complete summed omitted-mode remainder remain, so the quantitative Lemma 6.2 closeout stays open.

The remaining open nodes are not current standalone closeout candidates. The complete approximate-energy moment node still consumes Heath–Brown; the twisted fourth moment still consumes the DFI off-diagonal theorem; `S₂`, refined `S₃`, the energy theorem, and all final density outputs consume other open nodes. Heath–Brown, DFI, and Guth–Maynard Proposition 9.1 are independent entry points but remain major new source theorems rather than high-confidence near-term closeouts.

### Conclusive Implementation Plan for Shitlist #15

Shitlist #15 is one acceptance item with explicit finite interfaces and one final assembly gate. This is the selected path because it targets finite Dirichlet-polynomial and oscillatory-sum statements already close to the project's APIs. It does not require completing the entire classical Littlewood–Gabriel–fourth-moment contour stack.

#### Package A — Truncated zeta foundation — complete 9 August 2026

1. Added `ZetaTruncation.lean` and proved the variable-lower-limit Abel tail, its integrability, and `norm_abelZetaTail_le : ‖tail(b,s)‖ ≤ b ^ (-Re(s)) / Re(s)`.
2. Proved the finite summation-by-parts identity, the complex-power interval integral, the floor/fractional-part decomposition, and `riemannZeta_truncation` on `Re(s) > 0`, `s ≠ 1`.
3. Proved `zeta_zero_truncation` for genuine off-axis zeta zeros and `norm_zeta_zero_truncation_error_le`, with explicit error `‖ρ‖ b ^ (-Re(ρ)) / Re(ρ)`. No PNT+ theorem, new axiom, or conclusion-shaped premise is used.
4. Imported the module through `RiemannZeta.lean` and registered all nine new public theorems in the transitive audit. The focused and root builds are warning-free, and every new declaration has only permitted logical dependencies.
5. Pinned PNT+ at revision `4ecb950126c4290293c5662dfe0e884123171df5` and Mathlib at its exact Lean-4.30-compatible revision. Vendored the required `ZetaBounds`/`ZetaAppendix` proof sources locally, excluded the unrelated warning-producing Mertens import, and synchronized every exported theorem in the transitive audit.
6. Specialized the audit-clean Poisson/Euler–Maclaurin theorem `ZetaAppendix.proposition_dadaro` at `sharpZetaCutoff T = ⌊4T⌋ + 3/2`. The cutoff lies in `(4T,6T]`; its phase lies in `[1/12,1/4]`; the boundary and remainder coefficients are bounded by `14` and `129`; and `norm_zeta_zero_sharp_cutoff_sum_le` proves the detector-strength estimate `‖∑_{n≤a} n⁻ρ‖ ≤ 149 a⁻Re(ρ)` for every slab zero. Package A is therefore complete.

#### Package B — Targeted van der Corput and Weyl estimates — complete 9 August 2026

1. `VanDerCorput.lean` proves the unitary/logarithmic phase identities, three derivatives of the logarithmic phase, finite Weyl differencing, exact resolvent summation by parts, cotangent monotonicity and variation, and one-period Kusmin–Landau cancellation in increasing, decreasing, shifted-index, and shifted-period forms.
2. `SecondDerivative.lean` completes the monotone multi-period partition, counts indices close to `2πℤ`, applies interval Kusmin–Landau on every complementary block, and optimizes `δ = √λ` to prove the `(1/2,1/2)` B-process. `SecondOrderMeanValue.lean` supplies the localized second-order Rolle bridge used for logarithmic correlations.
3. `Weyl.lean` feeds that B-process into finite differencing. `WeylExplicit.lean` corrects the earlier summed-correlation overcount by using one uniform correlation majorant, selects `H = floor(A/Y)` for `t = Y³`, and proves the conventional `(1/6,2/3)` bound `‖Σ_{A≤n<2A} n^{-it}‖ ≤ 30 √(A Y)` together with a uniform-prefix form.
4. `WeylZeta.lean` proves finite Abel summation for antitone weights, identifies the weighted block exactly with `Σ (A+n)^(-1/2-iY³)`, and proves its norm is at most `30 √Y = 30 t^(1/6)` throughout the medium range. `FiniteDensityExponents.lean` correctly proves that this threshold covers the exceptional short Huxley zeta-polynomial range and that the corresponding Ingham range is empty. This does not control ordinary medium Type-I blocks: at `σ = 3/4`, `N = T^(2/3)`, and `V = N^(3/4)`, direct finite MHH gives a `T^(2/3)` contribution while the endpoint target is `T^(3/5)`. The standard B-process/reflection `N ↦ T/N` is therefore still required. Guth–Maynard Lemma 6.2 is a distinct smooth reflection input for #19; `LargeValuesReflection.lean` proves exact signed identities and the positive aggregate Mellin formula, but not yet the complete quantitative inequality.

#### Package C — Classical large values — complete 9 August 2026

1. `classical_montgomery_halasz_huxley_native` proves the full finite Montgomery–Halász–Huxley estimate
   `R ≪ T^ε (N^2 V⁻² + T * min (N V⁻²) (N^4 V⁻⁶))`
   for the project's separated finite ordinate sets and bounded coefficients.
2. `LogarithmicKernel.lean` proves the near-frequency `N/|t|` bound by shifted Kusmin–Landau and the far-frequency `√|t|` bound by the Package-B B-process. `ClassicalLargeValues.lean` proves phase-aligned finite Gram duality, harmonic separated-shell counting, local absorption, real floor-bin subdivision, the bounded-energy reduction, both quantitative branches, their `min`, and the final `T^ε` absorption.
3. The public theorem is warning-free and audit-clean: its transitive dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. The theorem assumes bounded coefficients directly; #17 supplies those bounds in powered-detector applications but is not hidden inside the finite analytic theorem.

#### Package D — Finite zero-density transfer

1. **Sharp zero truncation — complete:** `norm_zeta_zero_sharp_cutoff_sum_le` gives every zero `ρ ∈ zerosInRect σ 1 T (2*T)` a length-`O(T)` partial-zeta sum bounded by `149 * a ^ (-Re(ρ))`, with `4T < a ≤ 6T`.
2. **Exact-beta deweighting — complete:** `sharpMollifiedTail_beta_removal_native` applies the finite Dirichlet-series Phragmén–Lindelöf/localization theorem to the actual sharp Möbius product, retaining the requested `σ` exactly. The supporting mass estimates and eventual error-majorant absorption are kernel-checked; no hidden `σ - δ` premise or theorem-equivalent assumption is introduced.
3. **Finite detector, normalization, powering infrastructure, and dichotomy — complete within their exact signatures:** `ClassicalDetector.lean` proves finite zeta–Möbius cancellation and the raw tail witness. `FiniteDensityTransfer.lean` proves coefficient-mass bounds, common dyadic extraction, normalization, and unrestricted finite MHH. `ClassicalPowering.lean` proves exact finite powering and unit-bounded coefficient control. `FiniteDensityEndpoint.lean` now proves the coefficient-generic powering theorem and the unconditional arbitrary-`X` specialization `actual_typeII_powered_mhh_native`, eliminating the former `X=1` defect. The dichotomy is complete and returns the source Type-I/Type-II alternatives with analytic multiplicity.
4. **Endpoint-range reduction — arithmetic complete; analytic interfaces now separated:** `FiniteDensityExponents.lean` proves `ingham_zeta_polynomial_range_empty`, `huxley_zeta_polynomial_range_empty`, and `huxley_zeta_polynomial_range_below_weyl`. These settle the exceptional short zeta-polynomial ranges only after a Type-I witness has been converted to the fixed-coefficient short-polynomial form those certificates discuss. They do not perform that conversion. The obstruction is already visible at `σ = 3/4`, `N = T^(2/3)`, `V = N^(3/4)`: direct MHH has exponent `2/3`, larger than the required `3/5`.
5. **Multiplicity-aware common-witness extraction — complete:** `extract_sharpMollified_dyadic_witness_native`, `extracted_sharpMollified_block_card_bound`, and `finite_common_scale_binary_branch_extraction` combine the native Jensen cap, weighted branch selection, finite pigeonholing, separation, normalization, and unrestricted MHH while preserving analytic multiplicity. The global detector branch/scale choice is discharged by `classical_typeI_typeII_dichotomy_native`.
6. **Finite scale/exponent assembly — complete 9 August 2026:** `FiniteScaleAssembly.lean` defines the exact Montgomery–Halász–Huxley exponent and Corollary-11.10 subdivision envelope, proves the bounded two-or-three-fold scale reduction in both exponent and literal real-power form, proves both direct MHH windows and the final power-envelope bound, and constructs concrete `EndpointScaleCertificate`s for `τ₀ = 2 - σ` and `τ₀ = 3*σ - 1`. The public theorem `classical_finite_scale_exponent_assembly_native` packages the actual finite MHH theorem with both endpoint certificates. This closes the arithmetic assembly node without pretending that it proves the medium reflection or finite zero-density reduction; those are the separately open analytic inputs that must consume these certificates.
7. **Terminal Type-I branch — complete 10 August 2026:** `TerminalTypeI.lean` proves uniform Kusmin–Landau cancellation for every prefix beginning at a terminal scale, transfers it to the decreasing `n^{-σ}` weight by finite Abel summation, identifies the result with the actual `classicalZetaLongLineCoeff` block even when the sharp cutoff stops inside the block, and exports `typeI_scale_lt_height_of_large`, the case theorem consumed by the finite reduction. All five declarations are warning-free and audit-clean.
8. **Type-I smoothing and scale split — complete 11 August 2026:** `TypeISmoothing.lean` defines a fixed `C∞` dyadic partition, proves its support and exact telescoping identity on the actual tail, removes both sharp analytic edges while retaining exact values at integers, and proves common-scale extraction for a separated family with the precise `(k+1)` cardinality loss. Together with `typeISmoothScaleSplit_native`, this closes `PS`.
9. **Medium B-process — complete 11 August 2026:** `TypeIReflection.lean` proves that the source boundary is identically one on every interior medium cutoff support, proves parameter-uniform derivatives and Fourier decay for the normalized source kernel, applies scaled Poisson summation, splits the result into a finite symmetric dual window and a complete two-sided tail, and sums that tail with the explicit bound `K(1+|t|)^102/(Q^101 M^100)`. The public package is `mediumTypeIExactBProcess_native`. Its retained negative window is identified exactly with the common Mellin polynomial by `sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial`; no stationary-main-term approximation or unsummed remainder remains. The signed central window stays explicit in this optional analytic route.
10. **Shared Type-I deweighting — complete 11 August 2026:** `norm_classicalZetaLongLineCoeff_le_one` proves the sharp coefficients are fixed and unit-bounded; `typeISourceSmoothBlock_fourierDeweight` handles the short source block; and `typeIReflectedBlock_fourierDeweight` handles the corrected reflected logarithmic weight. The normalization is `t/(2πQ)`, forced by the exact Fourier phase rather than the inconsistent displayed cutoff in ANTEDB Lemma 11.5.
11. **Type-I branch resolution — complete 11 August 2026:** `normalizedClassicalTypeICoeff` repairs the decisive normalization by scaling the actual `n^{-σ}` block by `N^σ`. `actual_typeI_dichotomy_witness_mhh_absorbed_native` translates the enlarged ordinate interval into `[0,3T]`, applies MHH at threshold `N^σ V`, and absorbs the harmonic factor into `(3T)^ε`. `powered_actual_typeI_block_large_values_bound` implements the exact raised-scale route, while `actual_typeI_weyl_route_native` and the endpoint certificates cover the exceptional route. `actual_typeI_branch_resolution_native` packages all four components, closing `ZR` without claiming the later `FR` slab deduction.
12. **Actual Type-II powered MHH application — complete 11 August 2026:** `powered_unit_block_large_values_bound` isolates the coefficient-generic finite argument. `powered_actual_sharpMollified_block_large_values_bound` normalizes `sharpMollifiedLineCoeff A X σ` for arbitrary `X` using the proved divisor estimate and then performs exact powering, dyadic extraction, and MHH. `actual_typeII_powered_mhh_native` discharges the coefficient bound internally; no analytic premise or `X=1` specialization remains.
13. **Branch-to-slab reduction — open:** combine the completed Type-I theorem with the actual-`X` Type-II theorem, then convert the dichotomy's witness-set bound back to a positive-slab analytic-multiplicity zero count. This is `FR`; it must consume `ClassicalTypeITypeIIDichotomyConclusion` and both branch bounds explicitly.
14. This package owns the classical transfer required for Ingham and Huxley. It may later be reused by #18, but it does not by itself discharge #18's separately specified contour coverage, fourth-moment reduction, or twisted fourth-moment propositions.

##### Finite Type-I/Type-II dichotomy — completed implementation record

The selected implementation is `ClassicalDichotomy.lean`, built on the existing finite APIs. Public searches found no kernel-checked Lean implementation of this zero-density dichotomy in Mathlib, ANTEDB, PNT+, or the published zeta/L-function formalization. ANTEDB supplies the source proof; Mathlib supplies Dirichlet convolution, Möbius inversion, norm bounds, and weighted finite pigeonhole; PNT+ supplies zeta infrastructure already pinned in this repository. ANTEDB's Python zero-density code performs later exponent-region calculations and is not a proof of the analytic dichotomy.

1. **Exact pointwise split:** define the ordinary long tail `L(Y,A,ρ) = ∑_{Y<n≤A} n⁻ρ`. From the sharp zero approximation `‖S_A(ρ)‖ ≤ e` and `S_A = S_Y + L`, split on `q ≤ ‖S_Y(ρ)‖`. The first branch proves `q-e ≤ ‖L(Y,A,ρ)‖`. In the complementary branch, use the already proved exact identity `S_Y(ρ) * M_X(ρ) = 1 + sharpMollifiedTail Y X ρ` to prove `1-q*B ≤ ‖sharpMollifiedTail Y X ρ‖` whenever `‖M_X(ρ)‖ ≤ B`.
2. **Native thresholds and support:** specialize to `q = T⁻δ₂`, `Y = ⌊T^δ₁⌋`, and `X = ⌊T^(δ₂/2)⌋`. Prove one explicit eventual threshold giving `1 ≤ X ≤ Y ≤ A`, `e ≤ q/2`, and `q*B ≤ 1/4`. The native alternative is therefore a Type-I lower bound at least `q/2` or a Type-II lower bound at least `3/4`, with the Type-II coefficients supported exactly in `(X,X*Y]` and bounded by the existing divisor estimate.
3. **Exact-beta localization:** wrap `exists_nearby_large_value_finiteDirichlet` separately for the long ordinary-zeta tail and for `sharpMollifiedTail Y X`. The existing full-cutoff native wrapper must not be reused with the short cutoff without proving the altered hypotheses. Both branches must land on the exact line `Re(s)=σ` with explicit ordinate displacement and coefficient mass.
4. **Dominant branch:** partition the finite zero set by the decidable pointwise alternative and use analytic-vanishing-order weights. Select a branch containing at least half the total multiplicity; do not replace multiplicity by unweighted cardinality.
5. **Common dyadic scale:** apply `exists_large_dyadic_block` to the Type-I tail or `exists_sharpMollified_large_dyadic_block Y X` to the Type-II tail, then apply `finite_shifted_dyadic_witness_extraction` to obtain one scale and a `1`-separated ordinate set. Record all logarithmic, displacement-bin, local-multiplicity, and factor-two branch losses explicitly.
6. **Public acceptance theorem:** `classical_typeI_typeII_dichotomy_native` returns either a zero-count-zero case, a common-scale ordinary-zeta Type-I certificate, or a common-scale short Möbius-product Type-II certificate. Each nonempty certificate includes its scale range, fixed coefficients independent of the ordinate, uniform large-value lower bound, separated witness set, and an explicit bound for the original analytic multiplicity in terms of the witness cardinality.
8. **Verification and scope boundary:** the focused Type-I and Type-II endpoint modules build warning-free. Exact B-process, smoothing, reflection, deweighting, arbitrary-`X` Type-II powering, normalized and epsilon-absorbed Type-I MHH, exact Type-I powering, weighted Weyl, and the physical-scale bridge are registered in the transitive audit. `ZR` is complete; the later branch-to-slab theorem remains open.

#### Endpoint assembly and acceptance

1. **Ingham:** set `τ₀ = 2 - σ`. Send Type II through the actual-`X` powered MHH theorem and Type I through a new dichotomy consumer built from `typeI_dichotomy_witness_mhh_bound_native`; the existing certificate specialization supplies only the exponent window. Assemble the branch and multiplicity estimates to obtain `3 * (1 - σ) / (2 - σ)`.
2. **Huxley:** set `τ₀ = 3 * σ - 1`. Use the sixth-power MHH branch on Type II and the completed Type-I consumer once it exists, with `huxley_typeI_finite_window_resolution_native` supplying only the endpoint certificate. At `σ = 3/4`, derive the boundary from Ingham because both exponents equal `3/5`.
3. Prove `ingham_zero_density_native : InghamZeroDensity (fun σ T => N σ T)` and `huxley_zero_density_native : HuxleyZeroDensity (fun σ T => N σ T)` without project axioms, Guth–Maynard large values, #18 hypotheses, or theorem-equivalent premises.
4. Add every new public theorem to `Audit.lean`, build all affected modules without warnings, and run `run_lake_build.bat --no-pause`. Only both concrete endpoint theorems plus these verification gates close #15.

The completed truncation, detector dichotomy, exact-β removal, actual-`X` Type-II powering/MHH, normalized Type-I direct/powered/Weyl routes, endpoint arithmetic, terminal control, smoothing, exact `T/N` reflection, and deweighting remain valid. Weighted Littlewood, Gabriel interpolation, the standalone zeta fourth moment, and contour-edge moments are not mandatory for #15. The open path is now: perform the multiplicity-aware branch-to-slab reduction and prove both endpoints.

Primary implementation references are the [ANTEDB finite zero-density chapter](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html), the [ANTEDB Lean source tree](https://github.com/teorth/expdb/tree/main/Expdb), ANTEDB's [`zero_density_estimate.py`](https://github.com/teorth/expdb/blob/main/blueprint/src/python/zero_density_estimate.py), [Mathlib's L-series convolution API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Convolution.html), [Mathlib's Möbius API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html), [Mathlib's finite pigeonhole API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Pigeonhole.html), PNT+'s [`ZetaAppendix.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/IEANTN/ZetaAppendix.lean), and the source [Guth–Maynard paper](https://arxiv.org/html/2405.20552v2). Current ANTEDB contains Lean foundation modules but no reusable formal zero-density dichotomy or B/A/Weyl transform; its Python implementation automates exponent assembly rather than the analytic detector split. The pinned PNT+ sharp partial-zeta stack is an actual audited project dependency through the locally vendored source closure; ANTEDB and Guth–Maynard remain research references. Only this repository's pinned Lean build and dependency audit determine completion.

#### #15 foundation implementation audit — 9 August 2026

| Check | Verified result |
|---|---|
| Right-half-plane bound | `zeta_right_half_plane_bound` is now a theorem. It compares the absolutely convergent Dirichlet series termwise with ζ(2), then uses the proved bound `‖ζ(2)‖ < 5/3`. |
| Euler lower bound | `euler_product_lower_bound_2` is now a theorem. It bounds the Möbius L-series by `5/3` and uses its inverse identity with the Riemann zeta function to obtain the stated `3/5` lower bound. |
| Invalid interface removed | The unused `zeta_functional_equation_bound` axiom quantified over every `σ ≤ 0` with one fixed constant. This is incompatible with the Gamma-factor growth as `σ → -∞`; it was deleted rather than “proved” through a vacuous replacement. |
| Vertical growth | `riemannZeta_eq_abel`, `norm_riemannZeta_le_five_mul_norm`, `zeta_jensen_sphere_bound`, and `zeta_growth_bound_native` are kernel-checked; no project axiom remains in `ZeroCount.lean`. |
| Local multiplicity | `typeI_unit_bin_sum_le_jensen` and `localZeroMultiplicityBound_native` are kernel-checked and audit-clean. |
| Mean-value dependency | `montgomery_mean_value_native` and `halasz_montgomery_lemma_native` are kernel-checked. `integral_norm_sq_dirichletTimeUpTo_le` extends the continuous estimate from one dyadic block to `[1,X]`, and `integral_norm_sq_zetaMollifier_criticalLine_le` proves the actual critical-line mollifier second moment with the correct `(T+O(X)) log X` scale. |
| Rectangle argument principle | `RectangleArgumentPrinciple.lean` proves the multiplicity-aware logarithmic-derivative contour identity from analytic/meromorphic hypotheses, finite order, and boundary nonvanishing. `regularizedInghamZeroDetector_rectangle_argumentPrinciple` supplies the project detector specialization without an axiom or conclusion-shaped premise. |
| Classical-strip zeta growth | `norm_riemannZeta_le_twenty_mul_abs_im_on_classical_strip` derives `‖ζ(s)‖ ≤ 20 |Im(s)|` for `1/2 ≤ Re(s) < 3` and `|Im(s)| ≥ 1` from the native Abel-continuation bound. This subsumes the strip-growth role of the broader upstream PNT+ zeta modules without importing their duplicate dependency closure. |
| Truncated zeta at zeros | `ZetaTruncation.lean` retains the exact Abel identity and absolute tail bound, and now ports and specializes Dadaro's oscillatory Poisson/Euler–Maclaurin formula. `norm_zeta_zero_sharp_cutoff_sum_le` proves `‖∑_{n≤a} n⁻ρ‖ ≤ 149 a⁻Re(ρ)` at a half-integral cutoff with `4T < a ≤ 6T`. Package A is complete. |
| Endpoint boundary bridge | `huxley_zero_density_at_three_quarters_of_ingham` proves that a full Ingham estimate supplies the `σ = 3/4` Huxley case because both exponents normalize to `3/5`. It does not assume or claim the Huxley interior. |
| Classical large values | `LogarithmicKernel.lean` and `ClassicalLargeValues.lean` prove the full finite Montgomery–Halász–Huxley estimate. The public `classical_montgomery_halasz_huxley_native` theorem contains both `T * N * V⁻²` and `T * N^4 * V⁻⁶` alternatives through an exact `min`, with the harmonic shell loss absorbed into `T^ε`. |
| Finite scale/exponent assembly | `FiniteScaleAssembly.lean` proves the two-or-three scale reduction in exponent and literal power form, both MHH exponent windows, the Corollary-11.10 envelope and power inequalities, and concrete Ingham/Huxley endpoint certificates. `classical_finite_scale_exponent_assembly_native` is kernel-checked and contains the actual finite MHH theorem, not a proposition parameter. |
| Downstream work | Concrete Huxley and Ingham remain unproved. Exact-β removal, the dichotomy, common extraction, normalization, exact powering, the `X=1` theorem, coefficient growth, endpoint arithmetic, terminal restriction, source smoothing/common-scale extraction, the exact medium B-process, both deweighting identities, the generic Type-I MHH helper, and enlarged-interval normalization are complete. The actual dichotomy consumer, actual-`X` Type-II application, branch-to-slab consumer, and symmetric specialization remain. |
| Verification | The focused Type-I, paired-Gamma, smooth-AFE, quadratic-divisor, Estermann, and divisor-Voronoi modules pass without warnings. The current audit passes 1296/1296 dependency checks but fails the output gate on the two absent #15 endpoints and five other agenda outputs. The principal run is expected to preserve the honest overall `FAIL`/`1` until those outputs exist. |

This is substantive partial progress, not completion of #15. The item remains uncrossed because the two acceptance outputs `HuxleyZeroDensity (fun σ T => N σ T)` and `InghamZeroDensity (fun σ T => N σ T)` are still missing.

### Researched Completion Plan for Shitlist #18 — 10 August 2026

The public search found no drop-in Lean proof of the Maynard–Pratt Appendix C reduction, a twisted fourth moment, or the quadratic-divisor estimate underneath it. The viable route combines existing project and Mathlib infrastructure with narrowly selected external mathematics; a cited paper is a mathematical specification, never a Lean dependency.

1. **Coverage boundary — complete.** `TypeIContourTypeIICoverOnProp σ₀` exists, `TypeIContourTypeIICoverProp` is its `σ₀ = 7/10` specialization, and `typeIContourTypeIICoverOn_native` proves that exact source-range proposition.
2. **Uniform vertical Gamma decay and honest integrability — complete.** `GammaVerticalDecay.lean` obtains arbitrary polynomial decay directly from Gamma recurrence and the positive-half-plane Euler-integral bound. It proves continuity, whole-line integrability, and linear-weight integrability. `TypeIIContour.lean` combines this with a global Abel-formula critical-line zeta estimate and finite Möbius bounds to prove `integrable_typeIIContourIntegrand` for the full source strip.
3. **Appendix C coverage — complete.** `TypeIICoverage.lean` proves absolute convergence and inverse Mellin for the exponentially smoothed detector, the exact `Γ(s) ζ(ρ+s) M(ρ+s)` transform, analytic removal of the apparent `s=0` singularity, the finite rectangle shift and sole residue at `s=1-ρ`, quantitative horizontal and vertical tails, exact Möbius cancellation, the constant/body/tail dyadic decomposition, and the final `5/6`, `1/3`, and `1/12` margin assembly. The public outputs are `typeIContourTypeIICoverOn_native` and `typeIContourTypeIICover_native`.
4. **Fourth-moment reduction — complete.** `ScaledSeparated.lean` proves weighted selection for arbitrary positive `G` without losing fiber weights and proves overlap at most one when `G > 2H`. `TypeIIFourthMomentReduction.lean` proves the concrete multiplicity-preserving ordinate/fiber identity, Jensen unit-bin control, growing-scale extraction, representative-zero construction, the exact contour-to-critical-line Gamma convolution inequality, weighted fourth-power Hölder, arbitrary-order quantitative Gamma-tail absorption, bounded-overlap conversion to `[T/2,3T]`, and final epsilon-power assembly. The theorem `typeIIFourthMomentReduction_native` discharges `TypeIIFourthMomentReductionProp` without a new hypothesis.
5. **Generic twisted-fourth-moment theorem.** Rewrite `|M(s)ζ(s)|⁴` as `|ζ(s)|⁴ |M(s)²|²`. The reusable smooth `ζ²` AFE and diagonal evaluation for arbitrary coefficient-controlled Dirichlet polynomials are complete. The exact finite shift and affine Kloosterman L2 layers are proved. `Estermann.lean` and `DivisorVoronoi.lean` now prove periodic continuation/reflection, the exact Laurent main term, double-pole cancellation, vertical contour shift, and an assembled Mellin–Barnes Voronoi formula with visible inversion/Fubini/integrability/tail assumptions. The DFI closeout must now discharge those assumptions for the source test weights, implement the delta-symbol localization, obtain quantitative dual-transform cancellation, and perform the dyadic summation giving `P^(5/4)(X+Y)^(1/4)(XY)^(1/4+ε)`. Only then may the generic length-`T^(1/22)` and native moment bounds be assembled. Hughes–Young's full six-main-term asymptotic is unnecessary, but this off-diagonal power saving is not optional. The existing L2 cancellation may be used only through a proved consumer matching the DFI summation geometry and exponent.
6. **Möbius-square arithmetic specialization complete; analytic application open.** `TwistedMoment.lean` proves the exact convolution, support, eventual `cutoff(T)² ≤ T^(1/22)`, divisor-count coefficient bound, and exact `|Mζ|⁴ = |ζ|⁴ |M²|²` integral reduction. Applying the still-open generic Hughes–Young/DFI theorem to obtain `twistedZetaFourthMoment_native` remains part of step 5.
7. **Goal C specialization.** Combine the repaired native coverage theorem, `typeIIFourthMomentReduction_native`, `twistedZetaFourthMoment_native`, #15's native Huxley theorem, and the completed #16/#17 inputs. The public output must be `guthMaynardZeroDensity_of_largeValues_native`, whose sole mathematical hypothesis is `GuthMaynardLargeValues`.

Acceptance now requires the one remaining analytic Type-II input—the twisted fourth moment—plus explicit convergence for every whole-line integral, no theorem-equivalent premise hidden behind a generic wrapper, and an audit-clean one-premise Goal C theorem. Principal references are [Maynard–Pratt Appendix C](https://ora.ox.ac.uk/objects/uuid%3Ab2cc1c2e-6cec-495a-ba6a-61ba08acc723/files/sj38609141), [Mathlib's proved Mellin inversion](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/MellinInversion.lean), [Hughes–Young](https://arxiv.org/abs/0709.2345), the stronger but less suitable [Bettin–Bui–Li–Radziwiłł route](https://arxiv.org/abs/1609.02539), and [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).

#### Quadratic-divisor deep-research result — 12 August 2026

The source/Lean correspondence is now exact enough to prevent a false closeout:

| Human proof layer | Exact Lean status and required consumer |
|---|---|
| Hughes–Young AFE and `hm = kn` diagonal | Complete in `SmoothZetaAFE.lean`, `GammaPairBound.lean`, and `TwistedDiagonal.lean`. |
| `hm ≠ kn` to `am-bn=r` | Complete in `finiteQuadraticDivisorOffDiagonal_eq_sum_shifts`. |
| Complete exponential sums | Definitions, symmetry, DFT Parseval, and `kloostermanSumZMod_mean_square` are kernel-checked. The last theorem proves `∑ₘ |S(m,n;q)|²=qφ(q)` exactly. |
| DFI delta symbol and smooth derivative budget | Not formalized. This must model DFI equations (9)–(22), not an arbitrary finite weight. |
| Divisor Voronoi | The periodic Estermann continuation, functional equation, exact Laurent main terms, double-pole contour cancellation, vertical shift, reflected dual contour, and an assembled Mellin–Barnes Voronoi formula are kernel-checked in `Estermann.lean` and `DivisorVoronoi.lean`. The source-specific inversion/Fubini/tail discharge and quantitative dual-transform bounds needed for DFI Proposition 1 remain open. |
| Weil cancellation | `KloostermanWeilBoundProp` is only a stated proposition. The required pointwise composite-modulus theorem is absent; Mathlib's Gauss/Jacobi sums and elementary étale scaffolding do not contain this result. |
| Bessel range and integration-by-parts estimates | Not formalized. Mathlib has no number-theoretic `Y₀/K₀` API. |
| DFI Theorem 1 error | Not formalized. Its exact target is `P^(5/4)(X+Y)^(1/4)(XY)^(1/4+ε)` after the dyadic parameter optimization. |
| Hughes–Young summation and native moment | Not formalized. It must sum the DFI error over the mollifier coefficients and conclude `twistedZetaFourthMoment_native : TwistedZetaFourthMomentProp`. |

Broad GitHub/web searches found no reusable Lean, Coq, or Isabelle implementation of the divisor-Voronoi/pointwise-Weil package. Hughes–Young explicitly state that their error term depends entirely on DFI Theorem 1. Their stronger successors use Watt/spectral Kloosterman machinery and are therefore not a smaller formalization. A direct Dirichlet-polynomial mean value has length `T * T^(1/50)` after the squared mollifier and leaves a fixed positive power; the trivial Kloosterman cardinality estimate has the same fatal feature. Such a loss cannot be absorbed by the project's every-positive-`ε` definition of `EpsilonPowerBound`.

Verification after this research pass: the focused `QuadraticDivisor.lean`, `Estermann.lean`, and `DivisorVoronoi.lean` elaborations and the full `RiemannZeta` build pass with zero Lean warnings. The synchronized dependency audit passes all 1296 existing declarations, including the Kloosterman mean-square/affine bounds and the complete explicit-hypothesis Mellin–Barnes contour chain, with only `propext`, `Classical.choice`, and `Quot.sound`. The output audit exits `1` solely because the seven named research outputs, including `twistedZetaFourthMoment_native`, remain absent.

### NEXT CLOSEOUT execution contracts — 10 August 2026

This pass treats every node literally labelled `NEXT CLOSEOUT` as an implementation package. A package is not complete merely because its phase algebra or proposition is present.

1. **#18 smooth `ζ²` AFE and diagonal — complete.** `SmoothZetaAFE.lean` constructs the entire completed-xi numerator, proves its growth and reflection, shifts the finite rectangle, proves both horizontal edges vanish, and obtains the completed and ordinary-zeta critical-line limits plus the right-line divisor-series form. `GammaPairBound.lean` proves the missing cancellation-sensitive ratio from Euler's finite products, and the strengthened admissible Gaussian yields the exact uniform coefficient bound and an integrable Gaussian envelope. The diagonal is evaluated, regrouped by `q = hm = kn`, and the concrete coefficientwise weight is bounded on the height interval and consumed by the harmonic majorant at every Mellin ordinate. DFI and `hm ≠ kn` remain in `QD`.
2. **#19 quantitative smooth reflection — open.** `LargeValuesReflection.lean` proves arbitrary-order uniform two-parameter decay, explicit pointwise far-frequency control, exact cutoff Mellin inversion and Fubini transfer, a first/second-derivative bound `10 / √τ`, signed-mode conjugation, exact finite reflected sums, cancellation-preserving aggregate bounds, arbitrary Mellin decay, and pointwise uniform positive/negative core `T₀⁻¹ᐟ²` estimates. The public `gmSmoothReflection_native` is an identity, not the quantitative Lemma 6.2 closeout. The measurable core/tail integral split and the complete omitted-mode `T⁻¹⁰⁰` estimate remain.
3. **#15 branch interfaces — closed before slab assembly.** `TypeISmoothing.lean`, `TypeIReflection.lean`, and `TypeIFourierDeweight.lean` close the smooth/reflected transformations. `TypeIFiniteWindow.lean` now proves the normalized, epsilon-absorbed direct Type-I route, exact powered route, weighted Weyl route, and endpoint package. `FiniteDensityEndpoint.lean` closes the actual-`X` Type-II application. Both `ZR` and `IIE` are complete; the next #15 obligation is `FR`, the multiplicity-aware slab reduction.

   **Deep-research and dependency audit, 10 August 2026.** ANTEDB Lemma 11.5 has two separate Type-I formulas. A short smoothed block is Fourier-deweighted directly to an ordinary polynomial; a medium block at scale `N` first reflects to positive modes at `M = 2*pi*T/N`, with stationary factor `m^(it) * (2*pi*m^2/t)^(-1/2)`, and only then uses the same deweighting step. Broad searches of Mathlib, PNT+, ANTEDB/Expdb, and public Lean repositories found no formal stationary-main-term, sharp-to-smooth Type-I extraction, or zeta-block deweighting theorem to import. PNT+ proves the exact sharp Poisson formula and nonstationary expansion only. The completed `LargeValuesReflection.lean` supplies a reusable `T^(-1/2)` common-integral bound and common-Mellin-variable architecture, but its kernel is `w(x)^2*x^(it)`, not the actual `w(x)*x^(-sigma-it)` amplitude. Local symbol tracing also found no downstream consumer of `ClassicalTypeITypeIIDichotomyConclusion` or `EndpointScaleCertificate`. The faithful boundary is therefore three theorems, not one oversized “reflection” theorem: smoothing/classification, medium B-process, and shared deweighting. The subsequent branch-to-slab theorem must visibly consume the dichotomy and endpoint certificates.

The primary sources are ANTEDB Lemma 11.5 for #15, Hughes–Young Sections 2.1–3 for #18, and Guth–Maynard Lemmas 4.3 and 6.2 for #19. Mathlib supplies Mellin inversion, Schwartz Fourier theory, Poisson summation, and completed-zeta reflection. PNT+ supplies the exact partial-zeta Poisson formula and nonstationary phase expansion. Broad repository searches found no public Lean implementation of any of the three acceptance theorems, so none may be closed by import or citation alone.

**Implementation result.** `PS`, `MR`, `FD`, `IIE`, `ZR`, and `AF` are complete and audit-clean. `MR` exports `mediumTypeIExactBProcess_native`; `TypeIFiniteWindow.lean` supplies the corrected `N^σ` normalization, absorbed direct MHH route, exact powered route, weighted Weyl route, and final branch package. The source/Lean bijection is in `Type I Reflection Proof Bijection.md`. `GammaPairBound.lean` and `SmoothZetaAFE.lean` close the contour, ordinary-zeta normalization, coefficientwise Gamma-ratio weight, Gaussian decay, and weighted-diagonal layers of `AF`. `LargeValuesCubic.lean` closes its cubic/`S₁` package; `LargeValuesReflection.lean` closes only the exact reflection-identity layer, not quantitative Lemma 6.2.

### Source-Faithful Completion Plan for Shitlist #19 — 10 August 2026

**Implementation status, 11 August 2026:** Packages 1–4 are complete. The source-entry localization feeding Package 3 is also complete. Package 2 includes exact translation invariance, nonzero scaling covariance, affine reindexing, the seven-bin floor partition of tolerance-one energy, and the injection of its zero-defect bin into Mathlib exact additive energy for one-separated sets. Package 3 proves the exact operator-norm conclusions of Guth–Maynard Lemmas 4.1–4.2. Package 4 is closed by `LargeValuesCubic.lean`: it proves the complete Hilbert–Schmidt first-trace layer, exact cubic Poisson expansion, diagonal main term with `Oε(T⁻¹⁰⁰)` remainder, exact `S₁/S₂/S₃` split, and Proposition 5.1 in its epsilon-separated `Oε(T⁻¹⁰)` form. Package 6 has exact identities and cancellation-preserving two-sign aggregate infrastructure but remains open at its quantitative Lemma 6.2 conclusion. Packages 5–14 otherwise remain open. The audit and integrity portion of Package 14 passes, but final integration does not because the native large-values and concrete density theorems are absent.

The deleted `Decoupling.lean` interfaces were not valid weakened forms of Guth–Maynard. `l2_parabola_incidence_bound` permitted an arbitrary finite separated set while its bound had no dependence on a containing interval or height. `DecouplingProp` had an off-by-one counterexample at `K=N` with the coefficient supported at `N+1`. Guth–Maynard's paper does not use a parabola-decoupling theorem. The file, both contracts, their wrappers, and both project axioms are absent from the current tree.

The implementation target is pinned to [Guth–Maynard v2, 7 April 2026](https://arxiv.org/html/2405.20552v2), Theorem 1.1 and Sections 3–12. Its three-term conclusion is exactly the existing `GuthMaynardLargeValues` contract:

`|W| ≤ C T^ε (N² V⁻² + N^(18/5) V⁻⁴ + T N^(12/5) V⁻⁴)`.

The replacement is divided into theorem-sized packages. A package is complete only when its named mathematical output is proved without a new primitive proposition parameter or project axiom.

1. **Delete the false model and freeze conventions — complete.** `Decoupling.lean`, all four rejected declarations, and both project axioms are gone. `LargeValuesDefinitions.lean` fixes `(N,2N]`, the positive phase, the cutoff convention, and the source `R` function.
2. **Build the shared quantitative language — complete.** Compactly supported smooth-cutoff data, all-order derivative bounds, the sampling matrix, `R_W(v)`, tolerance-`η` energy, monotonicity, elementary energy bounds, translation/scaling covariance, affine reindexing, the exact floor-defect partition, and the Mathlib exact-energy bridge are proved.
3. **Prove the trace-dispersion algebra — complete.** The scalar sixth-moment dispersion theorem, exact matrix action and Gram kernel, positive Hermitian Gram spectrum, first/cubic trace identities, spectral cubic formula, singular-value identities, the matrix operator-energy estimate, the large-values cardinality estimate, and the sixth-root operator trace-dispersion conclusion prove the exact outputs of Lemmas 4.1–4.2.
4. ~~**Formalize Fourier decay, Poisson, and `S₁`.**~~ **Complete.** `LargeValuesPoisson.lean` proves the trace kernel and first-trace formula. `LargeValuesCubic.lean` proves the exact cubic Gram-trace Poisson expansion, identifies the all-zero diagonal term, controls its off-diagonal remainder by `Oε(T⁻¹⁰⁰)`, partitions all remaining configurations exactly into `S₁`, `S₂`, and `S₃`, and proves Proposition 5.1 as `gmCubicS1_estimate` with `Oε(T⁻¹⁰)` decay.

   **Research and proof route.** The controlling source is Guth–Maynard Lemma 4.5 and equations (5.4)–(5.5), followed by Proposition 5.1. The implementation reuses Mathlib's Schwartz/Poisson and absolutely summable integer-series APIs plus this repository's proved trace kernel and uniform two-parameter Fourier decay. No screened public Lean repository contains the cubic Guth–Maynard trace split or Proposition 5.1; Mathlib and PNT+ provide lower-level Fourier, Mellin, and Poisson infrastructure only. The proof therefore expands every Gram entry into its zero mode and complete nonzero tail, proves cancellation of the three Mellin phases around the trace cycle, isolates the diagonal zero mode, and bounds the one-tail configurations using separation and arbitrary-order decay.
5. **Prove the Heath–Brown difference-set mean square.** Formalize the 1979 estimate used as Guth–Maynard Theorem 1.6, including the three terms `|W|²N`, `|W|N²`, and `|W|^(5/4) T^(1/2) N`, with explicit epsilon-loss quantifiers. This is an internal theorem, not a permanent hypothesis of the final result. Its source is [Heath–Brown, *A large values estimate for Dirichlet polynomials*](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms/s2-20.1.8).
6. **Prove quantitative smooth reflection — in progress.** `LargeValuesReflection.lean` proves uniform Fourier decay, exact Mellin/Fubini rescaling, the critical oscillatory estimate, signed positive/negative reflected-mode identities, cancellation-preserving aggregate bounds, arbitrary Mellin decay, an elementary dual-tail bound, and pointwise source-uniform positive/negative core `T₀⁻¹ᐟ²` estimates. The remaining acceptance boundary is the measurable core/tail integral estimate and the complete summed two-sided `T⁻¹⁰⁰` omitted-frequency remainder.
7. **Close `S₂`.** Combine smooth reflection, dyadic selection, bounded powering, #17 factorization coefficients, and the native Heath–Brown theorem to prove Proposition 6.1. All scale selection and `T^ε` absorption must use existing finite pigeonhole and `EpsilonPowerBound` machinery.
8. **Create the approximate-energy bridge.** Express `∫|R_W(v)|⁴` as a smoothed count of tolerance-one additive quadruples, prove the `L²` and `L⁴` estimates used in Section 8, and isolate the exact normalization constants. Mathlib's `Finset.addEnergy` can serve only after the floor-bin comparison because its native notion counts exact equalities.
9. **Prove `S₃` localization.** Formalize the Section 7 change of variables and Jacobian, the nonstationary tail estimates, and Propositions 7.1–7.2. The local Carleson van der Corput machinery may discharge tail estimates but does not replace this multivariable argument.
10. **Prove the affine-transformation estimate.** Define finite truncations of the Section 9 functional `J`; prove Proposition 9.1 by Poisson summation in the third integer variable, rational/lattice reindexing, and iterative smoothing. State the estimate uniformly for every truncation to avoid an unnecessary measurable-supremum obligation; encode the downward epsilon iteration as finite natural-number induction.
11. **Derive the refined `S₃` bound.** Combine the affine estimate with the `R_W` moment/energy bridge to prove Proposition 10.1, with terms `T²|W|^(3/2)` and `TN|W|^(1/2)E(W)^(1/2)`.
12. **Prove the energy theorem.** Formalize the Section 11 smoothed third moment and discrete second/fourth moments, split reduced rational approximations by small and large gcd, prove the spacing/counting lemmas, and assemble Proposition 11.1. Use Mathlib's natural-number gcd/coprimality APIs, but retain the source tolerance-one real energy.
13. **Assemble the exact large-values theorem.** Combine `S₁`, `S₂`, refined `S₃`, and the energy theorem into Proposition 3.1, perform the Section 3 interval smoothing and separated-subset reduction, and derive `guthMaynardLargeValues_native : GuthMaynardLargeValues`. Use the already proved classical Montgomery–Halász–Huxley theorem for regimes outside the central Guth–Maynard window when finite exponent comparison shows it dominates the target; do not add Jutila as a second analytic dependency unless that comparison fails.
14. **Integrate and accept.** Delete `LargeValues.lean`'s placeholder status, register every new public declaration in `Audit.lean`, discharge Central Type I, apply #18 Goal C, derive the concrete Guth–Maynard and combined zero-density theorems, synchronize all three status documents, and require `run_lake_build.bat --no-pause` to return `PASS`/`0` with zero warnings and zero project axioms.

The two hard, largely independent critical paths are Package 5 (Heath–Brown) and Package 10 (the affine-transformation proposition). Matrix algebra, Poisson trace expansion, and approximate-energy bookkeeping should be completed before either is used by the final assembly. The difficulty order is therefore: interface deletion and definitions; scalar/matrix identities; energy bookkeeping and `S₁`; smooth reflection and `S₂`; Heath–Brown and affine transformation; GCD energy assembly; final exponent and epsilon assembly.

The screened Lean ecosystem provides lower-level components, not the target proof: [Mathlib Poisson summation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/PoissonSummation.html), [Schwartz-space Fourier theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.html), [matrix trace](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Trace.html), [singular values](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html), and [exact additive energy](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/Energy.html). [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) supplies reusable Mellin, Fourier, and Poisson infrastructure, while the Carleson project's [van der Corput development](https://github.com/fpvandoorn/carleson/blob/master/Carleson/Classical/VanDerCorput.lean) supplies only one-dimensional oscillatory-tail tools. Broad searches found no public Lean implementation of Guth–Maynard Theorem 1.1, Heath–Brown's difference-set theorem, or Guth–Maynard Proposition 9.1. Consequently, #19 remains open, but its route and acceptance obligations are now explicit and source-faithful.

### #16 beta-removal implementation audit — 8 August 2026

| Check | Verified result |
|---|---|
| Interface disposition | Deleted the seven former beta-layer axioms, including the `True` placeholder, unconstrained contour-error statement, and conclusion-shaped pigeonhole premise. No replacement axiom or hidden proposition parameter was introduced. |
| Analytic mechanism | For `z = σ + iγ`, `a = β - σ`, `H = T^(δ/2)`, and an integer `k`, the proof applies Mathlib's right-half-plane Phragmén–Lindelöf theorem to `((H/(H+w))^k) D_N(z+w)`. The rational factor is near one at `w = a`, decays outside `|Im w| ≤ T^δ`, and converts an interior large value into a boundary large value. |
| Quantitative control | `detectorMass_le_pow_seven` gives a uniform `T^7` coefficient-mass bound at admissible scales. Choosing `δ k ≥ 18` makes the exterior contribution smaller than `1/(4 log T)`, while `H > 4k` keeps the interior localizer norm above `3/4`. Thus the exact `1/(3 log T)` input becomes the required `1/(4 log T)` fixed-line output within displacement `T^δ`. |
| Final theorems | `beta_dependence_removal : DetectorBetaShiftProp` proves F-04 for the actual detector and actual Type-I zero set. `extractSeparated_native : ExtractSeparatedTarget` combines it with the previously proved Jensen multiplicity theorem and the complete #13 extraction machinery. |
| Source relationship | Guth–Maynard Section 13.1 presents beta removal using a smooth cutoff and truncated Fourier expansion. The Lean proof establishes the same pointwise fixed-line conclusion by an alternative complex-analytic localization argument; the documentation does not claim that the Fourier implementation was formalized. |
| Audit impact | The current explicit and discovered theorem sets agree at 1296/1296. Every beta/localization theorem, `extractSeparated_native`, every classical-moment theorem, the vendored PNT+ proof closure, native #18 coverage/reduction/AFE/diagonal, paired-Gamma, finite DFI-entry/Parseval/mean-square, periodic-Estermann and Mellin–Barnes contour theorems, and the #15/#19 proved foundations pass with only `propext`, `Classical.choice`, and `Quot.sound`. |
| Principal verification | The current focused audit synchronizes and passes 1296/1296 existing declarations. Its named output gate fails on seven absent agenda theorems, so the overall result remains honestly `FAIL`/`1`. |

### #17 arithmetic-coefficient implementation audit — 9 August 2026

| Check | Verified result |
|---|---|
| Divisor estimate | `divisorCountBound_native : DivisorCountBoundProp` proves the uniform subpolynomial divisor bound. The proof splits prime factors at an epsilon-dependent threshold, controls the finitely many small primes by an explicit constant, controls large primes by `a + 1 ≤ p^(εa)`, and reconstructs `n` from its factorization. |
| Ordered factorizations | `factorizationCountBound_native : FactorizationCountBoundProp` injects each positive ordered factorization of `m` into a `Fin k` tuple of divisors of `m`, bounds the tuple count by `d(m)^k`, and applies the divisor estimate with exponent `ε/(k+1)`. The proof includes `k = 0` without a separate assumption. |
| Downstream specialization | `powCoeffBound_native : PowCoeffBoundProp` applies `powCoeff_bound_of_divisor_and_factorization` to the two native witnesses. No divisor, factorization, detector-coefficient, or other arithmetic proposition parameter remains in this powered-coefficient result. |
| Integration | `ArithmeticCoefficients.lean` is imported by `RiemannZeta.lean`; all five new public declarations are explicitly registered in `Audit.lean`. The existing `montgomery_mean_value_native` and `halasz_montgomery_lemma_native` remain unchanged and audit-clean. |
| Verification | The focused arithmetic, paired-Gamma, smooth-AFE, quadratic-divisor, Estermann and divisor-Voronoi modules and root production closure build with zero warnings. The current audit synchronizes 1296/1296 declarations; all five #17 declarations and the proved #15/#18/#19 foundations pass with only permitted logical dependencies. |

## Historical Files Ordered by Estimated Repair Difficulty

This section now separates historical cleanup ranks from the files that still carry research obligations. The repository-wide audit covers the newly added production module `TwistedDiagonal.lean` through the `RiemannZeta.lean` import closure, alongside `RiemannZeta/Audit.lean` and the two retained anonymous examples `TestExp.lean` and `test_separated.lean`. No retained Lean file currently needs an integrity repair; the remaining work is theorem completion in the groups below. Historical deletion records remain evidence about earlier states, not descriptions of the present tree.

| Rank | File or group | Required repair | Estimated difficulty |
|---:|---|---|---|
| 1 | ~~`RiemannZeta/GuthMaynard/TestAxiom.lean`~~ | **Completed 8 August 2026:** deleted the isolated file containing the deliberately false axiom and its dependent theorem. | Trivial—complete |
| 2 | ~~Auxiliary tests, scratch files, tombstones, and side-effect utilities~~ | **Completed after re-audit 8 August 2026:** removed 30 unreferenced obsolete Lean files, preserved the useful power-expansion idea as Markdown, and directly elaborated both retained anonymous examples without warnings. | Easy–moderate—complete |
| 3 | ~~`TestExp.lean`, `test_separated.lean`, `test_zeta.lean`~~ | **Completed 8 August 2026:** converted the exponential and separation checks into complete examples and deleted the unproved Euler-product experiment. | Easy—complete |
| 4 | ~~`RiemannZeta/GuthMaynard/test_fourier.lean`, `RiemannZeta/GuthMaynard/ZeroCountScratch.lean`~~ | **Completed 8 August 2026:** deleted the isolated zero-valued Fourier toy and unused module-level symmetry assumption. | Easy—complete |
| 5 | ~~`RiemannZeta/GuthMaynard/InghamBound.lean`~~ | **Completed 8 August 2026:** removed the unused Huxley premise so the statement matches the two-bound proof; deleted the stale, unreferenced `ScratchTransfer.lean` duplicate. | Easy—complete |
| 6 | ~~`RiemannZeta/Audit.lean`~~ | **Completed for all named public theorems in the current tree:** the explicit and discovered sets synchronize at 1296/1296, every existing theorem has only the permitted logical dependencies, and the separate completion gate reports seven absent output names. | Easy–moderate—complete |
| 7 | ~~`RiemannZeta.lean`~~ | **Completed and maintained:** the root reaches all 79 subordinate production modules, including the six vendored PNT+ files and the current #15/#18/#19 modules. The deleted false `Decoupling` module is not imported. | Easy—complete |
| 8 | ~~Warning-producing files and `run_lake_build.bat`~~ | **Completed and maintained:** all five Lean stages—including both retained examples—fail on any `warning:` diagnostic; integrity scans use `--no-ignore`; current builds and scans are warning-free, while the output gate correctly makes stage 5 and the overall runner fail. | Easy–moderate—complete |
| 9 | ~~`RiemannZeta/GuthMaynard/ZeroDetector.lean`~~ | **Completed after re-audit 8 August 2026:** proved full-divisor-cardinality bounds independent of `T` and derived `UniformDetectorCoeffBoundProp` from the exact classical `DivisorCountBoundProp`; #17 later discharged that input. | Moderate—integrity/source reduction complete; arithmetic input now proved |
| 10 | ~~`RiemannZeta/GuthMaynard/PolynomialPowers.lean`~~ | **Finite/conditional layer completed:** `polynomial_power_identity` proves the exact `powCoeff` expansion, and `powCoeff_bound_of_divisor_and_factorization` exposes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly. #17 later discharged both inputs. | Moderate–hard—finite/conditional layer complete; arithmetic inputs now proved |
| 11 | ~~`RiemannZeta/GuthMaynard/MeanValue.lean`, `MeanValueProof.lean`~~ | **Completed 8 August 2026:** repaired the interval convention to `[0,T]`, proved `MontgomeryMeanValue`, and specialized the Halász–Montgomery consequence without a premise. | Hard—complete |
| 12 | ~~`RiemannZeta/GuthMaynard/HalaszMontgomery.lean`, `ZeroDetector.lean`, and `TypeIIZeros.lean`~~ | **Conditional/concrete layer completed:** coverage is eventual in height and source-range restricted; the generic count is identified with the concrete analytic-multiplicity residual count; and the concrete `ResidualZeroBoundProp` follows from three explicit analytic inputs. #18 has proved coverage and the fourth-moment reduction; only the twisted fourth moment remains Goal C work. | Very hard—conditional/concrete layer complete |
| ~~13~~ | ~~`RiemannZeta/GuthMaynard/ExtractSeparated.lean`, with supporting changes in `DirichletPolynomial.lean`, `Separated.lean`, `ZeroDetector.lean`, `ZeroCount.lean`, and `BetaDependence.lean`~~ | **Completed unconditionally 8 August 2026:** the unit-zero multiplicity theorem, beta removal, shifted-bin covering, raw loss accounting, `[0,3T]` translation, coefficient phase twisting with norm preservation, and pure epsilon-power normalization are kernel-checked in `extractSeparated_native`. | Very hard—complete |
| ~~14~~ | ~~`RiemannZeta/GuthMaynard/Transfer.lean` and prerequisites~~ | **Completed at the primitive-input conditional boundary 8 August 2026:** F-01 through F-10, the central Type-I estimate, dyadic-to-global reduction, residual assembly, and high-`σ` branch are kernel-checked. | Very hard—complete |
| 15 | `TypeIFiniteWindow.lean`, `FiniteDensityEndpoint.lean`, `ClassicalDichotomy.lean`, and the finite-density consumers | Actual-`X` Type-II powering and the normalized direct/powered/Weyl Type-I package are complete. Add the multiplicity-aware branch-to-slab reduction and endpoints. | Very hard—open; `FR` is the next finite consumer |
| ~~16~~ | ~~Beta removal~~ | Completed by the rational Phragmén–Lindelöf implementation recorded above. | Very hard—complete |
| ~~17~~ | ~~Arithmetic coefficient bounds~~ | Completed by `divisorCountBound_native`, `factorizationCountBound_native`, and `powCoeffBound_native`, as recorded above. | Very hard—complete |
| 18 | `TwistedMoment.lean`, `TwistedDiagonal.lean`, `SmoothZetaAFE.lean`, `GammaPairBound.lean`, `QuadraticDivisor.lean`, `Estermann.lean`, `DivisorVoronoi.lean`, and `TypeIIZeros.lean` | Native Appendix C coverage and the complete smooth `ζ²` AFE/diagonal package are proved. The exact finite DFI source-entry, Kloosterman L2 language, periodic Estermann continuation and explicit-hypothesis Mellin–Barnes Voronoi contour theorem are also proved. Source-weight tail discharge, delta localization, quantitative dual transforms, DFI error, twisted-moment, and one-premise Goal C outputs remain. | Extreme—in progress; exact contour layer complete, quantitative DFI core open |
| 19 | `LargeValuesLocalization.lean`, `LargeValuesMatrix.lean`, `LargeValuesPoisson.lean`, `LargeValuesCubic.lean`, `LargeValuesReflection.lean`, and `LargeValues.lean` | The published interval convention, exact three-piece source-to-smooth localization, matrix entry theorem, trace/Poisson, exact cubic split, `S₁`, finite signed-mode identities, arbitrary Mellin decay, cancellation-preserving aggregate bounds, and pointwise core `T₀⁻¹ᐟ²` estimates are kernel-checked. Missing are the measurable core/tail and complete summed-frequency quantitative Lemma 6.2 conclusion, Heath–Brown, `S₂`, energy/`S₃`, affine/GCD theorems, native large values, and transfers. | Hardest overall; quantitative reflection and source theorems precede the later packages |

### Current Actionable Files Ordered by Estimated Difficulty

| Rank | Existing file(s) to change first | Exact next proof boundary | Assessment |
|---:|---|---|---|
| ~~1~~ | `RiemannZeta/GuthMaynard/TypeIICoverage.lean`, `TypeIIContour.lean` | `typeIContourTypeIICoverOn_native`. | **Complete:** full Appendix C contour shift, tails, detector decomposition, and dichotomy assembly. |
| ~~1~~ | `RiemannZeta/GuthMaynard/GammaPairBound.lean`, `SmoothZetaAFE.lean`, and pinned PNT+ Gamma infrastructure | **Complete:** finite Euler products give the paired Gamma estimate, the exact coefficientwise divisor-contour factor is identified, and the strength-100 Gaussian gives uniform `exp (-84*u^2) * (2+8*u^2)^4` decay. | Hard–extreme—complete; DFI remains separate. |
| ~~2~~ | `FiniteDensityEndpoint.lean`, `ClassicalDichotomy.lean`, and #17 coefficient lemmas | **Complete:** arbitrary-`X` normalization, powering, dyadic extraction, and unrestricted MHH. | Kernel-checked. |
| ~~3~~ | `TypeIFiniteEstimates.lean`, `FiniteScaleAssembly.lean`, `TypeIFiniteWindow.lean`, and a finite branch consumer | Join the actual dichotomy Type-I witness to the correctly normalized cardinality theorem and every endpoint scale branch. | **Complete:** `actual_typeI_branch_resolution_native` closes `ZR`; `FR` remains separate. |
| 3 | A finite density consumer over `ClassicalDichotomy.lean` | Combine completed Type-I and actual-`X` Type-II bounds with multiplicity and certificates. | Very hard; `FR`, after `IIE`. |
| 5 | `QuadraticDivisor.lean`, `Estermann.lean`, `DivisorVoronoi.lean`, then the DFI quantitative consumer and twisted-moment consumer | Discharge the source-weight contour hypotheses, prove delta localization and quantitative dual-transform estimates, derive DFI Theorem 1's optimized error, and prove `twistedZetaFourthMoment_native`. | Extreme; exact finite/Fourier and contour/Voronoi layers complete, quantitative DFI error absent. |
| 6 | Subsequent #19 modules | Native Heath–Brown, `S₂`, then energy/affine/refined-`S₃`. | Very hard. |
| 7 | New #19 Heath–Brown, affine, energy, and GCD/spacing modules, then `LargeValues.lean` | Remaining `S₂/S₃` chain and `guthMaynardLargeValues_native`. | Hardest. |

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

1. **Completed for the production perimeter and kept synchronized through 12 August 2026:** created an explicit, synchronization-checked list, currently containing 1296 exported source-level theorems.
2. **Completed 8 August 2026:** imported every intended production module into the audit after making the three previously omitted modules compilable.
3. **Completed 8 August 2026:** replaced name-based classification with transitive `Lean.collectAxioms` inspection.
4. **Completed 8 August 2026:** the audit exits nonzero and identifies every audited theorem with a `sorryAx` or project-specific axiom dependency.
5. **Completed 8 August 2026:** removed the unused Huxley premise from the canonical combined-transfer signature, corrected the documentation, and deleted the stale, unreferenced `ScratchTransfer.lean` duplicate.
6. **Completed 8 August 2026:** extended the root import graph to all intended production modules after their compilation repairs.
7. **Completed during reopened #2:** removed every obsolete auxiliary named declaration. The two retained auxiliary files contain only anonymous examples and both elaborate directly.

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
- `RiemannZeta/GuthMaynard/LargeValuesDefinitions.lean`
- `RiemannZeta/GuthMaynard/LargeValuesMatrix.lean`
- `RiemannZeta/GuthMaynard/TraceDispersion.lean`
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
10. **Goal C boundary after completed #14 integration:** the transfer consumes `DivisorCountBoundProp` and `FactorizationCountBoundProp` directly; completed #17 now supplies both propositions.

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

1. **#15 first pass:** finish the zeta analytic foundations and local unit-height Jensen bound.
2. **#16:** prove the beta-removal theorem after replacing the malformed Fourier/contour interfaces.
3. **#17 — completed:** prove the divisor-count and factorization-count inputs; the Montgomery mean-value input was already complete. `ArithmeticCoefficients.lean` now supplies all three required native outputs.
4. **#15 second pass:** retain the proved finite Type-I estimates, then finish smooth extraction, stationary reflection, reflected deweighting, the actual-`X` Type-II powered MHH application, range resolution, branch-to-slab consumer, and endpoints. Do not cross out #15 before both endpoint theorems exist.
5. **#18:** repair the coverage range, prove uniform vertical Gamma decay and contour integrability, Appendix C coverage, scaled separated extraction and the concrete fourth-moment reduction, the generic Hughes–Young-range upper bound with its quadratic-divisor input, and a specialization whose only premise is `GuthMaynardLargeValues`.

**Exit evidence:**

- the transfer theorem assumes only the Guth–Maynard large-values theorem;
- every removed hypothesis is replaced by a kernel-checked theorem; and
- Goal C is stated accurately in all documentation.

### Phase 6: Formalize the large-values theorem—Goal D

**Files:**

- `RiemannZeta/GuthMaynard/LargeValuesDefinitions.lean`
- `RiemannZeta/GuthMaynard/LargeValuesMatrix.lean`
- `RiemannZeta/GuthMaynard/TraceDispersion.lean`
- `RiemannZeta/GuthMaynard/LargeValues.lean`
- additional focused modules introduced only when they represent real mathematical responsibilities

**Required actions—Shitlist #19:**

1. Delete the false interval-free incidence proposition, the off-by-one decoupling contract, both project axioms, and their dependent historical wrapper; Guth–Maynard does not use this decoupling model.
2. Introduce source-facing finite interfaces for the smooth polynomial, sampling matrix, singular-value trace-cube reduction, Poisson correlations, and tolerance-one approximate energy.
3. With the source localization, cubic trace split, `S₁`, and exact reflection identities complete, first prove quantitative Lemma 6.2, then prove the Heath–Brown difference-set mean-square input, `S₂`, the affine-transformation estimates, `S₃`, and the GCD/spacing energy assembly.
4. Assemble the exact `GuthMaynardLargeValues` statement used by Central Type I and the transfer.
5. Instantiate the #18 Goal C theorem and the combined transfer, then close all audit, warning, and runner gates.

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
| Remaining obstruction | At the #10 checkpoint, `DivisorCountBoundProp` and `FactorizationCountBoundProp` remained explicit Goal C inputs. Completed #17 now discharges both and exports `powCoeffBound_native`. |

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
| Honest analytic boundary | At the #12 repair, the coverage boundary was corrected to `TypeIContourTypeIICoverOnProp (7/10)` while coverage and `TwistedZetaFourthMomentProp` remained explicit inputs. The later #18 work now proves `typeIContourTypeIICoverOn_native` and `typeIIFourthMomentReduction_native`; only `TwistedZetaFourthMomentProp` remains unproved in this chain. |
| Integrity impact | Deleted the original Type II postulate, misleading wrapper, and conclusion-shaped target input without replacement. The concrete bridge uses Mathlib-backed zeta-zero finiteness and introduces no axiom, admitted proof, hidden target hypothesis, or vacuous theorem. |
| Audit impact | The synchronized audit now contains 132 explicit and 132 discovered production theorems. The three new concrete bridge theorems pass with only `propext`, `Classical.choice`, and `Quot.sound`; the same 6 unrelated forbidden-dependency failures and 14 direct project axioms remain. |
| Verification | The focused `TypeIIZeros` build succeeds with zero Lean warnings. The principal runner logged to `logs/overall_proof_20260808_121046.log`: stages 1–4 passed warning-free; the transitive audit synchronized 132/132 declarations and passed the corrected generic theorems plus all three concrete bridge theorems. Integrity scans found no admitted-proof or unsafe-bypass material and correctly reported 14 direct project axioms. The same 6 unrelated audit failures remain, so the overall exit code is honestly 1. |
| Remaining obstruction | Shitlist #12 is complete at the honest conditional/concrete boundary. Goal C now has native source coverage and Appendix C reduction; it must still prove the twisted fourth moment independently. #12 makes no unconditional claim for Maynard–Pratt Lemma 24. |

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
| Honest analytic boundary at the #13 iteration | `DetectorBetaShiftProp` and `LocalZeroMultiplicityBoundProp` were then unproved proposition specifications. Later #15 and #16 work discharged both and produced `extractSeparated_native`. |

### Critical Re-Audit and Reopened Plan: Shitlist #13

The implementation record above remains accurate history, but the stronger completion language is superseded by this interface audit.

| Field | Current finding and required treatment |
|---|---|
| Current verdict | This historical finite layer was later superseded by the completed normalized #13 wrapper. The #15 unit-zero theorem and #16 beta-removal theorem now discharge both premises, so `extractSeparated_native` is unconditional. |
| Local-input defect | `LocalZeroMultiplicityBoundProp` quantifies over every displacement function and directly returns the exact multiplicity sum in each shifted, scale-filtered unit bin. This packages the pullback and finite interval-covering step that the pre-implementation plan assigned to #13. Replace it with a uniform multiplicity-weighted bound for ordinary unit intervals of zeta zeros. |
| Required local deduction | Prove that a shifted unit bin with displacement at most `H` pulls back into `[z-H,z+1+H]`; cover that interval by at most `2⌈H⌉+3` ordinary unit bins; restrict to the selected Type-I scale; and derive an `O((H+1) log T)` shifted occupancy bound. This finite deduction belongs in `ExtractSeparated.lean`, not in an analytic hypothesis. |
| Beta-removal boundary | At this planning stage `DetectorBetaShiftProp` was the explicit input consumed by #13. #16 later discharged it by rational Phragmén–Lindelöf localization and deleted the malformed interfaces. |
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
| Audit impact | At the #13 iteration, eight public theorems were added and all passed. The later #15 foundation audit now supersedes these historical counts: 199/199 declarations, 3 dependency failures, and 10 direct project axioms. |
| Verification | Focused `DirichletPolynomial` and `ExtractSeparated` builds and the full default build completed with zero Lean warnings. `run_lake_build.bat --no-pause` logged to `logs/overall_proof_20260808_124518.log`: stages 1–4 passed warning-free, the audit synchronized 140/140 and passed every #13 theorem, integrity scans found no admitted-proof or unsafe-bypass material, and the axiom scan correctly reported 14 existing declarations. The same 6 unrelated audit failures remain, so the overall exit code is honestly 1. |
| Later analytic closure | #15 proved `LocalZeroMultiplicityBoundProp`; #16 proved `DetectorBetaShiftProp`; `extractSeparated_native` is now the unconditional Type-I extraction theorem. |

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
| Coverage | At that iteration the tree contained 44 Lean files and a 41-file production graph. The current superseding inventory is 83 Lean files: an 80-file root closure, `Audit.lean`, and two separately executed examples. No retained Lean file is outside the human-facing evaluation. |
| Verification | `cmd /c run_lake_build.bat --no-pause` logged to `logs/overall_proof_20260808_112057.log`. Stages 1–4 passed with zero Lean warnings. Stage 5 synchronized 123 explicit and 123 discovered theorems and failed on the same 6 project-axiom dependencies. Integrity scans found no admitted-proof or unsafe-bypass material and correctly failed on 14 direct project axioms. Overall exit code was honestly `1`; the log contains no `warning:` diagnostic. |
| Documentation | Updated runner coverage in `README.md` and `Paper_Riemann_Zeta.md`, corrected the paper's stale expected audit count from 17 to 6, and synchronized both agenda documents. |
| Remaining obstruction at that iteration | #8 had no remaining warning or retained-file coverage defect. The superseding 12 August audit has 1296/1296 passes and zero direct project axioms. |

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
| Honest boundary | At the #9 checkpoint, `DivisorCountBoundProp` was an explicit classical theorem specification. Completed #17 now proves it as `divisorCountBound_native`, so the source-uniform detector estimate specializes unconditionally. |

### Source and Interface Audit: Shitlist #14

At the pre-implementation audit, `Transfer.lean` was circular and supplied no part of the Section 13.1 deduction. The implementation results below supersede that baseline.

| F-step | Current status | Required #14 treatment |
|---|---|---|
| F-01 dyadic zero reduction | **Complete.** Zeta conjugation, analytic-order preservation, negative/positive rectangle equality, finite low-height control, and the eventual dyadic reduction are proved. | Implemented in `ZeroCount.lean` and `DyadicTransfer.lean`; no provisional parameter remains. |
| F-02 detector coefficients | **Complete unconditionally at the arithmetic boundary.** The truncated Möbius detector, admissible scales, and source-uniform coefficient bound are consumed by the central proof. | `divisorCountBound_native` discharges the former primitive arithmetic input. |
| F-03 Type I/Type II | **Complete conditionally.** The exact partition is assembled and the residual bound is derived internally. | The interface exposes three source-facing Type-II inputs. Native theorems discharge coverage and the fourth-moment reduction; only the twisted fourth moment remains open. |
| F-04 beta removal | **Complete.** `DetectorBetaShiftProp` is discharged by `beta_dependence_removal`. | #16 deleted the malformed declarations and proved the proposition by rational Phragmén–Lindelöf localization. |
| F-05 separated extraction | **Complete unconditionally.** #13's normalized extraction is invoked with native beta-shift and ordinary unit-zero theorems. | `extractSeparated_native` discharges the complete target. |
| F-06 normalize coefficients | **Complete.** Exact identities, restricted globally unit-bounded coefficients, threshold inversion, and uniform coefficient constants are integrated. | No #14 work remains. |
| F-07 polynomial powers | **Complete.** The block split and simultaneous pigeonhole feed the central proof, with all bounded losses absorbed. | No #14 work remains. |
| F-08 choose `k` | **Complete.** Both sides of equation (13.1), `2 ≤ k ≤ 101`, and detector-scale control are consumed. | No #14 work remains. |
| F-09 large-values case | **Complete conditionally.** The normalized fixed block is passed to the repaired large-values input and every loss is absorbed. | `GuthMaynardLargeValues` remains an explicit primitive analytic input and is the sole unresolved Central Type-I premise. |
| F-10 mean-value case | **Complete unconditionally at the input boundary.** The normalized-block mean-value case and its exponent comparison are assembled. | `montgomery_mean_value_native` discharges `MontgomeryMeanValue`. |

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
| Audit | At completion of #14, the synchronized audit checked 194 public theorems and failed on four project-axiom-dependent declarations. The later #15 foundation pass supersedes these historical counts. |
| Principal evaluation | At completion of #14, `run_lake_build.bat --no-pause` logged its run to `logs/overall_proof_20260808_154845.log` and exited `1`. The current evidence is the later #15 run recorded above. |
| Honest remaining boundary | #14 is **complete conditionally, not unconditionally**. Its signature retains ten primitive inputs, but native theorems discharge seven; the three unresolved inputs are Guth–Maynard large values, Huxley, and the twisted fourth moment. `TypeIPositiveSlabBoundProp` is a derived internal intermediate, and `DyadicToGlobalZeroCountProp` has been deleted. |

### Re-Audit Correction to Historical Completion Records

The iteration records above remain useful accounts of what each repair changed at that time, but their words “deleted,” “complete,” and “every” must be read subject to the highly critical re-audit near the top of this file. In particular:

- #2's initially incomplete deletion claim has now been repaired: every obsolete/tombstone path is absent and both retained examples elaborate cleanly;
- #6's synchronized transitive audit now covers every named public theorem in the cleaned tree; the two auxiliary declarations are anonymous examples;
- #8's initially production-only warning gate now covers both retained examples and uses ignore-resistant integrity scans;
- #9 derives the source-uniform detector estimate from `DivisorCountBoundProp`, and completed #17 now supplies that proposition via `divisorCountBound_native`;
- #10 proves the structural-power/explicit-coefficient identity and exposes the two arithmetic inputs directly; completed #17 discharges them and exports `powCoeffBound_native`;
- #12 now reaches the concrete `ResidualZeroBoundProp` from honest source-facing inputs; those hard analytic inputs remain open. #13's conditional/normalized extraction layer is now fully specialized by the proved #15 unit-zero and #16 beta-removal inputs.
- #14 removes the circular conclusion-equivalent assumption and completes the primitive-input conditional transfer; six of its ten source-facing hypotheses are now discharged, and the four remaining hypotheses are assigned to #15, #18, and #19.

These corrections do not invalidate the kernel-checked lemmas. They narrow the completion claims to exactly what those lemmas establish.

## Current Priority

Exactly three items remain, in Shitlist-number order:

1. **#15 — Classical finite zero-density endpoints (in progress).** The dichotomy, common extraction, exact powering infrastructure, arbitrary-`X` Type-II application, coefficient growth, endpoint arithmetic, terminal Type-I estimate, smoothing, medium B-process, Mellin reflection, deweighting, and the normalized direct/powered/Weyl Type-I branch package are proved. The corrected scale is `τ=log_N T`, satisfying `N^τ=T`, and MHH is applied at the correct threshold `N^σ V`. Both `IIE` and `ZR` are complete; their next common consumer is `FR → ZD`. This classical package is distinct from #19's `GuthMaynardLargeValues`.
2. **#18 — Type II and Goal C integration.** Source-range Maynard–Pratt coverage, uniform vertical Gamma decay, contour integrability, scaled extraction, the concrete fourth-moment reduction, completed-`ζ²` contour AFE, coefficientwise Hughes–Young Gamma-ratio weight, and weighted-diagonal reduction are complete. Prove the genuine quadratic-divisor off-diagonal theorem, assemble the generic Hughes–Young-range twisted moment, specialize it to `M²`, then reduce the public zero-density theorem to the single premise `GuthMaynardLargeValues` after #15 supplies Huxley.
3. **#19 — Large values and final integration.** The false decoupling contracts are deleted; the source definitions and exact source-to-matrix localization, sampling matrix, trace-dispersion algebra, Fourier/Poisson foundations, first- and cubic-trace expansions, Proposition 5.1 for `S₁`, uniform two-parameter Fourier decay, exact reflection identities, and cancellation-preserving signed aggregate bounds are proved. Next complete quantitative Lemma 6.2, then prove Heath–Brown, affine-transformation, approximate-energy, `S₂/S₃`, and the GCD/spacing chain; prove `GuthMaynardLargeValues`; derive the concrete Guth–Maynard and combined zero-density theorems; and make the principal runner pass.

These three tasks are exhaustive. No fourth mathematical cleanup item is deferred beyond them. When #15, #18, and #19 meet their stated completion tests, the overall research agenda is complete.
