# Whole-proof operational goal prompt

## Objective

Produce a reproducible, kernel-checked Lean 4 formalization of every new
mathematical output in Tao--Trudgian--Yang, arXiv `2501.16779v1`, while reusing
the live ANTEDB Lean foundations and the completed local Guth--Maynard
formalization where their exact interfaces agree.

The work is complete only when the source statements, Lean statements,
dependency graph, audit, documentation, and build runner agree. Python
optimization, numerical checks, and prose derivations may generate
certificates, but they may not serve as proof oracles.

## Frozen public theorem contract

Authorized supporting-lemma correction (20 September 2026): preserve the
kernel-checked counterexample to printed `power-energy` (Lemma 62), and
replace EPZAE-34 with the cardinality/energy two-witness theorem specified
below and in `Tao-Trudgian-Yang Energy Powering Repair.md`. Drop the false
`s' ≤ s/k` restrictions and the third, `s`-preserving witness. This is an
explicit correction to a supporting lemma, not to the advertised outputs.
Keep the original paper, the definitions of `S` and `E`, and the
counterexample unchanged. All public theorem statements below remain frozen.

The release layer must expose source-facing theorems for the following labels.

### Exponent-pair output

`new-exp-pair` must prove that each of the following is an exponent pair:

```text
(89/1282, 997/1282)
(652397/9713986, 7599781/9713986)
(10769/351096, 609317/702192)
(89/3478, 15327/17390)
```

The predicate must unfold to the paper's analytic exponential-sum estimate;
membership in a finite list or a convex polygon is not by itself the intended
claim.

### Zero-density outputs

With `A(sigma)` interpreted through the paper's zero-count convention and
epsilon-loss asymptotics, prove:

1. `hb-density2`:
   `A(sigma) <= 3 / (10*sigma - 7)` for `7/10 < sigma <= 1`.
2. `bourgain-density-improved`:
   `A(sigma) <= max (2/(9*sigma-6)) (9/(8*(2*sigma-1)))`
   for `17/22 <= sigma <= 4/5`, with the two stated subranges certified.
3. `bourgain-zero-density-optimized`: the exact eight-piece rational bound
   recorded in the crosswalk for `3/4 < sigma < 1`.

The final theorem chain must consume actual zeta zeros with multiplicity and
must prove the bridge from the local project's rectangle convention to the
paper's `Re rho >= sigma`, `|Im rho| <= T` convention.

### Additive-energy output

`Add-est` must prove all nine source clauses for
`A*(sigma) * (1-sigma)`, over their exact closed intervals and with the exact
maxima of rational functions shown in the paper. Additive energy must count
the intended approximate additive relations at unit tolerance, including
multiplicity and the paper's epsilon-loss normalization.

## Supporting source results in scope

The release outputs require faithful formal versions of:

- cheap asymptotic notation and automatic uniformity;
- model phase functions and `beta(alpha)`;
- exponent pairs, their convexity, A/B/C processes, the Sargos D-process, and
  beta/exponent-pair duality;
- the Heath--Brown derivative bound and all beta-table segments actually used
  by the four new pairs;
- zeta growth and the exponent-pair-to-`mu` bridge;
- large-value patterns, `LV`, zeta large values `LV_zeta`, subdivision,
  powering, and the cited classical/Guth--Maynard/Bourgain estimates;
- zero-density exponents and the Type I/Type II transfer from large values;
- the Bourgain zero-density theorem and its admissibility side conditions;
- additive energy, `LV*`, `LV*_zeta`, the five-dimensional energy regions,
  the corrected cardinality/energy powering theorem, and the Heath--Brown
  relation; and
- exact rational/polyhedral optimization certificates for every final
  envelope and interval split.

An upstream theorem may be imported only after its quantifiers, interval
conventions, coefficient normalization, sign convention, epsilon losses, and
constant dependencies are matched by a proved bridge.

### Corrected EPZAE-34 contract

Define `E₄(σ,τ,ρ,e) := ∃ s, E(σ,τ,ρ,e,s)`. For every fixed integer
`k ≥ 1` and every `E₄(σ,τ,ρ,e)`, prove:

```text
∃ eCard, E₄(σ, τ/k, ρ/k, eCard) ∧ eCard ≤ e/k;
∃ rEnergy, E₄(σ, τ/k, rEnergy, e/k) ∧ rEnergy ≤ ρ/k.
```

These are two potentially different witnesses. Their existential fifth
coordinates have no asserted relation to the input `s` or to `s/k`.
The full Lean target is `CorrectedCardinalityEnergyPowering`, now proved by
`correctedCardinalityEnergyPowering` in `CorrectedEnergyPowering.lean`.
Maintain that complete proof from actual powered Dirichlet polynomials,
uniform coefficient normalization, finite cardinality/energy selection,
and coordinate-preserving subsequence limits. The target's proposition
definition alone is not proof evidence; neither witness may be assumed.

Use the cardinality witness for large-value constraints and the energy
witness for the Heath--Brown relation, whose right side is nondecreasing
in cardinality and independent of `s`. Feed those justified constraints
into exact energy optimization and the nine unchanged `Add-est` clauses.

EPZAE-35 is now proved by `InLargeValueEnergyRegion.heathBrown_relation`;
`InCardinalityEnergyRegion.heathBrown_powered` composes the two proved
inputs without a separate analytic hypothesis. Maintain its exact source
signature and full `τ ≥ 0` domain. The finite derivation uses the native
second and fourth moments, with proved reflection, support, energy-count,
constant-dependency, and height-padding bridges. It does not use the
mismatched `N` factor in the archived `hbt` proof. The small-height
three-branch constraint and its powered consumer are available for EPZAE-36;
their existence does not complete any final projection or `Add-est` clause.
Keep these modules, their explicit audits and semantic regressions covered
by `run_tao_trudgian_yang_build.bat`, updating its PowerShell inventory and
the root imports whenever this proof chain changes.
Do not infer arbitrary polytope closure or use any scaled `s` constraint.
Keep `energyPowering_source_counterexample` as a permanent audited regression.

The clause-(i) general intermediate `imphb-lver-ineq` is now proved by
`InLargeValueEnergyRegion.energyClauseOneGeneral_lower_piece` and
`InLargeValueEnergyRegion.energyClauseOneGeneral_upper_piece`, with exact
range `[8σ-4,2(8σ-4)]`, closed crossover `σ=4/5`, and full upper endpoint
`σ=5/6`. `energyClauseOneGeneral_uniform_bound` and
`energyClauseOneGeneral_high_height_bound` supply uniform general bounds.
Maintain their actual dependency on corrected cardinality witnesses at
`k,k+1` and the separate corrected energy witness. The Huxley energy-region
bridge is proved in `ClassicalLargeValueRegions`; the six-branch rational
certificate is in `EnergyClauseOneGeneral`. Do not infer arbitrary region
closure from these specific, proved deductions.

`energyClauseOne_of_zeta_range` still assumes the real zeta-energy bounds
on `[1,8σ-4)`. Prove those remaining inputs, or establish the source's
endpoint-two reduction and its zeta inputs, before claiming `Add-est (i)`.
The other eight final clauses remain in scope. Keep both new modules and
their endpoint/consumer regressions in `run_tao_trudgian_yang_build.bat`
coverage, updating the root imports, explicit audit, and runner inventory.

The clause-(i) zeta rational certificate is now proved in
`EnergyClauseOneZeta`: six affine branches, the exact `τ=4σ-1` height
transition, `σ=65/86` crossover, and domination by the advertised maximum.
Preserve its distinction from the analytic estimate. The actual-region
consumer derives its Huxley cap from corrected cardinality powering and
its Heath--Brown relation from the proved native analytic chain; it still
requires the independent twelfth-moment cardinality inequality.
`InZetaLargeValueEnergyRegion.rho_le_of_largeValueBound` proves the exact
uniform-LV-to-region bridge, and the resulting uniform zeta-energy bounds
remain conditional on `IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))`.

`energyClauseOne_of_twelfth_and_short_zeta` now gives end-to-end assembly
with precisely the remaining short zeta-energy input on `[1,2)` and the
twelfth-moment LV input on `[2,8σ-4)`. The latter now follows from the
dyadic critical-line moment through `ZetaTwelfthFromMoment` below.
Prove that moment and the short-zeta input, or prove the source
endpoint-two transfer together with the moment, before
claiming clause (i). The nearby Gafni--Tao `HeathBrownTwelfthStatement`
file contains a proposition and conditional consumers, not an importable
proof of the full twelfth-moment estimate. Do not treat it as an axiom or
completed analytic input. Keep `EnergyClauseOneZeta`, all named audits,
closed-endpoint regressions, and conditional signatures in
`run_tao_trudgian_yang_build.bat` coverage.

The critical-line, twelfth-power summation step of `add-bound (ii)` is now
proved in `ZetaMomentKernel` and `ZetaMomentTransfer` on the actual zeta
function and the source interval `[T/2,3T]`. `ZetaMomentAsymptotics` proves
logarithmic-loss absorption and dyadic/source-window normalization, with
a consumer on actual `ZetaLargeValuePattern` objects. Preserve the exact
physical `C^12 N^6` normalization and uniform height threshold.
The low-level finite consumer explicitly assumes pointwise entry and the
dyadic critical-line moment separately. Preserve that modular interface;
`ZetaPerronEntry` now discharges the pointwise premise and
`ZetaTwelfthFromMoment` proves the uniform epsilon--delta LV deduction.
The moment hypothesis itself remains open. A conditional deduction does
not discharge `twelfth-bound`.
Do not assume away a Perron residue, smoothing loss, or support endpoint.
Keep all three modules, their 21 named public audits, and ten semantic
regressions in the root imports and `run_tao_trudgian_yang_build.bat`
inventory; update the runner whenever this analytic chain changes.

The exact coefficient-one source identity is now proved in
`ZetaIntervalCutoff`, `ZetaMellinEntry`, `ZetaMellinContour`, and
`ZetaMellinShift`. Preserve the actual-pattern consumer
`ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin`: the original
sharp polynomial equals the whole critical-line zeta integral plus
`mellin cutoff (1-it)`. The cutoff equals the active indicator at every
integer; both endpoints, the negative phase, and the moving pole are exact.
The native smooth-test object is constructed from this cutoff. Boundary
integrability, horizontal decay, and the contour shift are proved, with
constants permitted to depend on the fixed cutoff and ordinate.

Quantitative Mellin bounds, source-window localization, and residue/tail
absorption are now proved in the six-module continuation below. Preserve
their actual dependencies; do not replace them by fixed-cutoff convergence
or an independently assumed entry estimate. Keep these four identity
modules, their
36 named public theorem audits, the explicit cutoff-constructor audit, and
ten semantic regressions in the root imports and
`run_tao_trudgian_yang_build.bat` inventory. Update and rerun that principal
runner whenever the analytic chain, audit, or production coverage changes.
The preserved Lemma 62 counterexample and all final publication contracts
remain unchanged.

The uniform continuation consists of `ZetaCutoffDerivatives`,
`ZetaMellinDerivative`, `ZetaMellinUniform`, `ZetaMellinLocalization`,
`ZetaPerronEntry`, and `ZetaTwelfthFromMoment`. For `j ≥ 1`,
the cutoff derivative integral is bounded independently of its endpoints,
and for `σ ≥ 1/2` the Mellin estimate is
`|M_w(σ+iu)| ≤ C_j(σ) N^(σ+j-1)/(1+|u|)^j`.
The omitted critical integral is at most
`120 C_4(1/2) N^(7/2)/T²`; the residue is at most
`C_4(1) N^4/(1+|t|)^4`. The actual-pattern `perron_entry` absorbs both
when `T ≥ N^(7/4)` and `V ≥ 2 zetaPerronError`.
`exists_zetaPerron_uniform_threshold` derives these physical conditions
from the source windows, uniformly for `σ ≥ 1/2`, `τ ≥ 2`, `δ ≤ 1/4`.

`zetaTwelfth_largeValueBound_of_dyadic` proves the full uniform
`IsZetaLargeValueBound σ τ (2τ-12(σ-1/2))` from the genuine dyadic
critical-line twelfth moment alone. Its constants and approximation
radius precede the actual pattern. No pointwise entry or cardinality
conclusion is an assumed input.
`energyClauseOne_of_dyadic_moment_and_short_zeta` composes this theorem
with corrected powering, Heath--Brown energy, and the exact optimizations.
Prove its two remaining inputs: the dyadic twelfth moment and short zeta
energy on `[1,2)` (or establish the source endpoint-two alternative).
Other source moment parameters, other eight energy clauses, and the
complete EPZAE-00--41 contract remain in scope.

Keep all six continuation modules, their 38 named public theorem audits,
the constructed derivative-test audit, and 14 regressions in root imports
and `run_tao_trudgian_yang_build.bat` coverage. Update and rerun that
runner as this chain changes. Neither a passing runner nor a conditional
moment consequence proves the missing moment or any final `Add-est` clause.

## Source and dependency boundary

1. Primary paper: arXiv `2501.16779v1`, submitted 28 January 2025.
2. Paper-time ANTEDB snapshot: commit
   `9953003a48f46fe8075ccf9534321f98f656032e`, the last repository commit before
   the arXiv v1 submission time.
3. Current ANTEDB Lean snapshot: commit
   `088040634e8300f87e80f431d8bdc38c42cc8e11`, dated 4 September 2026.
4. Completed local Guth--Maynard foundation: the canonical source under
   `../71 Guth-Maynard, 2026/`, pinned by that project's own reproduction
   manifest and release tag.
5. Mathlib and `PrimeNumberTheoremAnd`: use only through a single selected
   toolchain/dependency graph after EPZAE-01 is resolved.

The paper-time snapshot is for historical reproduction of the optimization.
The current snapshot is for reusable Lean foundations. Never blur the two.

## Proof architecture

The project has three layers:

1. **Analytic semantics:** definitions and theorems about phase functions,
   exponential sums, zeta zeros, large-value patterns, and energy.
2. **Exact finite certificates:** rational arithmetic, affine envelopes,
   polyhedra, projection witnesses, interval partitions, and maximum/minimum
   comparisons.
3. **Public assembly:** the new exponent-pair, zero-density, and energy
   endpoints, consuming both previous layers through explicit theorems.

The finite-certificate layer must not assert that an analytic hypothesis is
true. The analytic layer must not bury an optimization result inside a
definition. The public layer must consume the actual upstream objects.

## Proposed production modules

```text
TaoTrudgianYang2025/
  AsymptoticBridge.lean
  PhaseBridge.lean
  RationalCertificates.lean
  PiecewiseEnvelope.lean
  PolyhedralCertificates.lean
  ExponentPair.lean
  ExponentPairProcesses.lean
  SargosDProcess.lean
  BetaDuality.lean
  HeathBrownDerivative.lean
  BetaTable.lean
  NewExponentPairs.lean
  ZetaGrowth.lean
  LargeValuePattern.lean
  LargeValueExponent.lean
  LargeValueSubdivision.lean
  LargeValuePowering.lean
  ClassicalLargeValues.lean
  ClassicalLargeValueRegions.lean
  GuthMaynardBridge.lean
  BourgainLargeValues.lean
  ZetaLargeValues.lean
  ZetaMomentKernel.lean
  ZetaMomentTransfer.lean
  ZetaMomentAsymptotics.lean
  ZetaIntervalCutoff.lean
  ZetaMellinEntry.lean
  ZetaMellinContour.lean
  ZetaMellinShift.lean
  ZetaCutoffDerivatives.lean
  ZetaMellinDerivative.lean
  ZetaMellinUniform.lean
  ZetaMellinLocalization.lean
  ZetaPerronEntry.lean
  ZetaTwelfthFromMoment.lean
  ZeroCountBridge.lean
  ZeroDensityExponent.lean
  ZeroDensityTransfer.lean
  ImprovedHeathBrownDensity.lean
  ImprovedBourgainDensity.lean
  BourgainOptimizedDensity.lean
  AdditiveEnergy.lean
  EnergyExponents.lean
  ZeroEnergyMultiplicity.lean
  EnergyRegions.lean
  EnergyRegionAsymptotics.lean
  EnergyBoundAsymptotics.lean
  EnergyPowering.lean
  EnergyPoweredPatterns.lean
  EnergyPoweringLimits.lean
  CorrectedEnergyPowering.lean
  EnergyPoweringBounds.lean
  EnergyPoweringObstruction.lean
  EnergyLogLimits.lean
  HeathBrownEnergyFinite.lean
  HeathBrownEnergy.lean
  EnergyClauseOneGeneral.lean
  EnergyClauseOneZeta.lean
  EnergyCertificates.lean
  NewAdditiveEnergy.lean
  PublicTheorems.lean
  SemanticRegression.lean
  Audit.lean
```

Module names may be refined, but every dependency edge in the architecture
must remain visible and audited.

## Integrity contract

- No `sorry`, `admit`, project `axiom`, conclusion-shaped theorem parameter,
  `native_decide`, `implemented_by`, or unsafe proof bypass.
- No floating upstream branch, unpinned source archive, or silently updated
  generated certificate.
- Generated Lean certificate files must be deterministic, reviewed, imported
  by the root module, and checked by the kernel.
- Every public theorem must have an explicit transitive axiom audit.
- Every source convention bridge must have semantic regression examples at
  endpoints and overlap points.
- All production modules must be in the default import graph and principal
  runner.
- Zero project warnings and linter diagnostics are required for release.

## Principal verification runner

`run_tao_trudgian_yang_build.bat` is a required part of the project contract,
not optional convenience tooling. It must be updated in the same change
whenever the package layout, production-module inventory, toolchain,
dependency pins, generated certificates, semantic regressions, public theorem
list, or axiom audit changes.

The runner must resolve the project from its own location, preserve a complete
timestamped log, support `--no-pause`, and return a nonzero exit code if any
required inventory, source hash, build, warning, semantic, integrity, or audit
gate fails. While no Lean package exists it must say `PLANNING SCAFFOLD ONLY`
and must not describe its result as a Lean build. Once the package is
installed, a release claim requires executing this exact runner successfully;
a direct `lake build` alone is insufficient.

## Release acceptance gates

A release may be called complete only when all of the following pass:

1. all frozen public statements elaborate exactly;
2. all supporting analytic inputs are proved or imported through exact proved
   bridges, with no remaining mathematical theorem parameter;
3. every rational and polyhedral certificate is replayed in Lean;
4. paper-time Python reproduction agrees with the frozen endpoint tables;
5. the source hashes and both ANTEDB pins pass;
6. the repository-wide shortcut scans pass;
7. `run_tao_trudgian_yang_build.bat --no-pause` covers all production modules
   and completes with zero warnings;
8. the exhaustive dependency audit reports only permitted Lean/Mathlib logical
   axioms;
9. the architecture, checklist, crosswalk, research agenda, README, and
   reproduction manifest state the same completion status; and
10. semantic regression tests verify zero-count conventions, interval
    endpoints, multiplicity, epsilon-loss quantifiers, convex-hull membership,
    and every piecewise crossover;
11. the corrected two-witness powering theorem is proved on its full domain,
    and every powered optimization constraint is justified without the false
    fifth-coordinate scaling; and
12. the original Lemma 62 counterexample remains imported, explicitly audited,
    and covered by `run_tao_trudgian_yang_build.bat`, alongside the repaired
    theorem and its downstream consumers.

Until then, use the status terms **planned**, **defined/stated**,
**conditionally proved**, or **kernel-checked helper** as appropriate. Do not
say the paper or any advertised output is formalized.
