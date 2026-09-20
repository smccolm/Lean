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

Implementation status note (20 September 2026): the supporting `power-energy`
requirement in EPZAE-34 has a kernel-checked counterexample. See
`Tao-Trudgian-Yang Energy Powering Obstruction.md`. The source statement and
this completion contract remain unchanged pending owner authorization of a
documented replacement. Do not attempt to discharge it with an assumption,
an altered double-zeta-sum normalization, or a silently weakened conclusion.

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
  energy powering, and the Heath--Brown relation; and
- exact rational/polyhedral optimization certificates for every final
  envelope and interval split.

An upstream theorem may be imported only after its quantifiers, interval
conventions, coefficient normalization, sign convention, epsilon losses, and
constant dependencies are matched by a proved bridge.

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
  GuthMaynardBridge.lean
  BourgainLargeValues.lean
  ZetaLargeValues.lean
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
  HeathBrownEnergyRelation.lean
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
    and every piecewise crossover.

Until then, use the status terms **planned**, **defined/stated**,
**conditionally proved**, or **kernel-checked helper** as appropriate. Do not
say the paper or any advertised output is formalized.
