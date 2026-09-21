# Tooling record

The human-facing build runner now verifies the unified Lean package, frozen
ANTEDB source ledger, source archive hashes, forbidden-shortcut policy,
semantic regressions, and dynamic transitive axiom audit. It writes a complete
timestamped log and supports `--no-pause`.

Installed and planned tools:

- `verify_sources.ps1` -- recompute `Sources/SHA256SUMS.txt`, check archive
  commit metadata, and fail on missing/unlisted files;
- `generate_certificates.py` -- installed standard-library extractor that
  verifies the paper-time archive hash, extracts the four new-pair
  coordinates, reconstructs the eight exact Bourgain lower-envelope pieces,
  extracts and sign-normalizes all nine energy-clause tables from the frozen
  blueprint, and deterministically emits their kernel-consumed rational data
  module;
- `reproduce_paper_time.py` -- future tool to invoke pinned ANTEDB functions for the 2025
  outputs and serialize exact rational results;
- `emit_certificates.py` -- future full conversion of exact rational witnesses to deterministic
  Lean data, never theorem declarations;
- deterministic regeneration/diff checking for the installed generated module
  is integrated directly into the principal runner;
- `run_tao_trudgian_yang_build.ps1` -- installed warning-failing Lake build,
  semantic-regression, axiom-audit, integrity, inventory, and pin orchestrator;
  its inventory now rejects unlisted Lean files and production modules absent
  from the root imports, and its warning gate covers filename-prefixed Lean
  diagnostics as well as bare warning lines;
  the preserved `EnergyPoweringObstruction`, the `EnergyPowering` interfaces,
  and all three full-proof modules (`EnergyPoweredPatterns`,
  `EnergyPoweringLimits`, `CorrectedEnergyPowering`) are in its production
  inventory; both obstruction and repair reports are required project files;
  the downstream `EnergyPoweringBounds`, `EnergyLogLimits`,
  `HeathBrownEnergyFinite`, `HeathBrownEnergy`, `ClassicalLargeValueRegions`,
  `EnergyClauseOneGeneral`, `EnergyClauseOneZeta`, `ZetaMomentKernel`,
  `ZetaMomentTransfer`, `ZetaMomentAsymptotics`, `ZetaIntervalCutoff`,
  `ZetaMellinEntry`, `ZetaMellinContour`, and `ZetaMellinShift` modules are
  covered as well, including their exact source-entry audits and regressions;
  the uniform continuation (`ZetaCutoffDerivatives`, `ZetaMellinDerivative`,
  `ZetaMellinUniform`, `ZetaMellinLocalization`, `ZetaPerronEntry`,
  `ZetaTwelfthFromMoment`) is inventoried with 39 named public theorem
  audits, the derivative-test constructor audit, and 14 regressions;
  `ZetaShortPerron`, `ZetaShortPatterns`, and `EnergyClauseOneFromMoment`
  are also inventoried and root-imported. Their original 11 public theorems and
  the new short-height theorem in `ZetaTwelfthFromMoment` have 12 named
  audits; eight additional regressions check source boundaries and the
  final clause-(i) signature with only the genuine moment hypothesis;
  `ZetaLargeValueDiscreteness` and `ZetaPointwiseNonexistence` are now
  inventoried and root-imported too. Together with the new sharp-interval
  consumer in `ZetaShortPatterns`, they add 13 named theorem audits and
  eight regressions for infimum semantics, negative/zero/positive branches,
  and the genuine pointwise conclusion. The analytic twelfth moment is
  still open;
  the six modules `ZetaSquareContour`, `ZetaSquareContourShift`,
  `ZetaSquareDivisorKernel`, `ZetaSquareDivisorSeries`,
  `ZetaSquareSourceEntry`, and `ZetaSquareLocalMean` are inventoried and
  root-imported, with 47 named theorem audits and nine source-entry
  regressions. Coverage includes absolute integrated-norm summability
  and the actual local second-moment identity, not a claimed proof of
  the sharp Atkinson estimate;
  `ZetaSquareAveraging`, `ZetaSquareGaussianTail`, and
  `ZetaSquareGaussianTransform` are covered with 31 named theorem audits
  and nine additional regressions. These test physical Gaussian
  normalization, uniform logarithmic tails, and the closed quadratic
  transform boundary. Four further modules cover the proved actual
  digamma/Gamma-phase approximation and its whole-line Gaussian
  transform, now with 26 named audits and 12 phase regressions. Seven
  further modules prove the uniform actual shifted-Gamma/pole error,
  whole normalized contour bound and complete reflected divisor-source
  remainder. They add 44 public audits (plus the promoted Gamma derivative
  audit counted above) and 14 regressions. All seven are required by the
  same root import/inventory check. Nine more modules cover actual
  Mellin weights/reflection, signed source arguments, height variation,
  square-root coefficient mass, freezing, real zeta normalization and
  the complete quadratic Gaussian-source comparison. All 78 new public
  theorems have named audits; 20 additional regressions test zero
  coefficients, both closed height boundaries, the Gaussian scale
  boundary, factor two, and the full source-consumer quantifiers.
  Six further modules cover the exact finite frequency band, Gaussian
  shortening tail, uniform logarithmic scale/error assembly, actual
  local-second-moment consumer and physical divisor support. Their
  29 public theorem audits and 18 regressions are required by the same
  root/inventory gate. Eight further required modules construct the
  entire weight, actual smooth cutoff and native test, pay transition
  tails, and consume native Voronoi and literal Bessel bridges. Their
  43 public audits and 18 regressions are included in the same gates.
  Seven further modules prove literal K0 decay, full smooth support
  and mass, actual integrability, complete divisor summation, arbitrary
  power saving and source removal. All 29 public audits and 16
  regressions are included in the same root/inventory gates. Six further
  required modules insert the lattice phase, reapply native Voronoi,
  transfer the complete K0 bound and remove it from the actual physical
  source; exact carrier factorization and unique nondegenerate saddle
  calculus are also proved. All 40 public audits and 22 regressions
  are covered by the root and batch inventory. Nine further modules
  prove the actual amplitude variation, phase-adjusted main-integral
  bound and its physical-source removal, leaving the complete Y0 sum.
  Their 38 public audits and 20 regressions are included. Thirteen further
  required modules prove the literal Y0 ray and two-term expansion,
  sum its actual arithmetic remainder and consume the complete replacement
  in both physical zeta theorems. All 71 public audits and 25 regressions
  are covered by the same root and exact inventory gate. Ten further
  required modules prove uniform signed-carrier cancellation, actual
  power-weight bounds, exact four-carrier algebra and integrability,
  complete-series summability and both physical zeta consumers.
  Their 43 public audits and 24 regressions are included in the same
  root and backing inventory. The summand majorants are not used as
  summable arithmetic bounds. Four further modules and the generalized
  weighted-primitive helper prove the actual far-frequency gain,
  a summable majorant for the complete correction, its `C G`
  bound and leading-only physical zeta consumers. Their 19 new
  public audits and 16 regressions are in the same root/inventory
  gates. Leading stationary main values and sharper leading tails,
  sharp Atkinson inequality
  and genuine twelfth moment remain open, not assumed or excluded;
- `run_tao_trudgian_yang_build.bat` -- human-facing wrapper at the project root, with
  `--no-pause` support for agents and CI.

Every tool must print the exact input pins and preserve complete stdout/stderr
in the reproduction log. A tool exit code is not proof evidence unless its
output is consumed by a Lean kernel-checked certificate theorem.

## Second-order Fourier and finite-source coverage

The root and backing inventory now also cover fifteen modules from
`ZetaQuadraticGaussianSecondDerivative` through `AtkinsonFiniteSource`.
All 59 new public theorems have named audits, and 20 additional semantic
regressions check the actual amplitude, both signed source frequencies,
scale boundaries, zero coefficients and physical finite-source signatures.
This earlier tail gate proves C G for N≥T^10. The source-scale truncation
coverage below now supplies the shorter cutoff.
No incomplete module is excluded and no warning gate is weakened.

Keep `run_tao_trudgian_yang_build.bat` and its backing inventory
synchronized; run it and `run_lake_build.bat` after relevant changes.
The Reproduction Manifest records terminal verification evidence.

## Finite stationary reduction coverage

The root and exact PowerShell inventory now cover twelve additional modules
from `AtkinsonSaddleNormalization` through `AtkinsonStationaryPhysical`.
All 71 public theorems have named dependency audits. The 22 new regressions
cover both phases, (-1)^n, zero frequency/window, equal paired Gaussians,
closed G²=2T and n=T damping boundaries, both logarithmic-remainder
endpoints, natural derivative scale and actual full-source consumers.
Physical saddle-window containment is derived for 10000n≤T.

No source hash, dependency pin, exclusion or warning gate changed.
Keep `run_tao_trudgian_yang_build.bat` synchronized as this chain changes;
both it and `run_lake_build.bat` remain required. A passing runner checks
this finite-window scope. Fresnel evaluation is now proved below;
sharp Atkinson, the genuine twelfth moment and unconditional Add-est
outputs remain open.

## Fresnel evaluation and source power-saving coverage

Nine additional production modules, `ContinuousKernelPrimitive`,
`FresnelDampedTails`, `FresnelGaussianComparison`, `FresnelAbelLimit`,
`FresnelEvaluation`, `AtkinsonStationaryMain`,
`AtkinsonStationaryEvaluation`, `AtkinsonEvaluatedPhases` and
`AtkinsonStationaryPowerSaving`, are root-imported and explicitly
inventoried. All 35 public theorems have named audits; 16 regressions
check zero damping, branch choice, both signs, the closed power-balance
boundary and actual uniform source consumers.

No warning gate, source pin or exclusion changed. Maintain
`run_tao_trudgian_yang_build.bat` and its PowerShell inventory as this
chain grows; execute it and `run_lake_build.bat` after relevant changes.
A PASS verifies this per-carrier scope, not sharp summed stationary errors,
the twelfth moment or unconditional Add-est. See the Reproduction Manifest.

## Source-scale truncation coverage

The eleven modules from `AtkinsonSaddleSupport` through
`AtkinsonSourceCutoff` are explicitly inventoried and root-imported.
All 53 public theorems have named dependency audits.
The 22 new regressions cover actual endpoint vanishing, both slope signs,
closed G²=2T and frequency thresholds, literal ceiling values and the
uniform physical zeta and retained-index stationary consumers.

The runner now covers a complete source-scale leading-tail estimate,
not only the older N≥T^10 truncation. No warning gate, source pin or
exclusion changed. Maintain `run_tao_trudgian_yang_build.bat` and its
PowerShell inventory; execute it and `run_lake_build.bat` after relevant
changes. Kernel integrity does not close summed stationary errors,
the genuine twelfth moment or unconditional Add-est.

## Symmetric stationary summation coverage

The ten modules from `StationaryOddRemainder` through
`AtkinsonStationaryZetaSource` are root-imported and explicitly inventoried.
All 43 public theorems have named audits. The 24 regressions include
both amplitude endpoints, both logarithmic Taylor endpoints, the
small/large exponential-error branches, reversed odd-integral orientation,
closed radius balances, the empty divisor prefix, literal cutoff 18,
complete stationary-series support and exact uniform physical consumers.

Keep `run_tao_trudgian_yang_build.bat` and its backing PowerShell inventory
synchronized; execute it and `run_lake_build.bat` after relevant changes.
Their integrity verdict does not close smaller source widths, final main
assembly, the twelfth moment or unconditional Add-est. No diagnostic gate
or exclusion changed.

## Normalized main and partial-summation checkpoint

Five new modules, 30 named audits and 24 regressions derive the actual
common fourth-root coefficient from the original saddle power, curvature
and Bessel constants. Both signed main sums retain separate cutoff/Mellin
weights. Only the raw phase sums are conjugated.

The actual weights have a proved uniform bound
C G T^(-1/4) n^(-1/4) exp(-G²n/(12T)) on n≤T,
T,G,L>0, G²≤2T and 8L≤G. The exact Abel bound retains literal finite
weight differences. Both physical zeta consumers are linked to the same
explicit source cutoff and normalized mains. Errors remain
Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or Cδ,κ G log T above
T^(1/4+κ), within the original power-width range.

The continuation below proves uniform damped variation and the actual
source-block bound. Global dyadic/Gram assembly, smaller source widths or
a proved lower-value-range reduction, and the genuine twelfth moment remain open. No unconditional Add-est clause is closed.
The original counterexample and corrected powering/Heath–Brown chain
are unchanged. The exact `run_tao_trudgian_yang_build.bat` inventory
is synchronized; maintain it and rerun both principal evaluation scopes.

## Damped variation and source-block checkpoint

Six new modules, from `FiniteWeightVariation` through
`AtkinsonPhaseBlockBound`, have 36 named public audits and 24 regressions.
The actual Gaussian increments telescope against a decreasing real
envelope. Ordered actual saddle samples, the constructed Mellin bound,
both original cutoff transitions and the decreasing fourth-root
coefficient give uniform variation for both separate normalized weights.

`exists_finiteVariationBound_atkinsonMainWeights` bounds both the
supremum on indices 0..N and the adjacent-difference sum by
C G T^(-1/4) m^(-1/4) exp(-G²m/(12T)), for
T,G,L>0, G²≤2T, m>0 and 10000(m+N)≤T.
No 8L≤G condition or conjugacy of residual weights is assumed.

The actual stationary Bessel/divisor block at m..m+N-1 is bounded by
that same shape times the maximum of the actual raw phase partial sums,
with a larger uniform C. `exists_atkinsonSourceCutoff_block_bound`
derives its small-frequency and scale conditions for every retained
block from the original power-width range and the exact source ceiling
cutoff, beyond a δ-dependent threshold.

ZVB records these proved consumers; the continuation below also proves
global dyadic assembly. The phase-sum/Gram bound, smaller-width stationary errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
The block theorem has no fourth-root-width restriction; the earlier
stationary-error/zeta consumer still does. No unconditional Add-est
clause or full EPZAE-00--41 completion is claimed.

The original counterexample and independent-coordinate powering/
Heath–Brown chain are unchanged. The exact
`run_tao_trudgian_yang_build.bat` root/audit/PowerShell inventory is
synchronized; maintain it and rerun both principal evaluation scopes.
See the Reproduction Manifest for the semantic audit and terminal evidence.

## Complete dyadic-source checkpoint

Three new modules, `TruncatedDyadicPartition`, `AtkinsonDyadicMain`
and `AtkinsonDyadicZetaConsumer`, have 20 named public audits and
24 regressions. The exact partition uses M=2^j and block length
min(M,N-M), for j<clog(2,N). Every retained endpoint stays at or below
the original cutoff; zero/one cutoffs and exact powers of two are covered.

The actual complete stationary Bessel/divisor series is now bounded by
C G T^(-1/4) times the sum of
M^(-1/4) exp(-G²M/(12T)) times the actual block phase-prefix maximum.
The same source ceiling cutoff supplies every block's small-frequency
geometry. Enlarging only the last raw phase maximum to a full block
does not enlarge the stationary source.

Four Gaussian/local-mean consumers use this complete dyadic bound.
Their error remains Cδ,ε(G log T+T^(1/4+ε)) for G≥T^(1/4), or
Cδ,κ G log T for G≥T^(1/4+κ), within the original power-width range.
The stationary-main bound itself has no fourth-root-width restriction.
ZDA records this exact assembly and these physical consumers.

Global dyadic assembly is now proved. The maximal phase-sum/Gram
estimate, the source-form bridge, smaller-width errors or a proved
lower-value-range reduction, and the genuine twelfth moment remain open.
No unconditional Add-est clause or full-goal completion is claimed.

The counterexample and corrected powering/Heath–Brown chain are unchanged.
Maintain the synchronized root, audits, regressions and exact backing
inventory of `run_tao_trudgian_yang_build.bat`; run it and
`run_lake_build.bat` after relevant changes. The Reproduction Manifest
records the separate semantic and terminal integrity evidence.
