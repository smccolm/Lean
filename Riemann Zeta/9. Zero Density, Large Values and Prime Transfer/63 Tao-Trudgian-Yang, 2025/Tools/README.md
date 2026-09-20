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
  Their 38 public audits and 20 regressions are included. The remaining
  Y0 asymptotic and uniform stationary estimates, sharp Atkinson inequality
  and genuine twelfth moment remain open, not assumed or excluded;
- `run_tao_trudgian_yang_build.bat` -- human-facing wrapper at the project root, with
  `--no-pause` support for agents and CI.

Every tool must print the exact input pins and preserve complete stdout/stderr
in the reproduction log. A tool exit code is not proof evidence unless its
output is consumed by a Lean kernel-checked certificate theorem.
