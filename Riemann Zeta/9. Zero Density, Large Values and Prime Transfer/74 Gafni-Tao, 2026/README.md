# Gafni-Tao exceptional intervals in Lean

This directory contains an isolated Lean formalization of the release-scope
results in Gafni-Tao, *Primes in almost all short intervals*, arXiv
`2505.24017v1`. It consumes a read-only snapshot of the completed
Guth-Maynard foundation and does not modify or import back into the canonical
`RiemannZeta/` project.

The formalization is a kernel-checked implementation of published mathematics.
It is not a claim of new mathematics, peer review, publication, canonicality,
or a path to the Riemann Hypothesis.

## Results in the release root

For `0 < theta < 1`, the principal refined theorem is:

```lean
GafniTao.gafniTaoTheorem13_native :
  exceptionalExponent theta <= refinedExceptionalUpperExponent theta
```

The right side is the extended-real expression corresponding to

```text
inf_(epsilon>0)
  sup_(0<=sigma<1, A(sigma)>=1/(1-theta)-epsilon)
    min(
      (1-theta)(1-sigma)A(sigma)+2sigma-1,
      (1-theta)(1-sigma)A*(sigma)+4sigma-3
    ).
```

The source `inf_(epsilon>0)` is retained. The proof does not assume continuity
or attainment of `A`. The alternate strict-upper-half statement is
`gafniTaoTheorem13_max_native`.

The ordinary second-moment corollaries are:

```lean
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem12_max_native
```

The frozen-Guth-Maynard specialization of Theorem 1.1 is:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

It uses `A0=30/13` and contains both conclusions:

- the prime number theorem in every interval of length `x^theta` for
  `theta>17/30`;
- the prime number theorem outside one measurable natural-density-zero set for
  `theta>2/15`.

Regression projections expose each half separately without replacing the
combined theorem:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_allIntervals_regression
GafniTao.gafniTaoTheorem11_guthMaynard_almostAll_regression
```

The two displayed Section 3 sample inequalities are also native:

```lean
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native :
  exceptionalExponent (17 / 30) <= ((7 / 12 : Real) : EReal)

GafniTao.exceptionalExponent_two_fifteenths_add_le_native
    (hDelta : 0 < Delta) (hDeltaUpper : Delta <= 1 / 100) :
  exceptionalExponent (2 / 15 + Delta) <=
    ((1 - 9 * Delta / 13 : Real) : EReal)
```

The second theorem gives an explicit quantified meaning to “sufficiently
small.”

## Source-faithful objects

The exceptional set is the measurable set of real `x` in `[X,2X]` for which

```text
|sum_(x<n<=x+x^theta) Lambda(n)-x^theta| >= delta*x^theta.
```

The arithmetic interval is half-open and the Mangoldt weight includes prime
powers. `mu_delta(theta)` is the infimum of fixed exponents for an eventual
`O_(delta,theta)(X^xi)` bound; no epsilon loss is inserted into this
definition. `mu(theta)` is the supremum over positive `delta`, represented in
`EReal` with the empty-supremum convention.

The ordinary zero count uses analytic multiplicity in the frozen rectangle.
The four-zero count is ordered and weighted by the product of the four
analytic multiplicities, with tolerance

```text
|gamma1+gamma2-gamma3-gamma4| <= 1.
```

The exponents `A` and `A*` use their source epsilon-power bounds. Lean proves
occurrence-list equalities connecting these definitions to the finite sums
used in the moment argument.

## Analytic proof route

The release follows Section 2 in source order:

1. the real-endpoint Chebyshev/von-Mangoldt identity;
2. the finite multiplicative cover and the replacement at
   `tau=X^(1-theta)`;
3. the sharp truncated explicit formula with sign, multiplicity, pole,
   trivial-zero, prime-power, endpoint, selected-height, and contour errors;
4. equations (2.3) and (2.4);
5. native Vinogradov-Korobov zero-free count vanishing and a native Pintz
   logarithmic near-one density estimate;
6. Lemma 2.1's right-edge decay;
7. Lemma 2.2's physical strip supremum;
8. the nonnegative compactly supported bump, its complex Fourier transform,
   uniform decay, and the exact `c_rho`;
9. Lemma 2.3's second moment;
10. pair counting, double counting, Schur control, and the exact `N*` bridge;
11. Lemma 2.4's fourth moment;
12. the half-open `J`-strip right-edge, small-density, `L2`, and `L4`
    alternatives in equation (2.7); and
13. the epsilon and strip-width limits in the paper's order.

The formal ledger retains logarithmic, endpoint, cover-multiplicity, `2/J`,
`4/J`, and epsilon losses until the final limit theorem.

## Published inputs actually consumed

The ordinary density route uses the actual frozen theorem
`RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native`; it is not
supplied as a theorem-equivalent parameter.

The first numerical sample uses the two native Heath-Brown four-zero energy
cells required near `sigma=7/10`. The second uses the native Pintz theorem

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native.
```

The general theorem uses

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native.
```

These are sufficient source statements for the Gafni-Tao consumers. This
release does not claim the optimized numerical constants from Ford's older
formulations.

## Isolation and pins

The standalone package is `Extension/`. Its direct pins are:

- frozen GM tag `gm-foundation-freeze-v1.0.1`;
- frozen GM commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`;
- Lean `v4.30.0`;
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- a local minimal PNT+ closure derived from source revision
  `4ecb950126c4290293c5662dfe0e884123171df5`.

Downloaded papers and source archives are listed in `Sources/PINS.md` and
hashed in `Sources/SHA256SUMS.txt`. The frozen foundation archive has its own
manifest at `Extension/FrozenFoundation/SHA256SUMS.txt`.

## Build and audit

From this directory, run:

```powershell
cmd /c run_gafni_tao_build.bat --no-pause
```

The two Lake workspaces keep their downloaded dependency packages under the
repository-root `.lake/` directory. The formalization and its local PNT+ source
remain in this Node 74 directory, while the shorter generated-dependency paths
keep deep Mathlib artifact names below the legacy Windows path limit.

The runner:

- verifies all source hashes, the frozen-foundation archive, and the exact
  local PNT+ closure;
- builds the warning-free local PNT+ package;
- builds `Extension/GafniTao.lean`, the isolated production root;
- rejects every warning, tactic suggestion, or linter diagnostic;
- runs `Extension/GafniTao/Audit.lean`;
- scans all Gafni-Tao Lean files for forbidden proof shortcuts; and
- saves a complete timestamped log in `logs/`.

The central audit reports only the standard Lean/Mathlib logical dependencies
`propext`, `Classical.choice`, and `Quot.sound` for the public endpoints. It
must not report `sorryAx` or any project postulate.

### Warning-free PNT+ closure

The exact upstream PNT+ revision contains two unrelated admitted declarations
in `Wiener.lean`. Those declarations and two helpers used only by them are not
in the dependency graph of `WeakPNT`, `chebyshev_asymptotic`, the frozen
foundation, or any Gafni-Tao theorem. The isolated package therefore uses the
exact 83-file transitive closure it needs, with 82 files byte-identical and
only that unreachable four-declaration block removed from `Wiener.lean`.

The runner verifies the upstream and retained SHA-256 values, exact closure
size, sole permitted divergence, absence of the removed declarations, and zero
Lean diagnostics. This is an auditable local derivative of the pinned source,
not a claim that the upstream repository itself is warning-free. See
`Gafni-Tao Reproduction Manifest.md`.

The latest recorded isolated run passed after the map-oriented move on
2026-09-07, building the complete local PNT+ and Gafni-Tao roots with zero
diagnostics. Runner logs are transient ignored evidence; rerun the command
above to produce evidence for the current checkout.

## Project-control documents

These files have distinct roles and should not be merged:

- `README.md` (this file): concise project status, entry points, and verification
  instructions.
- `Gafni-Tao Architecture.md`: the canonical raw-Mermaid dependency and status
  dashboard. It deliberately contains Mermaid source only.
- `Gafni-Tao Checklist.md`: the detailed GT-00 through GT-26 acceptance ledger.
- `Gafni-Tao Goal Prompt.md`: the operational kickoff contract for an agent
  resuming work within the frozen-foundation boundary.
- `Gafni-Tao Research Agenda.md`: mathematical scope, strategy, non-claims, and
  maintenance rules.
- `Gafni-Tao Crosswalk.md`: source-to-declaration map and specification
  conventions.
- `Gafni-Tao Reproduction Manifest.md`: exact pins, commands, hashes, and the
  local PNT+ derivation.
- `Gafni-Tao Sources.md` and `Sources/`: source research, provenance, and pinned
  source artifacts.
- `Extension/GafniTao/Audit.lean`: executable theorem-dependency audit.
- `Dependencies/PrimeNumberTheoremAndClean/README.md`: exact minimal PNT+
  closure and its sole source edit.

Root-level Lean files under `Extension/` whose names begin with `Probe` (plus
the similarly named API/check experiments) are unimported legacy development
probes, not production theorem modules. They remain adjacent to the frozen
release because the release-integrity scan covers the entire Extension Lean
tree; relocating or deleting them is deferred to a deliberately versioned
release-boundary change.

## Deliberate non-claims

The release does not include or claim:

- the full best-known piecewise Section 3 numerical curve;
- the optional third/high Heath-Brown energy cell;
- Ford's optimized constants `9.463`, `133.66`, `76.2`, `4.45`, or `58.05`;
- a formalization of every theorem in every cited source;
- external semantic validation, peer review, publication, or canonical status.

Those are possible follow-on projects, not assumptions hidden inside the
released theorem chain.

## Repository synchronization

`push_to_github.bat` is a simple owner-operated synchronization script. It is
not invoked by the build, audit, or runner. The current suggested commit
message is recorded near the top of `Gafni-Tao Research Agenda.md`.
