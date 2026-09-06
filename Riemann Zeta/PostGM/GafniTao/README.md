# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has crossed another major mathematical boundary.

The core Gafni-Tao theorem path is already imported through the isolated release root:

```text
Extension/GafniTao.lean
```

and represented on the central dependency-audit surface:

```text
Extension/GafniTao/Audit.lean
```

That release-integrated core includes:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native

GafniTao.pintzTwentyThreeTwentyFourCutoff_native

GafniTao.heathBrownVMVTMainConjecture_native
GafniTao.heathBrownKthDerivativeTheorem_native
```

The development workbench has now gone further.

It proves the first two native Heath-Brown four-zero energy cells:

```lean
GafniTao.heathBrown_zeroAdditiveEnergy_first_native
GafniTao.heathBrown_zeroAdditiveEnergy_second_native
```

and then proves both displayed Gafni-Tao Section 3 sample bounds:

```lean
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native

GafniTao.exceptionalExponent_two_fifteenths_add_le_native
```

The first theorem is exactly:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

The second theorem proves, for:

```math
0<\Delta\le\frac{1}{100},
```

that:

```math
\mu\!\left(\frac{2}{15}+\Delta\right)
\le
1-\frac{9\Delta}{13}.
```

These two Section 3 sample modules are **not yet imported by `Extension/GafniTao.lean` and are not yet on the central `Audit.lean` surface**.

The mathematical status is therefore:

> **The core Gafni-Tao theorem is release-integrated and centrally audited. Both displayed Section 3 sample bounds are now proved in the development workbench and await release-root and central-audit promotion.**

The stronger full three-cell predicate:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

remains open.

It is no longer required for the first displayed sample, because the native first-sample proof confines the optimizing parameter to the range covered by the first two proved Heath-Brown cells.

The complete publication-facing project is therefore **very near completion but not yet claimed complete**.

---

# Purpose

This directory is the isolated post-Guth-Maynard program for formalizing Ayla Gafni and Terence Tao's paper:

*On the number of exceptional intervals to the prime number theorem in short intervals*

arXiv:2505.24017v1.

The project targets the actual mathematical dependency chain used in the paper:

- the exact short-interval exceptional set;
- Lebesgue-measure exceptional exponents;
- multiplicity-weighted zero density;
- multiplicity-weighted four-zero additive energy;
- the sharp truncated explicit formula;
- second and fourth moments;
- equation (2.7);
- finite-strip and epsilon limiting;
- near-one zero-free and density inputs;
- Theorems 1.3, 1.2, and 1.1;
- the displayed Section 3 numerical consequences;
- optional stronger source-fidelity and optimizer results where explicitly pursued.

This work does not prove the Riemann Hypothesis.

---

# Current proof architecture

The downstream Gafni-Tao mechanism is:

```math
\mathrm{zeta\ zeros}
\longrightarrow
N(\sigma,T),\,N^{\ast}(\sigma,T)
\longrightarrow
A(\sigma),\,A^{\ast}(\sigma)
```

```math
\longrightarrow
L^{\infty},\,L^{2},\,L^{4}
\ \mathrm{zero\text{-}sum\ bounds}
```

```math
\longrightarrow
\mathrm{equation\ (2.7)}
```

```math
\longrightarrow
\mathrm{local\ exceptional\ measure}
```

```math
\longrightarrow
\mathrm{finite\ strips}
\longrightarrow
\varepsilon\mathrm{\ limits}
```

```math
\longrightarrow
\mathrm{meas}\,E_{\delta}(X,\theta)
\ll
X^{\xi}
```

```math
\longrightarrow
\mu_{\delta}(\theta)
\longrightarrow
\mu(\theta).
```

This chain is release-root integrated.

The native near-one source route is:

```text
qualitative Ford exponential sum
              |
              v
qualitative Ford zeta growth
              |
              v
five-frequency VK detector
              |
              v
FordAsymptoticZeroFree
              |
              +-------------------+
              |                   |
              v                   v
VK count vanishing       Pintz near-one detector
              |                   |
              +---------+---------+
                        |
                        v
             native near-one package
                        |
                        v
           exact Gafni-Tao Theorem 1.3
                        |
                        v
           exact Gafni-Tao Theorem 1.2
                        |
                        v
             Guth-Maynard Theorem 1.1
```

That chain is also release-root integrated and centrally audited.

The first displayed Section 3 sample now follows:

```text
Wooley Corollary 3.2
        |
        v
p-adic concentration
        |
        v
VMVT main conjecture
        |
        v
Heath-Brown kth derivative
        |
        v
zero-shell and energy extraction
        |
        v
native first HB energy cell
        +
native second HB energy cell
        |
        v
optimizer confined below 3/4
        |
        v
refined exponent <= 7/12
        |
        v
native Theorem 1.3
        |
        v
mu(17/30) <= 7/12
```

The second displayed sample follows:

```text
native Pintz source chain
        |
        v
native 23/24 cutoff
        |
        v
second-sample exponent algebra
        |
        v
native Theorem 1.3
        |
        v
mu(2/15 + Delta) <= 1 - 9 Delta / 13
```

for the explicit formalized range:

```math
0<\Delta\le\frac{1}{100}.
```

Both final sample theorems currently remain outside the release root and central audit.

---

# Current status table

| Proof layer | Mathematical state | Release / audit state |
|---|---|---|
| Exact exceptional set | Proved | Integrated and audited |
| `mu_delta` / `mu` machinery | Proved | Integrated and audited |
| Multiplicity-weighted `N` | Proved | Integrated and audited |
| Multiplicity-weighted `N*` | Proved | Integrated and audited |
| `A` / `A*` machinery | Proved | Integrated and audited |
| Local arithmetic entry | Proved | Integrated and audited |
| Brun-Titchmarsh localization | Proved | Integrated and audited |
| Native sharp explicit formula | Proved | Integrated and audited |
| Complex Fourier bump | Proved | Integrated and audited |
| Second moment | Proved | Integrated and audited |
| Fourth moment | Proved | Integrated and audited |
| Finite half-open strips | Proved | Integrated and audited |
| Equation (2.7) | Proved | Integrated and audited |
| Limit assembly | Proved | Integrated and audited |
| Global exceptional cover | Proved | Integrated and audited |
| Native VK zero-free theorem | Proved | Integrated and audited |
| Native Pintz near-one package | Proved | Integrated and audited |
| Exact native Theorem 1.3 | Proved | Integrated and audited |
| Exact native Theorem 1.2 | Proved | Integrated and audited |
| Native Theorem 1.1 | Proved | Integrated and audited |
| Pintz `23/24` cutoff | Proved | Integrated and audited |
| Wooley Corollary 3.2 | Proved | Integrated transitively |
| VMVT main conjecture | Proved | Integrated and audited |
| Heath-Brown kth derivative | Proved | Integrated and audited |
| GM energy translation bridge | Proved | Integrated and audited |
| Powered GM energy bridge | Proved | Integrated and audited |
| Heath-Brown first energy cell | Proved | Workbench, local audit |
| Heath-Brown second energy cell | Proved | Workbench, local audit |
| First published sample | Proved | Workbench, local audit |
| Second published sample | Proved | Workbench, local audit |
| Full three-cell `HeathBrownZeroEnergyBounds` | Open | Optional stronger target |
| Optimized Ford source constants | Open | Optional source-fidelity targets |
| Full certified Section 3 envelope | Open | Optional later phase |
| Final sample root integration | Pending | Active |
| Final central audit promotion | Pending | Active |
| Final release execution / inspection | Pending | Active |
| Repository cleanup | Pending | Active |

---

# Exact exceptional-set framework

The formalization uses the actual Mangoldt exceptional set:

```math
E_{\delta}(X,\theta)
=
\left\{
x\in[X,2X]:
\left|
\psi\!\left(x+x^{\theta}\right)
-\psi(x)-x^{\theta}
\right|
\ge
\delta x^{\theta}
\right\}.
```

It defines:

```math
\mu_{\delta}(\theta)
```

and:

```math
\mu(\theta).
```

The development includes:

- measurability;
- finite measure;
- threshold monotonicity;
- fixed-power eventual bounds;
- epsilon-exponent machinery where required;
- eventual-empty behavior;
- countable positive-threshold reduction;
- exact `EReal` infimum and supremum behavior.

The arithmetic interval convention is:

```text
x < n <= x + x^theta
```

and the outer exceptional interval is:

```text
X <= x <= 2X.
```

---

# Multiplicity-weighted zero quantities

The ordinary zero count is:

```math
N(\sigma,T)
```

and the four-zero additive-energy quantity is:

```math
N^{\ast}(\sigma,T).
```

The four-zero object counts ordered zero occurrences with analytic multiplicity and source tolerance:

```math
\left|
\gamma_{1}+\gamma_{2}-\gamma_{3}-\gamma_{4}
\right|
\le 1.
```

The project does not replace this quantity by an unweighted energy of distinct ordinates.

The exponent interfaces `A` and `A*` feed the second- and fourth-moment branches.

---

# Native sharp truncated explicit formula

The root-integrated endpoint is:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting sharp-Perron chain handles:

- finite Mangoldt Perron identities;
- logarithmic-derivative expansions;
- contour rectangles;
- residues;
- analytic zero multiplicity;
- selected good heights;
- right, horizontal, and left edges;
- functional-equation input;
- low heights;
- arbitrary real endpoints;
- endpoint-uniform estimates.

The physical range includes:

```math
2\le T\le x.
```

This analytic input is supplied internally by the native Gafni-Tao theorem.

---

# Equation (2.7)

The half-open strip machinery is release-integrated.

The source alternatives are represented by:

```text
small-density strip
        |
        v
eventually empty
```

```text
right-edge strip
        |
        v
native near-one density
+
native zero-free region
```

```text
remaining strip
        |
        +----------+
        |          |
        v          v
       L2          L4
        |          |
        +----+-----+
             |
             v
          Markov
```

These strip estimates are assembled into the complete large-zero-sum measure estimate.

The finite strip count and epsilon are then removed by the exact limiting argument without imposing continuity on the density exponent.

---

# Native Gafni-Tao core

The release root imports:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11
```

The central audit contains:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native
```

The refined native theorem proves:

```math
\mu(\theta)
\le
\mathrm{refinedExceptionalUpperExponent}(\theta)
```

for:

```math
0<\theta<1.
```

The ordinary theorem proves:

```math
\mu(\theta)
\le
\mathrm{ordinaryExceptionalUpperExponent}(\theta).
```

The native theorem supplies internally:

- the frozen Guth-Maynard smooth cutoff;
- the native sharp explicit formula;
- the native near-one density package;
- the native Vinogradov-Korobov zero-free theorem.

The core theorem therefore no longer accepts project-level analytic source assumptions.

---

# Native Theorem 1.1

The release root imports `Theorem11`.

The central audit contains the native Guth-Maynard specialization using:

```math
A_{0}
=
\frac{30}{13}.
```

The all-interval threshold is:

```math
\theta>\frac{17}{30}.
```

The almost-all threshold is:

```math
\theta>\frac{2}{15}.
```

The almost-all theorem produces one measurable exceptional set of ordinary natural density zero.

---

# Native Pintz Section 3 cutoff

The release root imports:

```text
PintzPublishedCutoffNative
```

and the central audit contains:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native
```

which proves:

```lean
PintzTwentyThreeTwentyFourCutoff
```

for the actual multiplicity-weighted zero-count model.

The Pintz source gate required for the second Section 3 sample is therefore closed.

---

# Wooley / VMVT / Heath-Brown derivative chain

The source target:

```lean
GafniTao.WooleyPolynomialCorollary32
```

has a native proof.

The downstream chain then proves:

```lean
GafniTao.heathBrownVMVTMainConjecture_native
GafniTao.heathBrownKthDerivativeTheorem_native.
```

The latter two endpoints are root-integrated and centrally audited.

Thus the former Wooley / VMVT dependency is no longer an open mathematical branch.

---

# Native low-range Heath-Brown energy bounds

The workbench now proves the first two source energy cells directly against the genuine multiplicity-weighted zero additive energy.

## First cell

For:

```math
\frac{1}{2}\le\sigma\le\frac{2}{3},
```

the theorem:

```lean
GafniTao.heathBrown_zeroAdditiveEnergy_first_native
```

proves:

```math
A^{\ast}(\sigma)
\le
\frac{10-11\sigma}
{(2-\sigma)(1-\sigma)}.
```

The left endpoint is handled explicitly through the Ingham density theorem and a zero-energy comparison.

It is not obtained by assuming continuity of the exponent infimum.

## Second cell

For:

```math
\frac{2}{3}<\sigma\le\frac{3}{4},
```

the theorem:

```lean
GafniTao.heathBrown_zeroAdditiveEnergy_second_native
```

proves:

```math
A^{\ast}(\sigma)
\le
\frac{18-19\sigma}
{(4-2\sigma)(1-\sigma)}.
```

These two theorems are locally audited inside:

```text
HeathBrownZeroEnergyLowNative.lean
```

They are not yet imported through the central release root.

---

# First published Section 3 sample

The first displayed sample no longer requires the full three-cell Heath-Brown package.

The native proof observes that the frozen Guth-Maynard density constraint forces the optimizing parameter into an arbitrarily small neighborhood of:

```math
\frac{7}{10},
```

and therefore below:

```math
\frac{3}{4}.
```

Only the first two native Heath-Brown cells are required.

The workbench proves:

```lean
GafniTao.first_sample_fixed_epsilon_bound_native
```

and then:

```lean
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le_native.
```

The publication-facing theorem is:

```lean
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native
```

with exact conclusion:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

This theorem directly composes the native Section 3 exponent bound with:

```lean
GafniTao.gafniTaoTheorem13_native.
```

No `HeathBrownZeroEnergyBounds` assumption appears in the final theorem.

---

# Second published Section 3 sample

The workbench now also proves the final second displayed sample:

```lean
GafniTao.exceptionalExponent_two_fifteenths_add_le_native
```

for:

```math
0<\Delta\le\frac{1}{100}.
```

Its conclusion is:

```math
\mu\!\left(
\frac{2}{15}+\Delta
\right)
\le
1-\frac{9\Delta}{13}.
```

The proof directly composes:

```lean
GafniTao.gafniTaoTheorem13_native
```

with:

```lean
GafniTao.refinedExceptionalUpperExponent_two_fifteenths_add_le
```

using:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native.
```

Thus both the source input and final mathematical composition are now proved.

---

# Section 3 release status

The two final sample theorems exist in:

```text
Section3NativeSamples.lean
```

which imports:

```text
HeathBrownZeroEnergyLowNative
PintzPublishedCutoffNative
Section3Algebra
```

That module locally checks:

```lean
first_sample_fixed_epsilon_bound_native
refinedExceptionalUpperExponent_seventeen_thirtieths_le_native
exceptionalExponent_seventeen_thirtieths_le_native
exceptionalExponent_two_fifteenths_add_le_native
```

with `#print axioms`.

However:

```text
HeathBrownZeroEnergyLowNative
Section3NativeSamples
```

are not yet imported by the central release root.

Their endpoints do not yet appear in central `Audit.lean`.

Therefore the two published samples should currently be described as:

```text
mathematically proved
locally dependency-audited
release promotion pending
```

rather than:

```text
fully release-certified.
```

---

# Stronger full Heath-Brown envelope

The source-facing predicate:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

contains three piecewise cells.

The first two are now proved natively.

The third high-range cell remains active.

The full three-cell package is stronger than what is required for the first displayed Gafni-Tao sample.

It therefore belongs in the remaining program as:

```text
stronger Section 3 source theorem
full-envelope / source-fidelity target
```

rather than as a blocker to:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

The ongoing high-cell development remains useful for:

- the full published energy envelope;
- broader Section 3 optimization;
- reusable four-zero energy theory;
- source fidelity.

---

# Energy-detector bridge

The release root already imports:

```text
EnergyDetectorTranslation
EnergyDetectorPoweredTranslation
```

and central `Audit.lean` contains representative endpoints from this chain.

The bridge proves exact operations for:

- translating symmetric ordinate sets into the frozen GM interval;
- preserving cardinality and separation;
- translating the Dirichlet polynomial by an exact phase twist;
- preserving coefficient norm bounds;
- powering the polynomial;
- splitting approximate additive energy into color classes;
- feeding those classes into the frozen Guth-Maynard energy theorem;
- transporting the resulting energy estimate back to the original set.

A representative endpoint is:

```lean
GafniTao.finite_symmetric_source_powered_energy_gm_bound.
```

This machinery feeds the native low-range Heath-Brown energy results and the remaining high-cell program.

---

# Optional optimized Ford objectives

The repository still contains source-facing targets such as:

```lean
GafniTao.FordTheorem2
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
```

with the original optimized Ford constants.

These are not blockers to:

- native Theorem 1.3;
- native Theorem 1.2;
- native Theorem 1.1;
- either displayed Section 3 sample.

The native Pintz/VK path already supplies the analytic inputs required for those results.

The optimized Ford contracts should therefore be classified as:

```text
optional source-fidelity and reusable-analysis objectives.
```

---

# Optional full Section 3 optimizer

The displayed samples are now mathematically proved.

A larger optional target is the full piecewise Section 3 envelope.

If pursued, it should:

1. pin the exact source tables;
2. state every piecewise input explicitly;
3. prove endpoint compatibility;
4. reduce the optimization to finitely many exact cells;
5. certify the cells in Lean;
6. use floating-point calculations only for exploration and checking.

The still-open high Heath-Brown cell may matter for this stronger objective even though it is unnecessary for the first displayed sample.

---

# Central audit status

The central audit is:

```text
Extension/GafniTao/Audit.lean
```

and imports:

```lean
import GafniTao.
```

It already covers the native core, including:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native

GafniTao.pintzTwentyThreeTwentyFourCutoff_native

GafniTao.heathBrownVMVTMainConjecture_native
GafniTao.heathBrownKthDerivativeTheorem_native
```

It also covers major energy-translation endpoints.

It does not yet centrally audit:

```lean
GafniTao.heathBrown_zeroAdditiveEnergy_first_native
GafniTao.heathBrown_zeroAdditiveEnergy_second_native

GafniTao.first_sample_fixed_epsilon_bound_native
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le_native
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native
GafniTao.exceptionalExponent_two_fifteenths_add_le_native
```

because the corresponding modules have not yet been promoted into the release root.

---

# Verification

Run from:

```text
Riemann Zeta/PostGM/GafniTao/Extension
```

A release-quality verification should include:

```bash
lake build
lake env lean GafniTao/Audit.lean
```

and:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

Interpret the results carefully.

Compilation alone is not enough.

A local `#print axioms` check does not replace central release-audit promotion.

A theorem is publication-facing only after the intended dependency path is imported, built, and inspected.

---

# Source and repository hygiene

The development repository contains several artifact classes:

```text
source references
Lean proof modules
certificate data
certificate generators
temporary probes
temporary Python environments
compiled caches
extraction artifacts
```

Before final release:

- remove accidental temporary Python environments;
- remove compiled caches;
- remove obsolete extraction debris;
- keep intentionally pinned source material;
- keep certificate generators only where useful for reproduction;
- ensure generated certificate data is independently checked by Lean;
- keep temporary probes outside the publication-facing dependency graph.

---

# Isolation boundary

The extension remains isolated from the completed Guth-Maynard foundation.

Frozen foundation commit:

```text
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be
```

Frozen foundation tag:

```text
gm-foundation-freeze-v1.0.1
```

Foundation Lean version:

```text
v4.30.0
```

All Gafni-Tao development belongs below:

```text
PostGM/GafniTao/Extension/
```

Do not modify the frozen foundation merely to make the extension easier to prove.

Do not weaken frozen public contracts.

Do not import the experimental extension back into:

```text
RiemannZeta.lean
```

The dependency direction remains:

```text
Frozen Guth-Maynard foundation
              |
              v
      Gafni-Tao extension
```

---

# Acceptance standard

A publication-facing theorem is accepted only when every applicable condition holds:

1. The Lean statement matches the intended source theorem.
2. Source parameter ranges and endpoint conventions are correct.
3. Analytic multiplicities are represented correctly.
4. Constants and logarithmic factors are accounted for.
5. No unproved continuity assumption is introduced.
6. No unauthorized epsilon loss is inserted.
7. No project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised target theorem supplies the result.
8. The theorem is imported through the intended release root.
9. Source-sensitive endpoints appear in the central audit.
10. The isolated package builds.
11. The actual axiom output is inspected.
12. Generated certificates are checked by Lean.
13. Public documentation agrees with the actual theorem graph.

---

# Claim discipline

The strongest safe summary of the repository at present is:

> The core Gafni-Tao formalization is root-integrated and represented on the central audit surface. This includes the native Vinogradov-Korobov zero-free theorem, a sufficient native Pintz near-one density package, exact native Theorems 1.3 and 1.2, the Guth-Maynard `30/13` specialization of Theorem 1.1, the native Pintz `23/24` cutoff, and the Wooley-to-VMVT-to-Heath-Brown kth-derivative chain. Beyond that release root, the development workbench now proves the first two Heath-Brown four-zero energy cells and both displayed Section 3 sample results. Those final sample modules remain to be imported into the release root and added to the central audit. The stronger third Heath-Brown energy cell, full three-cell envelope, optimized Ford constants, and full certified Section 3 optimizer remain optional or broader continuation targets.

Do not yet claim:

```text
The entire isolated package has completed its final release certification.
```

A concise current claim is:

```text
Core Gafni-Tao release path integrated;
both displayed Section 3 samples proved;
final sample promotion and release certification pending.
```

---

# Documents

The project-control documents are:

- [Gafni-Tao Sources.md](Gafni-Tao%20Sources.md)
- [Gafni-Tao Architecture.md](Gafni-Tao%20Architecture.md)
- [Gafni-Tao Research Agenda.md](Gafni-Tao%20Research%20Agenda.md)
- [Gafni-Tao Crosswalk.md](Gafni-Tao%20Crosswalk.md)
- [Gafni-Tao Shitlist.md](Gafni-Tao%20Shitlist.md)
- [Gafni-Tao Goal Prompt.md](Gafni-Tao%20Goal%20Prompt.md)

When documentation and Lean disagree:

```text
actual theorem source
        +
release-root imports
        +
central audit
```

take precedence.

Then update the documentation.

---

# Near-term execution order

## 1. Promote the native Section 3 sample chain

Import:

```text
HeathBrownZeroEnergyLowNative
Section3NativeSamples
```

through:

```text
Extension/GafniTao.lean.
```

Then add the public endpoints to central `Audit.lean`:

```lean
GafniTao.heathBrown_zeroAdditiveEnergy_first_native
GafniTao.heathBrown_zeroAdditiveEnergy_second_native

GafniTao.first_sample_fixed_epsilon_bound_native
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le_native
GafniTao.exceptionalExponent_seventeen_thirtieths_le_native
GafniTao.exceptionalExponent_two_fifteenths_add_le_native
```

Run the complete isolated build and inspect actual dependency output.

---

## 2. Synchronize the public project-control documents

Once the sample modules are promoted, update:

```text
README.md
Gafni-Tao Architecture.md
Gafni-Tao Crosswalk.md
Gafni-Tao Shitlist.md
Gafni-Tao Research Agenda.md
```

so the displayed samples are no longer described as pending mathematical results.

---

## 3. Decide the scope of the stronger Heath-Brown program

The first two cells suffice for the first displayed sample.

Decide whether to continue immediately toward:

```lean
HeathBrownZeroEnergyBounds
```

including the third high-range cell.

Reasons to continue include:

- source fidelity;
- the full Section 3 envelope;
- reusable energy machinery;
- future downstream consumers.

It is no longer required to claim the first displayed sample.

---

## 4. Decide whether to finish the optimized Ford objectives

The optimized Ford contracts are not needed for the native Gafni-Tao results already proved.

Possible continuation targets are:

```lean
FordTheorem2
FordZetaGrowthBound
FordNearOneDensityEstimate
```

Treat these as independent analytic formalization goals rather than blockers.

---

## 5. Full certified Section 3 optimizer

If the full numerical envelope is in project scope:

- pin all source tables;
- formalize each source segment;
- prove endpoint compatibility;
- reduce optimization to exact finite cells;
- certify every cell in Lean.

Do this after the displayed sample theorems are release-integrated.

---

## 6. Final release pass

Before declaring the current scoped project complete:

1. run the complete isolated build;
2. execute central `Audit.lean`;
3. inspect the actual axiom output;
4. run the forbidden-token scan;
5. remove temporary environments, caches, and probes;
6. synchronize documentation;
7. verify that both public sample theorems are reachable from `GafniTao.lean`.

---

# Repository workflow

`push_to_github.bat` remains the owner-operated publication step.

A GitHub push is a selected public snapshot.

It is not proof verification.

Agents must not push unless separately instructed.

Use completion-language commit messages only after the corresponding release step is actually finished.

Examples:

```bat
push_to_github.bat "PostGM Gafni-Tao: integrate both native Section 3 sample theorems"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: complete central audit of published sample bounds"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close full Heath-Brown three-cell energy envelope"
```

---

# Completion condition

The core theorem path is already:

```text
frozen Guth-Maynard foundation
             |
             +---------------------------+
             |                           |
             v                           v
native sharp explicit formula     native near-one package
             |                           |
             +-------------+-------------+
                           |
                           v
                Section 2 transfer machine
                           |
                           v
             exact Gafni-Tao Theorem 1.3
                           |
                           v
                  Theorem 1.2
                           |
                           v
           Guth-Maynard Theorem 1.1
```

and is release-root integrated.

The two displayed Section 3 mathematical paths are now:

```text
native HB first and second cells
             |
             v
first-sample optimizer
             |
             v
mu(17/30) <= 7/12
```

and:

```text
native Pintz 23/24 cutoff
             |
             v
second-sample algebra
             |
             v
mu(2/15 + Delta) <= 1 - 9 Delta / 13
```

for:

```math
0<\Delta\le\frac{1}{100}.
```

Both final theorems exist.

The immediate completion gate is now:

```text
Section3NativeSamples
        |
        v
release-root import
        |
        v
central Audit.lean
        |
        v
full build and dependency inspection
        |
        v
publication-facing release
```

Until that promotion is complete:

**the core Gafni-Tao theorem is release-integrated, both displayed Section 3 sample bounds are mathematically proved, and final Section 3 release promotion is the immediate gate.**