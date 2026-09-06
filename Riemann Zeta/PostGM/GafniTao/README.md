# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has now crossed the release-integration boundary for the native Gafni-Tao core.

The isolated root:

```text
Extension/GafniTao.lean
```

now imports the native analytic source inputs and native theorem suite:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11
PintzPublishedCutoffNative
WooleyNative
EnergyDetectorTranslation
EnergyDetectorPoweredTranslation
```

The central audit:

```text
Extension/GafniTao/Audit.lean
```

now explicitly audits the corresponding native endpoints, including:

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

The core Gafni-Tao theorem is therefore no longer merely a workbench result.

It is now part of the intended isolated root and central dependency-audit surface.

The remaining mathematical frontier has contracted primarily to the Heath-Brown four-zero energy envelope required for the first published Section 3 sample:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

The Pintz `23/24` cutoff needed for the second published sample is now proved natively:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native
```

The exact second-sample exponent algebra is already proved in `Section3Algebra.lean`.

Thus the second sample has no remaining Pintz source-theorem gap. Its remaining work is publication-facing composition and release integration of the Section 3 result.

The complete paper-facing project is **not yet claimed complete**.

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
- the two displayed Section 3 consequences;
- any later certified numerical envelope that is explicitly claimed.

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
\mu(\theta)
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

That chain is now also release-root integrated and centrally audited.

The Section 3 dependency graph is currently:

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
pair-count / detector / energy extraction
        |
        v
HeathBrownZeroEnergyBounds
        |
        v
mu(17/30) <= 7/12
```

and:

```text
native Pintz 2023 source chain
        |
        v
Pintz 23/24 cutoff
        |
        v
second-sample exponent algebra
        |
        v
small-Delta published result
```

The second chain has reached the cutoff theorem.

The first chain remains open at the final zero-energy envelope.

---

# Current status

| Proof layer | Mathematical state | Root / audit state |
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
| Native Theorem 1.1, GM `30/13` | Proved | Integrated and audited |
| Wooley source Corollary 3.2 | Proved | Consumer chain integrated |
| VMVT main conjecture | Proved | Integrated and audited |
| Heath-Brown kth derivative theorem | Proved | Integrated and audited |
| Pintz `23/24` cutoff | Proved | Integrated and audited |
| Signed-shell energy extraction | Proved infrastructure | Integrated and audited |
| Translation into GM base interval | Proved | Integrated and audited |
| Powered GM energy bridge | Proved | Integrated and audited |
| Heath-Brown zero-energy envelope | Open | Active |
| First published sample algebra | Proved conditionally | Section 3 workbench |
| First published sample | Awaiting Heath-Brown energy envelope | Open |
| Second published sample algebra | Proved | Section 3 workbench |
| Pintz source gate for second sample | Closed | Integrated and audited |
| Final second-sample wrapper | Composition / promotion pending | Active |
| Full certified Section 3 optimizer | Open | Optional later phase |
| Final audit execution and inspection | Pending final release pass | Active |

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
- finite-measure facts;
- threshold monotonicity;
- fixed-power eventual bounds;
- epsilon-exponent machinery where appropriate;
- eventual-empty behavior;
- countable positive-threshold reduction;
- exact `EReal` infimum and supremum behavior.

The arithmetic interval convention remains:

```text
x < n <= x + x^theta
```

and the outer exceptional interval remains:

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

The latter counts ordered four-tuples of zero occurrences with analytic multiplicity and the source tolerance:

```math
|\gamma_{1}+\gamma_{2}-\gamma_{3}-\gamma_{4}|
\le 1.
```

The project does not replace the source object by an unweighted set of distinct ordinates.

The associated exponent interfaces `A` and `A*` feed the second- and fourth-moment arguments.

---

# Native sharp truncated explicit formula

The root-integrated native endpoint is:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting sharp-Perron development handles:

- finite Mangoldt Perron identities;
- logarithmic-derivative expansions;
- contour rectangles;
- residues;
- analytic zero multiplicity;
- selected good heights;
- horizontal and vertical edges;
- left-edge estimates;
- functional-equation input;
- low heights;
- arbitrary real endpoints;
- endpoint-uniform cutoff estimates.

The physical range includes:

```math
2 \le T \le x.
```

This analytic input is internally supplied by the native Gafni-Tao theorem.

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

These strip estimates are assembled into the full large-zero-sum measure estimate.

The finite strip count and epsilon are then removed by the exact limiting argument without imposing continuity on the density exponent.

---

# Native Vinogradov-Korobov theorem

The root now imports:

```text
FordAsymptoticZeroFree
```

and the central audit contains:

```lean
GafniTao.ford_asymptotic_zero_free_native
```

with type:

```lean
FordAsymptoticZeroFree
```

This closes the existential zero-free input needed by the core Gafni-Tao theorem.

The proof uses the qualitative Richert-Ford growth machinery together with the five-frequency Vinogradov-Korobov detector.

The older fully optimized Ford constants are not required for this core theorem route.

---

# Native near-one density package

The root now imports:

```text
PintzNearOneNative
```

and the central audit contains:

```lean
GafniTao.exists_pintz_nearOne_log_density_native
```

The theorem supplies:

```text
a positive VK width
a count-vanishing threshold
a sufficient logarithmic near-one density bound
```

The logarithmic density input uses the proved Pintz route rather than requiring the older optimized Ford `58.05 / log^16` package.

This native input is sufficient for the exact Gafni-Tao theorem.

---

# Exact native Theorems 1.3 and 1.2

The root now imports:

```text
NativeTheorems
```

and the central audit explicitly contains:

```lean
GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native
```

The refined theorem proves:

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

The exact source-exponent forms and alternate upper-half max forms remain separately named.

The native theorem supplies internally:

- the frozen Guth-Maynard smooth cutoff;
- the native sharp explicit formula;
- the native near-one density input;
- the native VK zero-free theorem.

There is no longer a project-level source assumption at the top of the native general theorem.

---

# Native Theorem 1.1

The root now imports:

```text
Theorem11
```

and the central audit contains:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_native
GafniTao.gafniTaoTheorem11_guthMaynard_allIntervals_regression
GafniTao.gafniTaoTheorem11_guthMaynard_almostAll_regression
```

using the frozen Guth-Maynard density coefficient:

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

The almost-all result is represented using a single measurable exceptional set of ordinary natural density zero.

---

# Pintz Section 3 cutoff

The previous Section 3 Pintz gate has now been closed.

The root imports:

```text
PintzPublishedCutoffNative
```

and the central audit contains:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native
```

with exact type:

```lean
PintzTwentyThreeTwentyFourCutoff
```

The theorem proves that for:

```math
\frac{23}{24}<\sigma<1,
```

the ordinary zero-density envelope has coefficient at most one.

It does so using the actual native Pintz cell machinery and the project's symmetric multiplicity-weighted zero count.

Thus the source assumption required by the second Section 3 sample has been eliminated.

---

# Second published Section 3 sample

`Section3Algebra.lean` already proves:

```lean
GafniTao.refinedExceptionalUpperExponent_two_fifteenths_add_le
```

from:

```lean
PintzTwentyThreeTwentyFourCutoff.
```

The theorem states, for:

```math
0<\Delta\le\frac{1}{100},
```

that:

```math
\mathrm{refinedExceptionalUpperExponent}
\left(
\frac{2}{15}+\Delta
\right)
\le
1-\frac{9\Delta}{13}.
```

Since:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native
```

is now proved, the mathematical source gate for this sample is closed.

The remaining task is to create or promote the publication-facing unconditional composition with:

```lean
GafniTao.gafniTaoTheorem13_native.
```

The second sample should therefore be described as:

```text
source mathematics closed;
final public composition and release promotion pending.
```

---

# Wooley / VMVT chain

The Wooley source campaign has reached its intended theorem.

The source target:

```lean
GafniTao.WooleyPolynomialCorollary32
```

is proved by:

```lean
GafniTao.wooleyPolynomialCorollary32_native.
```

The downstream bridge then yields the native VMVT main-conjecture input:

```lean
GafniTao.heathBrownVMVTMainConjecture_native
```

and the native Heath-Brown kth-derivative theorem:

```lean
GafniTao.heathBrownKthDerivativeTheorem_native.
```

`WooleyNative` is now imported by the root, and the latter two endpoints are explicitly present in the central audit.

Thus the former Wooley / VMVT branch is no longer an open mathematical dependency.

---

# Heath-Brown energy campaign

This is now the main mathematical frontier.

The target is:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

which requires the three source cells:

```math
A^{\ast}(\sigma)
\le
\frac{10-11\sigma}
{(2-\sigma)(1-\sigma)}
```

on the first range,

```math
A^{\ast}(\sigma)
\le
\frac{18-19\sigma}
{(4-2\sigma)(1-\sigma)}
```

on the middle range, and:

```math
A^{\ast}(\sigma)
\le
\frac{12}{4\sigma-1}
```

on the upper range.

The native kth-derivative theorem and source-shaped finite pair-count machinery already exist.

The current campaign is now attacking the convention and extraction problem between zeta-zero energy and the frozen Guth-Maynard large-values machinery.

---

# New energy-detector bridge

The root now imports:

```text
EnergyDetectorTranslation
EnergyDetectorPoweredTranslation
```

and the central audit contains representative endpoints from these modules.

The translation layer proves exact identities for:

- translating a symmetric ordinate set into the frozen GM base interval;
- preserving cardinality;
- preserving separation;
- translating Dirichlet-polynomial values by an exact unimodular phase twist;
- preserving coefficient norm bounds;
- transporting approximate additive energy by equality.

The powered-energy layer then proves:

```lean
GafniTao.finite_symmetric_source_powered_energy_gm_bound
```

which starts with a separated symmetric large-value set and:

1. translates it into the frozen GM interval;
2. applies the exact phase twist;
3. raises the polynomial to a controlled power;
4. normalizes the powered coefficients;
5. splits the energy into four coordinate classes;
6. feeds those classes into the frozen Guth-Maynard energy theorem;
7. transfers the resulting energy bound back to the original symmetric set.

This is now part of the root and central audit.

It is a direct bridge toward:

```lean
HeathBrownZeroEnergyBounds.
```

The bridge is not yet the final three-cell zero-energy theorem.

---

# First published Section 3 sample

The target remains:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

The exact exponent algebra is already proved in:

```lean
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le
```

conditional only on:

```lean
HeathBrownZeroEnergyBounds.
```

Therefore the remaining mathematical source task for the first sample is sharply isolated:

```text
native kth-derivative theorem
        |
        v
zero-shell / large-value extraction
        |
        v
powered GM energy bridge
        |
        v
HeathBrownZeroEnergyBounds
        |
        v
existing Section 3 algebra
        |
        v
mu(17/30) <= 7/12
```

---

# Older optimized Ford objectives

The repository still contains source-facing objectives such as:

```lean
GafniTao.FordTheorem2
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
```

with the original optimized Ford constants.

These are no longer blockers to the native core Gafni-Tao theorem.

The native Pintz/VK route already supplies sufficient analytic inputs.

They should therefore be classified as:

```text
source-fidelity / optimization objectives
```

rather than:

```text
core theorem blockers.
```

They may still be worth completing independently.

---

# Release integration state

The native core integration gate has substantially closed.

The root now contains:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11
PintzPublishedCutoffNative
WooleyNative
EnergyDetectorTranslation
EnergyDetectorPoweredTranslation
```

The central audit explicitly lists the major native endpoints from these branches.

What remains for final release certification is not merely import wiring.

It is the final execution and inspection step:

1. build the isolated package;
2. run the central audit;
3. inspect the actual `#print axioms` output;
4. run the forbidden-token/source scan;
5. remove or classify development debris;
6. synchronize all public documentation.

The existence of `#print axioms` commands in `Audit.lean` does not by itself certify that their output has been freshly inspected.

---

# Central audit

The central audit now includes, among many others:

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

GafniTao.absoluteSlab_sharpMollified_energy_extraction
GafniTao.sourceDirichletPoly_translate
GafniTao.sourceDirichletPoly_large_on_gmTranslate
GafniTao.exists_source_powered_dyadic_index
GafniTao.exists_source_normalized_powered_block
GafniTao.exists_real_energy_color_classes
GafniTao.finite_source_powered_energy_gm_bound
GafniTao.finite_symmetric_source_powered_energy_gm_bound
```

This is now a much better reflection of the current mathematical frontier.

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

A `Prop` that restates a source theorem is not a proof of that theorem.

An audit source file containing `#print axioms` commands is not equivalent to inspection of their actual output.

Generated certificate data is acceptable only when Lean independently verifies it.

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

These must remain distinct.

Before final release:

- remove accidental temporary environments and caches;
- keep source references intentionally;
- retain certificate generators only where useful for reproduction;
- ensure generated certificate data is independently checked by Lean;
- keep temporary probes out of the publication-facing dependency path.

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

> The core Gafni-Tao formalization is now root-integrated and represented on the central audit surface. This includes the native Vinogradov-Korobov zero-free theorem, a sufficient native Pintz near-one density package, exact native Theorems 1.3 and 1.2, and the Guth-Maynard `30/13` specialization of Theorem 1.1. The Wooley-to-VMVT-to-Heath-Brown kth-derivative chain is also proved and integrated. Pintz's `23/24` Section 3 cutoff is now proved natively, root-integrated, and centrally audited. The remaining major mathematical source gate is the Heath-Brown multiplicity-weighted four-zero energy envelope needed for the first published sample. A new root-integrated energy-detector translation and powered Guth-Maynard bridge directly attacks that remaining gap. The second sample's Pintz source gate is closed, with final publication-facing composition still to be promoted.

Do not currently claim:

```text
The complete Gafni-Tao paper formalization is finished.
```

A concise current claim is:

```text
Core Gafni-Tao release path integrated;
Pintz Section 3 cutoff closed;
Heath-Brown zero-energy envelope remains the main mathematical gate.
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

## 1. Close `HeathBrownZeroEnergyBounds`

This is now the principal mathematical source gate.

Use the existing chain:

```text
native Heath-Brown kth derivative
        |
        v
finite pair-count estimates
        |
        v
signed zero-shell extraction
        |
        v
exact symmetric-set translation
        |
        v
powered GM large-values bridge
        |
        v
three-cell zero-energy envelope
```

The final target is:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

on the genuine multiplicity-weighted `N*` object.

---

## 2. Close the first published sample

Once the energy envelope is proved, combine it with:

```lean
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le
```

and:

```lean
GafniTao.gafniTaoTheorem13_native
```

to prove the publication-facing theorem:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

---

## 3. Promote the second published sample

The Pintz `23/24` cutoff is now native.

Use:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_native
```

with:

```lean
GafniTao.refinedExceptionalUpperExponent_two_fifteenths_add_le
```

and:

```lean
GafniTao.gafniTaoTheorem13_native
```

to construct the unconditional public theorem on the already formalized range:

```math
0<\Delta\le\frac{1}{100}.
```

The target conclusion is:

```math
\mu\!\left(\frac{2}{15}+\Delta\right)
\le
1-\frac{9\Delta}{13}.
```

---

## 4. Promote Section 3 modules into the release path

After the public sample theorems exist:

- import the intended Section 3 modules through `GafniTao.lean`;
- add their public endpoints to `Audit.lean`;
- inspect actual dependency output.

---

## 5. Decide whether to finish optimized Ford objectives

The optimized Ford contracts are no longer needed by the core Gafni-Tao proof.

Decide separately whether the project should also close:

```lean
FordTheorem2
FordZetaGrowthBound
FordNearOneDensityEstimate
```

for source fidelity and reusable analytic value.

---

## 6. Full certified Section 3 optimizer

Only after the displayed sample bounds are complete should the optional full numerical envelope become the main task.

Pin the exact source tables.

Reduce the optimization to finitely many exact cells.

Certify the cells in Lean.

Do not use floating-point calculations as proof evidence.

---

## 7. Final release audit

Before the final completion claim:

1. run `lake build`;
2. execute the central `Audit.lean`;
3. inspect every nonstandard axiom dependency;
4. scan for unfinished declarations;
5. clean temporary environments, caches, and probes;
6. synchronize all public documentation;
7. confirm the final theorem path is reachable from the isolated root.

---

# Repository workflow

`push_to_github.bat` remains the owner-operated publication step.

A GitHub push is a selected public snapshot.

It is not proof verification.

Agents must not push unless separately instructed.

Use completion-language commit messages only after the corresponding theorem is actually closed.

Examples:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Heath-Brown zero-energy envelope"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close first published Section 3 sample"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: integrate second published Section 3 sample"
```

---

# Completion condition

The core theorem path is now structurally:

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

and is imported through the isolated root and represented on the central audit surface.

The full paper-facing phase additionally requires:

```text
native Heath-Brown kth derivative
             |
             v
energy extraction and GM bridge
             |
             v
HeathBrownZeroEnergyBounds
             |
             v
mu(17/30) <= 7/12
```

and:

```text
native Pintz 23/24 cutoff
             |
             v
existing second-sample algebra
             |
             v
small-Delta public theorem
```

The Pintz source gate in the second branch is now closed.

Until the remaining composition and Heath-Brown energy theorem are finished:

**the core Gafni-Tao release path is integrated, the Pintz Section 3 cutoff is closed, and the Heath-Brown zero-energy envelope is the main remaining mathematical gate.**