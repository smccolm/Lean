# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has crossed several major mathematical boundaries.

Most of the downstream Gafni-Tao Section 2 transfer mechanism is already integrated into the isolated release root and central audit.

Separately, the development workbench now contains native Lean proofs of:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native
```

The workbench also now closes the Wooley / VMVT dependency chain:

```lean
GafniTao.wooleyPolynomialCorollary32_native
GafniTao.heathBrownVMVTMainConjecture_native
GafniTao.heathBrownKthDerivativeTheorem_native
```

Thus the source-level Wooley Corollary 3.2 target, the corresponding VMVT main-conjecture input, and Heath-Brown's kth-derivative theorem are now mathematically proved in Lean.

These newer theorem files are **not yet imported by the release root `Extension/GafniTao.lean` or represented in the central `Audit.lean`**.

The current publication-facing mathematical frontier is narrower:

```lean
GafniTao.HeathBrownZeroEnergyBounds
GafniTao.PintzTwentyThreeTwentyFourCutoff
```

remain open source inputs for the two displayed Section 3 sample results.

The correct current claim is:

> **The core Gafni-Tao theorem and the Wooley-to-Heath-Brown VMVT dependency are proved in the development workbench. Release-root integration, central audit promotion, and the remaining Section 3 source inputs are still active.**

The complete publication-facing project is therefore **not yet claimed complete**.

---

# Purpose

This directory is the isolated post-Guth-Maynard program for formalizing Ayla Gafni and Terence Tao's paper:

*On the number of exceptional intervals to the prime number theorem in short intervals*

arXiv:2505.24017v1.

The project targets the actual mathematical dependency chain used in the paper:

- exceptional-set measure theory;
- multiplicity-weighted zero density;
- four-zero additive energy;
- the sharp explicit formula;
- second and fourth moments;
- the equation (2.7) strip argument;
- finite-strip and epsilon limiting;
- near-one zero-free and density inputs;
- Theorems 1.3, 1.2, and 1.1;
- the published Section 3 numerical consequences.

This work does not prove the Riemann Hypothesis.

---

# Current architecture

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

That downstream machine is substantially release-root integrated.

The native source-input route is now:

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

The major Wooley / Heath-Brown dependency route is now:

```text
Wooley source means
        |
        v
conditioning and p-adic descent
        |
        v
Sections 6 through 10
        |
        v
WooleyPolynomialCorollary32
        |
        v
monomial p-adic concentration
        |
        v
VMVT main conjecture
        |
        v
Heath-Brown kth-derivative theorem
        |
        v
Heath-Brown pair-count machinery
        |
        v
HeathBrownZeroEnergyBounds
        |
        v
first published Gafni-Tao sample
```

The chain is proved through the kth-derivative theorem.

The final energy-envelope step remains open.

---

# Release root versus development workbench

The distinction between mathematical proof state and release integration is intentional.

## Release root

The production-style root is:

```text
Extension/GafniTao.lean
```

It currently imports the established downstream Gafni-Tao mechanism and the older Ford analytic/combinatorial chain through:

```text
FordLemma33Finite
FordCountMonotone
FordLemma63MomentIntegral
ZeroEnergyLocal
```

It does **not yet** import the newer native theorem suite:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11

PublishedExponentInputs
Section3Algebra

WooleySourceCriticalBase
WooleyNative

HeathBrown...
Pintz2023...
```

## Development workbench

The repository contains substantial proved mathematics beyond the release root.

Important native workbench endpoints now include:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native

GafniTao.wooleyPolynomialCorollary32_native
GafniTao.heathBrownVMVTMainConjecture_native
GafniTao.heathBrownKthDerivativeTheorem_native
```

These theorems must be promoted deliberately into the release root and central audit before they become publication-facing release claims.

---

# Current status table

| Proof layer | Mathematical state | Release-root state |
|---|---|---|
| Exact exceptional set | Proved | Integrated |
| `mu_delta` / `mu` machinery | Proved | Integrated |
| Multiplicity-weighted `N` | Proved | Integrated |
| Multiplicity-weighted `N*` | Proved | Integrated |
| `A` / `A*` exponent machinery | Proved | Integrated |
| Local arithmetic entry | Proved | Integrated |
| Brun-Titchmarsh localization | Proved | Integrated |
| Native sharp explicit formula | Proved | Integrated |
| Complex Fourier bump | Proved | Integrated |
| Second moment | Proved | Integrated |
| Fourth moment | Proved | Integrated |
| Finite half-open strips | Proved | Integrated |
| Equation (2.7) | Proved | Integrated |
| Limit assembly | Proved | Integrated |
| Global exceptional cover | Proved | Integrated |
| Conditional Theorem 1.3 | Proved | Integrated |
| Conditional Theorem 1.2 | Proved | Integrated |
| Frozen GM `30/13` consumer | Proved | Integrated |
| Qualitative Ford exponential sum | Proved | Workbench |
| Qualitative Ford zeta growth | Proved | Workbench |
| Native Ford asymptotic zero-free region | Proved | Workbench |
| Native Pintz near-one package | Proved | Workbench |
| Exact unconditional Theorem 1.3 | Proved | Workbench |
| Exact unconditional Theorem 1.2 | Proved | Workbench |
| Theorem 1.1, GM `30/13` specialization | Proved | Workbench |
| Section 3 epsilon-removal algebra | Proved | Workbench |
| First sample exponent algebra | Proved conditional on Heath-Brown energy | Workbench |
| Second sample exponent algebra | Proved conditional on Pintz cutoff | Workbench |
| Wooley source Corollary 3.2 | Proved | Workbench |
| Wooley p-adic concentration bridge | Proved | Workbench |
| VMVT main conjecture input | Proved | Workbench |
| Heath-Brown kth-derivative theorem | Proved | Workbench |
| Heath-Brown finite Lemma 2 | Substantially proved | Workbench |
| Heath-Brown zero-energy envelope | Open | Workbench |
| Pintz Corollaries 1-3 source chain | Substantially proved | Workbench |
| Pintz Theorem 1' to `23/24` bridge | Proved | Workbench |
| Pintz `23/24` source cutoff | Open | Workbench |
| Published first sample | Awaiting Heath-Brown energy input | Open |
| Published small-Delta sample | Awaiting Pintz cutoff | Open |
| Full Section 3 optimizer | Open | Open |
| Native-core release promotion | Pending | Open |
| Final release audit | Pending | Open |

---

# Implemented downstream theorem spine

## 1. Exceptional sets

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
\right\}
```

The project defines:

```math
\mu_{\delta}(\theta)
```

and:

```math
\mu(\theta)
```

with the required measure-theoretic and extended-real infrastructure.

The implementation includes:

- measurability;
- finite measure;
- threshold monotonicity;
- fixed-power bounds;
- epsilon-exponent bounds;
- eventual-empty behavior;
- positive-threshold countable reduction.

---

## 2. Multiplicity-weighted zero counting

The project uses the actual multiplicity-weighted zero counts.

The ordinary count is:

```math
N(\sigma,T)
```

and the four-zero energy quantity is:

```math
N^{\ast}(\sigma,T)
```

The four-zero object counts ordered zero occurrences with analytic multiplicity.

It is not replaced by an unweighted set of ordinates.

The exponent interfaces `A` and `A*` feed the second- and fourth-moment arguments.

---

## 3. Native sharp explicit formula

The release-integrated native endpoint is:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The sharp-Perron development handles:

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
2 \le T \le x
```

---

## 4. Second and fourth moments

The second-moment route consumes the actual ordinary zero count.

The fourth-moment route consumes the actual multiplicity-weighted four-zero energy.

Thus the refined theorem genuinely retains the `A*` improvement.

---

## 5. Equation (2.7)

The half-open strip machinery is implemented.

The strip alternatives have the form:

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
near-one density + zero-free input
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

These are assembled into a measure bound for the complete large-zero-sum event.

---

## 6. Limit and global-cover assembly

The finite strip count and positive epsilon are removed through the exact limiting machinery.

Representative integrated results include:

```lean
GafniTao.exists_refined_limit_witness
GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The proof chain therefore reaches the actual global exceptional exponent.

---

# Native Vinogradov-Korobov zero-free theorem

The workbench contains:

```lean
GafniTao.ford_asymptotic_zero_free_native
```

with type:

```lean
FordAsymptoticZeroFree
```

This discharges the earlier existential zero-free source contract.

The proof uses:

- the qualitative global Ford/Richert zeta-growth bound;
- the Vinogradov-Korobov scale;
- the five-frequency trigonometric detector;
- an explicit positive zero-free constant;
- conjugation symmetry.

Thus the zero-free branch is no longer a mathematical prerequisite for the general Gafni-Tao theorem.

It remains a release-integration task.

---

# Native near-one density package

The workbench contains:

```lean
GafniTao.exists_pintz_nearOne_log_density_native
```

which produces:

```text
a positive VK width
a zero-free count-vanishing threshold
a near-one logarithmic density bound
```

The density statement has the form:

```lean
NearOneLogDensityBound
  pintzNearOneDensityCoefficient
  524
  Tdensity
```

The proof splits the range into:

```text
below VK boundary
    -> zero count vanishes

eta <= 1/8
    -> corrected Pintz detector

1/8 < eta <= 1/2
    -> global zero-count bound absorbed
       by the larger Pintz exponent
```

The logarithmic power `524` is intentional.

This route is sufficient for the exact general Gafni-Tao theorem.

It does not reproduce the older optimized Ford `58.05 / log^16` package.

That optimized package remains a source-fidelity objective rather than a blocker.

---

# Exact native Theorems 1.3 and 1.2

The workbench contains:

```lean
GafniTao.gafniTaoTheorem13_native
```

with theorem statement:

```math
\mu(\theta)
\le
\mathrm{refinedExceptionalUpperExponent}(\theta)
```

for:

```math
0<\theta<1
```

It supplies internally:

- the frozen Guth-Maynard smooth cutoff;
- the native sharp explicit formula;
- the native Pintz near-one package;
- the native VK zero-free theorem.

The ordinary theorem:

```lean
GafniTao.gafniTaoTheorem12_native
```

proves:

```math
\mu(\theta)
\le
\mathrm{ordinaryExceptionalUpperExponent}(\theta)
```

The workbench also contains:

```lean
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native
```

The exact source exponent theorem and the alternate max-form theorem remain separately named.

---

# Native Theorem 1.1

The workbench contains:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

using:

```math
A_{0}
=
\frac{30}{13}
```

The all-interval threshold is:

```math
\theta
>
\frac{17}{30}
```

The almost-all threshold is:

```math
\theta
>
\frac{2}{15}
```

The almost-all branch produces a single measurable exceptional set `E` satisfying:

```text
NaturalDensityZero E
```

outside which the short-interval prime number theorem holds.

Representative endpoints include:

```lean
GafniTao.gafniTaoTheorem11_almostAll_guthMaynard_singleSet_native
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

---

# Section 3

The active mathematical frontier is now concentrated in two source predicates.

## Published source interfaces

`PublishedExponentInputs.lean` records:

```lean
GafniTao.PintzFirstDensitySegment
GafniTao.PintzTwentyThreeTwentyFourCutoff
GafniTao.HeathBrownZeroEnergyBounds
```

These predicates are defined using the genuine project zero-count and zero-energy objects.

No separate numerical surrogate exponent is used.

---

## First published sample

The target is:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}
```

The exact exponent algebra is already proved conditionally.

The workbench contains:

```lean
GafniTao.refinedExceptionalUpperExponent_seventeen_thirtieths_le
```

with assumption:

```lean
hHeathBrown : HeathBrownZeroEnergyBounds
```

Thus the remaining mathematical task for the first sample is the source closure of the Heath-Brown four-zero energy envelope.

The Gafni-Tao optimization algebra is already complete.

---

## Second published sample

The workbench contains:

```lean
GafniTao.refinedExceptionalUpperExponent_two_fifteenths_add_le
```

which proves, for:

```math
0<\Delta\le\frac{1}{100},
```

the bound:

```math
\mathrm{refinedExceptionalUpperExponent}
\left(
\frac{2}{15}+\Delta
\right)
\le
1-\frac{9\Delta}{13}
```

assuming:

```lean
PintzTwentyThreeTwentyFourCutoff
```

The sufficiently-small range is already explicit.

The remaining task is to discharge the Pintz cutoff source predicate.

---

# Wooley / VMVT source theorem

The Wooley source campaign has now crossed its main mathematical endpoint.

The source target:

```lean
GafniTao.WooleyPolynomialCorollary32
```

is proved by:

```lean
GafniTao.wooleyPolynomialCorollary32_native
```

The proof uses:

- the degree-one collision identity;
- strong induction on degree;
- lower-degree source Corollary 3.2 inputs;
- the source-faithful Sections 7 through 10 descent;
- the vanishing of the operational critical exponent;
- the infimum-to-eventual-bound bridge.

The proof file places the native endpoint on its local `#print axioms` surface.

The exact downstream specialization:

```lean
GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
```

then consumes the native source theorem.

Thus the former chain:

```text
WooleyPolynomialCorollary32
        |
        v
p-adic concentration
```

is no longer conditional.

---

# Native VMVT and Heath-Brown kth-derivative theorem

`WooleyNative.lean` now proves:

```lean
GafniTao.heathBrownVMVTMainConjecture_native
```

directly from:

```lean
GafniTao.wooleyPolynomialCorollary32_native
```

through the existing p-adic concentration bridge.

It then proves:

```lean
GafniTao.heathBrownKthDerivativeTheorem_native
```

by feeding the native VMVT theorem into the already constructed Heath-Brown consumer.

The resulting chain is now:

```text
WooleyPolynomialCorollary32
        |
        v
p-adic concentration
        |
        v
VMVT main conjecture
        |
        v
Heath-Brown kth-derivative theorem
```

with all four stages proved in the development workbench.

This closes the previously open Wooley / VMVT dependency.

---

# Heath-Brown energy campaign

The remaining Heath-Brown problem is no longer the kth-derivative theorem itself.

That dependency is now natively proved.

The workbench also contains a source-shaped finite form of Heath-Brown Lemma 2:

```lean
GafniTao.heathBrownPairCount_card_cast_le_lemma_two
```

with a bound of the form:

```math
\#\mathrm{Pairs}
\le
C_{k,A}
\left(
N+\lambda N^{2}+\lambda^{-2/k}
\right)
\left(
1+\log N
\right)
```

under the expected derivative hypotheses.

The open target is:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

The remaining task is to connect the now-native kth-derivative theorem and pair-count machinery to the three-cell multiplicity-weighted four-zero energy envelope used by Gafni-Tao.

The chain is now:

```text
Wooley source theorem
        |
        v
VMVT
        |
        v
Heath-Brown kth derivative
        |
        v
finite pair-count bounds
        |
        v
HeathBrownZeroEnergyBounds
        |
        v
mu(17/30) <= 7/12
```

Only the final energy-envelope conversion remains mathematically open in this branch.

---

# Pintz Section 3 campaign

The Pintz campaign has also narrowed substantially.

The workbench contains a large native Pintz source chain, including source-scale detector, Mellin, Halasz, and corollary machinery.

The source-facing theorem:

```lean
PintzTheoremOnePrime
```

is defined using the genuine analytic-multiplicity zero count and the source exponent structure.

The workbench proves:

```lean
GafniTao.pintzTwentyThreeTwentyFourCutoff_of_theoremOnePrime
```

which shows that:

```lean
PintzTheoremOnePrime
```

implies exactly:

```lean
PintzTwentyThreeTwentyFourCutoff
```

The remaining mathematical gap is therefore upstream of the cutoff itself.

The current chain is:

```text
native Pintz source machinery
        |
        v
PintzTheoremOnePrime
        |
        v
PintzTwentyThreeTwentyFourCutoff
        |
        v
small-Delta Gafni-Tao sample
```

The implication from `PintzTheoremOnePrime` to the published `23/24` cutoff is already proved.

`PintzTheoremOnePrime` itself remains a source theorem interface at the current snapshot.

---

# Older optimized Ford contracts

The repository still contains:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordTheorem2
```

with the published optimized constants.

These are no longer required to close the general Gafni-Tao theorem because the native Pintz/VK route supplies sufficient near-one inputs.

They should therefore be classified as:

```text
source-fidelity / optimized Ford objectives
```

rather than:

```text
blockers to the core Gafni-Tao theorem
```

`FordAsymptoticZeroFree`, by contrast, now has the native proof:

```lean
GafniTao.ford_asymptotic_zero_free_native
```

---

# Integration frontier

The largest non-mathematical task remains release promotion.

The following major theorem families remain outside the current release root:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11

PublishedExponentInputs
Section3Algebra

WooleySourceCriticalBase
WooleyNative

HeathBrown...
Pintz2023...
```

A theorem counts as release-integrated only when:

1. its module is imported by `Extension/GafniTao.lean`;
2. the isolated package builds through that root;
3. its public or source-sensitive endpoints are represented in `Audit.lean`;
4. the actual `#print axioms` output is inspected;
5. the theorem is reachable through the intended final dependency path.

---

# Central audit

The current central audit is:

```text
Extension/GafniTao/Audit.lean
```

It imports:

```lean
import GafniTao
```

and therefore audits only the current release root.

It does **not yet** centrally audit the newer native endpoints:

```lean
ford_asymptotic_zero_free_native
exists_pintz_nearOne_log_density_native

gafniTaoTheorem13_native
gafniTaoTheorem12_native
gafniTaoTheorem13_max_native
gafniTaoTheorem12_max_native

gafniTaoTheorem11_guthMaynard_native

wooleyPolynomialCorollary32_native
heathBrownVMVTMainConjecture_native
heathBrownKthDerivativeTheorem_native

refinedExceptionalUpperExponent_seventeen_thirtieths_le
refinedExceptionalUpperExponent_two_fifteenths_add_le
```

Individual workbench files may contain local `#print axioms` commands.

Those local checks are useful.

They do not replace central audit promotion.

---

# Verification

Run from:

```text
Riemann Zeta/PostGM/GafniTao/Extension
```

Release verification should include:

```bash
lake build
lake env lean GafniTao/Audit.lean
```

and:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

Interpret the scan carefully.

A source-facing `Prop` definition is not itself a theorem.

A theorem in a workbench file is not yet part of the release dependency path.

An external certificate generator is not proof evidence.

The actual Lean dependency output must be inspected.

---

# Source and certificate discipline

The repository contains several artifact classes:

```text
source references
Lean proof modules
certificate data
certificate generators
temporary probes
development artifacts
```

These categories must remain distinct.

Generated certificate data is acceptable when Lean independently verifies the certificate.

External scripts may generate candidate certificate data.

They are not theorem oracles.

Temporary probes, Python environments, caches, compiled files, and extraction debris should not be part of the publication-facing dependency path.

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

Do not modify the frozen foundation to make the extension easier to prove.

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

A publication-facing theorem is accepted only when all applicable conditions hold:

1. The Lean statement matches the intended source theorem.
2. Source parameter ranges and endpoints are correct.
3. Analytic multiplicities are represented correctly.
4. Constants and logarithmic factors are accounted for.
5. No hidden continuity assumption is introduced.
6. No unauthorized epsilon loss is inserted.
7. No project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised restatement supplies the theorem.
8. The theorem is imported through the intended release root.
9. Source-sensitive endpoints appear in the central audit.
10. The isolated package builds.
11. The actual axiom output is inspected.
12. Generated certificates are checked by Lean.
13. Public documentation agrees with the actual dependency path.

---

# Claim discipline

The strongest safe summary of the repository at present is:

> Most of the downstream Gafni-Tao Section 2 mechanism is already release-root integrated and centrally audited. Beyond that release root, the repository contains native Lean proofs of a Vinogradov-Korobov zero-free region, a sufficient Pintz near-one logarithmic density package, exact unconditional Gafni-Tao Theorems 1.3 and 1.2, and the frozen Guth-Maynard `30/13` specialization of Theorem 1.1. The Wooley source Corollary 3.2 target is now also natively proved, and its existing consumer chain yields the VMVT main conjecture input and Heath-Brown's kth-derivative theorem. These newer theorem files have not yet been promoted into the release root and central audit. The mathematical frontier is now concentrated in the Section 3 source inputs: `HeathBrownZeroEnergyBounds` and `PintzTwentyThreeTwentyFourCutoff`.

Do not currently shorten this to:

```text
The Gafni-Tao release package is complete.
```

That is not yet justified.

A more precise short claim is:

```text
Core Gafni-Tao and Wooley/VMVT source chain proved in the workbench;
release integration and two Section 3 source gates remain active.
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

These documents are project-control artifacts, not proof objects.

When documentation and Lean disagree:

```text
actual theorem source
        +
root imports
        +
central audit
```

take precedence.

Then update the documentation.

---

# Near-term execution order

## 1. Promote the native core theorem chain

Integrate:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11
```

into the intended root.

Add the appropriate endpoints to the central audit.

Run the full isolated build and inspect dependencies.

---

## 2. Promote the completed Wooley / VMVT chain

The former Wooley source target is now proved.

Integrate the intended publication dependency path containing:

```text
WooleySourceCriticalBase
WooleyNative
```

and the required dependencies.

Add representative central-audit endpoints:

```lean
wooleyPolynomialCorollary32_native
heathBrownVMVTMainConjecture_native
heathBrownKthDerivativeTheorem_native
```

Do not continue treating Wooley Corollary 3.2 as an open mathematical target.

---

## 3. Close the Heath-Brown energy envelope

Use the now-native kth-derivative theorem together with the existing Heath-Brown pair-count chain to prove:

```lean
HeathBrownZeroEnergyBounds
```

The former VMVT dependency is no longer open.

The remaining task is the passage from the derivative/counting machinery to the actual multiplicity-weighted three-cell zero-energy envelope.

Once that predicate is discharged, combine:

```lean
gafniTaoTheorem13_native
```

with:

```lean
refinedExceptionalUpperExponent_seventeen_thirtieths_le
```

to obtain:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}.
```

---

## 4. Close the Pintz Section 3 cutoff

The implication:

```text
PintzTheoremOnePrime
        |
        v
PintzTwentyThreeTwentyFourCutoff
```

is already proved.

The immediate mathematical target is therefore the source theorem feeding that implication.

Once the source theorem is discharged, combine the resulting cutoff with:

```lean
refinedExceptionalUpperExponent_two_fifteenths_add_le
```

and the native general theorem.

This closes the sufficiently-small-Delta sample on the formalized range:

```math
0<\Delta\le\frac{1}{100}.
```

---

## 5. Synchronize Section 3 integration

After each remaining source input closes:

1. import the source chain into the release root;
2. add central audit entries;
3. connect the source input to `Section3Algebra`;
4. create the unconditional sample theorem;
5. update the Crosswalk, Shitlist, Architecture, and README.

---

## 6. Full Section 3 optimizer

Only after the displayed sample bounds are closed should the optional full Figure 4 envelope become the priority.

Pin all numerical source tables.

Reduce the optimization to finitely many exact cells.

Certify those cells in Lean.

Do not use floating-point output as proof evidence.

---

## 7. Final release audit

Before the final completion claim:

1. run the isolated package build;
2. run `Audit.lean`;
3. inspect all nonstandard axiom dependencies;
4. scan for unfinished declarations;
5. remove or classify temporary probes, Python environments, and caches;
6. synchronize all project-control documentation;
7. confirm that the public theorem path is reachable from the root.

---

# Repository workflow

`push_to_github.bat` remains the owner-operated publication step.

A GitHub push is a selected public snapshot.

It is not proof verification.

Agents must not push unless separately instructed.

Use milestone commit messages only after the stated theorem is genuinely closed.

Examples:

```bat
push_to_github.bat "PostGM Gafni-Tao: integrate native core and Wooley VMVT chain"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close Heath-Brown Section 3 energy input"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close Pintz 23-24 cutoff"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close first published Section 3 sample"
```

---

# Completion condition

The core theorem phase is release-complete when:

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

is imported, built, and centrally audited.

The Wooley / VMVT dependency phase is mathematically closed when:

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
```

is promoted into the same release dependency path.

The full paper-facing phase additionally requires:

```text
native Heath-Brown kth derivative
             |
             v
HeathBrownZeroEnergyBounds
             |
             v
mu(17/30) <= 7/12
```

and:

```text
Pintz source theorem
             |
             v
Pintz 23/24 cutoff
             |
             v
small-Delta published bound
```

together with any claimed full numerical optimizer.

Until then:

**the core Gafni-Tao theorem and Wooley/VMVT source chain are proved in the development workbench; release integration and the two published Section 3 source gates are the active front.**