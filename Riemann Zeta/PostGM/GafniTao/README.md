# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has crossed an important boundary.

Most of the downstream Gafni-Tao Section 2 transfer mechanism is already integrated into the isolated package root and central audit.

Separately, the development workbench now contains native Lean theorems that close the remaining analytic inputs required for the general Gafni-Tao exceptional-exponent theorem and then prove:

```lean
GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native
```

The workbench also contains the full frozen Guth-Maynard `A0 = 30/13` specialization of Theorem 1.1:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

including:

- the all-interval threshold `theta > 17/30`;
- the almost-all threshold `theta > 2/15`;
- a single measurable exceptional set of ordinary natural density zero for the almost-all statement.

These native theorem files are **not yet imported by the release root `Extension/GafniTao.lean` or represented in the central `Audit.lean`**.

The correct current claim is therefore:

> **The general Gafni-Tao theorem has been proved in the development workbench, while release-root integration and central dependency audit remain pending.**

The active mathematical frontier has moved to the published Section 3 inputs and numerical consequences, especially the Heath-Brown four-zero energy input and the Pintz `23/24` cutoff.

The newest development also contains a large source-faithful Wooley / VMVT program intended to close the analytic mean-value inputs required by that campaign.

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
- the explicit formula;
- second and fourth moments;
- the equation (2.7) strip argument;
- limiting assembly;
- the near-one zero-free and density inputs;
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

That downstream machine is substantially root-integrated.

The newer native source-input route is:

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

This second route currently exists in workbench files rather than the release root.

---

# Release root versus development workbench

The distinction is now important enough to be explicit.

## Release root

The production-style root is:

```text
Extension/GafniTao.lean
```

It currently imports the established downstream Gafni-Tao mechanism and the older Ford analytic/combinatorial source campaign through:

```text
FordLemma33Finite
FordCountMonotone
FordLemma63MomentIntegral
ZeroEnergyLocal
```

It does **not yet** import:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11
PublishedExponentInputs
Section3Algebra
HeathBrown...
Wooley...
```

## Development workbench

The repository nevertheless contains substantial additional Lean mathematics beyond the release root.

The most important development endpoints now include:

```lean
GafniTao.ford_asymptotic_zero_free_native
GafniTao.exists_pintz_nearOne_log_density_native

GafniTao.gafniTaoTheorem13_native
GafniTao.gafniTaoTheorem12_native
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native

GafniTao.gafniTaoTheorem11_guthMaynard_native
```

These must be promoted deliberately into the root and central audit before they become publication-facing release claims.

---

# Current status table

| Proof layer | Mathematical state | Release-root state |
|---|---|---|
| Exact exceptional set | Implemented | Integrated |
| `mu_delta` / `mu` machinery | Implemented | Integrated |
| Multiplicity-weighted `N` | Implemented | Integrated |
| Multiplicity-weighted `N*` | Implemented | Integrated |
| `A` / `A*` exponent machinery | Implemented | Integrated |
| Local arithmetic entry | Implemented | Integrated |
| Brun-Titchmarsh localization | Implemented | Integrated |
| Native sharp explicit formula | Implemented | Integrated |
| Complex Fourier bump | Implemented | Integrated |
| Second moment | Implemented | Integrated |
| Fourth moment | Implemented | Integrated |
| Finite half-open strips | Implemented | Integrated |
| Equation (2.7) | Implemented | Integrated |
| Limit assembly | Implemented | Integrated |
| Global exceptional cover | Implemented | Integrated |
| Conditional Theorem 1.3 | Implemented | Integrated |
| Conditional Theorem 1.2 | Implemented | Integrated |
| Frozen GM `30/13` consumer | Implemented | Integrated |
| Qualitative Ford exponential sum | Proved | Workbench |
| Qualitative Ford zeta growth | Proved | Workbench |
| Native Ford asymptotic zero-free region | Proved | Workbench |
| Native Pintz near-one package | Proved | Workbench |
| Exact unconditional Theorem 1.3 | Proved | Workbench |
| Exact unconditional Theorem 1.2 | Proved | Workbench |
| Theorem 1.1, GM `30/13` specialization | Proved | Workbench |
| Section 3 epsilon-removal algebra | Proved | Workbench |
| First sample exponent algebra | Proved conditional on Heath-Brown input | Workbench |
| Second sample exponent algebra | Proved conditional on Pintz cutoff | Workbench |
| Heath-Brown finite Lemma 2 | Substantially proved | Workbench |
| Heath-Brown zero-energy envelope | Source closure still open | Workbench |
| Pintz `23/24` cutoff | Source closure still open | Workbench |
| Wooley source / VMVT campaign | Active, substantial | Workbench |
| Published first sample | Awaiting Heath-Brown input | Open |
| Published small-Delta sample | Awaiting Pintz cutoff | Open |
| Full Section 3 optimizer | Open | Open |
| Final release audit | Open | Open |

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

It defines:

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
- logarithmic derivative expansions;
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

These are assembled into a bound for the complete large-zero-sum event.

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

The workbench now contains:

```lean
GafniTao.ford_asymptotic_zero_free_native
```

with type:

```lean
FordAsymptoticZeroFree
```

This is a genuine discharge of the earlier existential zero-free source contract.

The proof uses:

- the qualitative global Ford/Richert zeta-growth bound;
- the Vinogradov-Korobov scale;
- the five-frequency trigonometric detector;
- an explicit positive zero-free constant;
- conjugation symmetry for negative zero ordinates.

Thus the zero-free branch is no longer an open mathematical prerequisite for the general Gafni-Tao theorem.

It remains an integration prerequisite for the release package.

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

This route is sufficient for the general Gafni-Tao theorem.

It does **not** reproduce Ford's older optimized `58.05` / `log^16` source package.

That optimized contract may remain of independent source-fidelity interest, but it is no longer a blocker for the native general theorem.

---

# Exact native Theorems 1.3 and 1.2

The workbench now contains:

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
0 < \theta < 1
```

It supplies internally:

- the frozen Guth-Maynard smooth cutoff;
- the native sharp explicit formula;
- the native Pintz/Ford near-one package;
- the native zero-free input.

The ordinary theorem:

```lean
GafniTao.gafniTaoTheorem12_native
```

then proves:

```math
\mu(\theta)
\le
\mathrm{ordinaryExceptionalUpperExponent}(\theta)
```

The workbench also contains the alternate upper-half max formulations:

```lean
GafniTao.gafniTaoTheorem13_max_native
GafniTao.gafniTaoTheorem12_max_native
```

The project should preserve the distinction between the exact source exponent theorem and the alternate max-form statements.

---

# Native Theorem 1.1

The workbench now contains the complete frozen Guth-Maynard specialization:

```lean
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

with:

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

The almost-all branch has been strengthened to produce a **single measurable exceptional set** `E` such that:

```text
NaturalDensityZero E
```

and the short-interval PNT holds outside `E`.

Representative endpoints are:

```lean
GafniTao.gafniTaoTheorem11_almostAll_guthMaynard_singleSet_native
GafniTao.gafniTaoTheorem11_guthMaynard_native
```

---

# Section 3

The active mathematical frontier is now Section 3.

## Published source interfaces

`PublishedExponentInputs.lean` records the exact source-facing inputs still required for the displayed sample bounds.

These include:

```lean
GafniTao.PintzFirstDensitySegment
GafniTao.PintzTwentyThreeTwentyFourCutoff
GafniTao.HeathBrownZeroEnergyBounds
```

These are predicates on the genuine project zero-count and zero-energy objects.

No separate numerical surrogate exponent has been introduced.

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

Thus the remaining mathematical task for this sample is the source closure of the Heath-Brown four-zero energy input, not the Gafni-Tao optimization algebra.

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

The sufficiently-small range is therefore already explicit.

The outstanding task is to discharge the Pintz cutoff source predicate.

---

# Heath-Brown source campaign

The repository now contains a large Heath-Brown kth-derivative and refined-counting development.

A source-shaped finite form of Heath-Brown Lemma 2 has already been obtained:

```lean
GafniTao.heathBrownPairCount_card_cast_le_lemma_two
```

with bound of the form:

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

under the expected differentiability and kth-derivative hypotheses.

This is substantial progress toward the Section 3 energy input.

It does not yet prove:

```lean
GafniTao.HeathBrownZeroEnergyBounds
```

The remaining work is to connect the derivative/counting machinery to the actual multiplicity-weighted four-zero energy envelope used by Gafni-Tao.

---

# Wooley / VMVT source campaign

The latest public progress commit substantially expands the Wooley branch.

The development now contains source-level infrastructure for:

- finitely supported integer coefficient sequences;
- exact normalized polynomial means;
- conditioned polynomial means;
- source boxing and unboxing;
- coefficient-one specialization;
- translation-dilation invariance;
- initial conditioning;
- p-adic separation;
- polynomial-system refinement;
- Sections 6, 7, and 8 arithmetic;
- source-to-p-adic specialization.

The source target is represented by:

```lean
GafniTao.WooleyPolynomialCorollary32
```

This remains a target proposition.

The workbench already contains source-sequence consumers for substantial pieces of Wooley Sections 6 through 8.

For example:

```lean
GafniTao.wooleySourcePolynomial_lemma_6_3
```

is a source-sequence form of Wooley Lemma 6.3.

The exact downstream specialization is also already formalized:

```lean
GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
```

which proves that the full source-faithful polynomial Corollary 3.2 implies the precise coefficient-one p-adic concentration statement needed by the critical VMVT consumer.

Thus the current Wooley problem is sharply isolated:

```text
prove source Corollary 3.2
        |
        v
existing source-to-p-adic bridge
        |
        v
critical VMVT consumer
        |
        v
Section 3 source campaign
```

---

# Older optimized Ford contracts

The repository still contains the source-facing contracts:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordTheorem2
```

with the published optimized constants.

These are no longer required to close the general Gafni-Tao theorem because the native Pintz/Ford route supplies sufficient near-one inputs by a different proved path.

They should therefore be classified as:

```text
source-fidelity / optimized Ford objectives
```

rather than:

```text
blockers to the general Gafni-Tao theorem
```

The distinction matters.

`FordAsymptoticZeroFree`, by contrast, now has the native proof:

```lean
GafniTao.ford_asymptotic_zero_free_native
```

---

# Integration frontier

The largest immediate non-mathematical task is now release integration.

The following major files exist outside the current release root:

```text
FordAsymptoticZeroFree
PintzNearOneNative
NativeTheorems
Theorem11

PublishedExponentInputs
Section3Algebra

HeathBrown...
Wooley...
```

Before any publication-facing completion claim, the intended theorem path must be deliberately promoted.

A theorem counts as release-integrated only when:

1. its module is imported by `Extension/GafniTao.lean`;
2. the isolated package builds through that root;
3. its public/source-sensitive endpoints are represented in `Audit.lean`;
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

and therefore currently audits only the existing release root.

It does **not yet** centrally audit:

```lean
ford_asymptotic_zero_free_native
exists_pintz_nearOne_log_density_native

gafniTaoTheorem13_native
gafniTaoTheorem12_native
gafniTaoTheorem13_max_native
gafniTaoTheorem12_max_native

gafniTaoTheorem11_guthMaynard_native

refinedExceptionalUpperExponent_seventeen_thirtieths_le
refinedExceptionalUpperExponent_two_fifteenths_add_le

Heath-Brown workbench endpoints
Wooley workbench endpoints
```

Some of those individual files contain their own `#print axioms` commands.

That is useful local dependency checking.

It does not replace promotion into the central audit.

---

# Verification

Run from:

```text
Riemann Zeta/PostGM/GafniTao/Extension
```

The release verification should include:

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

The repository contains:

```text
source references
Lean proof modules
certificate data
certificate generators
temporary probes
development artifacts
```

These categories must remain distinct.

Generated data is acceptable when Lean independently verifies the certificate.

Temporary probes and cache artifacts should not be part of the publication-facing dependency path.

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
5. No hidden continuity assumptions are introduced.
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

> Most of the downstream Gafni-Tao Section 2 mechanism is already integrated and centrally audited. Beyond that release root, the repository now contains native Lean proofs of a Vinogradov-Korobov zero-free region, a sufficient Pintz near-one logarithmic density package, exact unconditional Gafni-Tao Theorems 1.3 and 1.2, and the frozen Guth-Maynard `30/13` specialization of Theorem 1.1. These newer theorem files have not yet been promoted into the release root and central audit. The mathematical frontier has moved to the Section 3 source inputs: the first sample algebra is complete conditional on the Heath-Brown four-zero energy envelope, and the second sample algebra is complete conditional on the Pintz `23/24` cutoff. A large Heath-Brown derivative/counting campaign and an expanding source-faithful Wooley / VMVT campaign are actively attacking those remaining inputs.

Do not currently shorten this to:

```text
The Gafni-Tao release package is complete.
```

That is not yet justified.

A more precise short claim is:

```text
Core Gafni-Tao theorem proved in the workbench; release integration and Section 3 remain active.
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

This is now the shortest route to turning the workbench core theorem into a release theorem.

---

## 2. Close the Heath-Brown energy input

Continue from the source-scale finite Lemma 2 development toward:

```lean
HeathBrownZeroEnergyBounds
```

Once that predicate is discharged, combine:

```lean
gafniTaoTheorem13_native
```

with:

```lean
refinedExceptionalUpperExponent_seventeen_thirtieths_le
```

to obtain the first published sample:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}
```

without external analytic assumptions.

---

## 3. Close the Pintz Section 3 cutoff

Prove:

```lean
PintzTwentyThreeTwentyFourCutoff
```

from the pinned Pintz source argument.

Then combine it with:

```lean
refinedExceptionalUpperExponent_two_fifteenths_add_le
```

and the native general theorem.

This closes the sufficiently-small-Delta sample on the already formalized range:

```math
0<\Delta\le\frac{1}{100}.
```

---

## 4. Continue the Wooley source theorem

The current target is:

```lean
WooleyPolynomialCorollary32
```

The repository already has:

- source means;
- boxing;
- coefficient specialization;
- source Sections 6 through 8;
- the source-to-p-adic consumer.

Complete the remaining Wooley source sections needed to prove Corollary 3.2.

Then consume the already-proved:

```lean
wooleyMonomialPadicConcentration_of_polynomialCorollary32
```

bridge.

---

## 5. Synchronize Section 3 integration

After each source input closes:

1. import the corresponding chain into the release root;
2. add central audit entries;
3. connect the source input to `Section3Algebra`;
4. create the unconditional sample theorem;
5. update the Crosswalk and Architecture.

---

## 6. Full Section 3 optimizer

Only after the displayed sample bounds are closed should the optional full Figure 4 envelope become the priority.

Pin all numerical source tables.

Reduce the optimization to finitely many exact cells.

Certify the cells in Lean.

Do not use floating-point output as proof evidence.

---

## 7. Final release audit

Before the final completion claim:

1. run the isolated package build;
2. run `Audit.lean`;
3. inspect all nonstandard axiom dependencies;
4. scan for unfinished declarations;
5. remove or classify temporary probes and caches;
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
push_to_github.bat "PostGM Gafni-Tao: integrate native Theorems 1.3, 1.2 and 1.1"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close Heath-Brown Section 3 energy input"
```

```bat
push_to_github.bat "PostGM Gafni-Tao: close first published Section 3 sample"
```

---

# Completion condition

The core theorem phase is release-complete when the dependency graph is:

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

and that path is imported, built, and centrally audited.

The full paper-facing phase additionally requires:

```text
Heath-Brown source input
             |
             v
mu(17/30) <= 7/12
```

and:

```text
Pintz 23/24 source cutoff
             |
             v
small-Delta published bound
```

together with any claimed full numerical optimizer.

Until then:

**the core Gafni-Tao theorem is proved in the development workbench; release integration and the published Section 3 source inputs are the active front.**