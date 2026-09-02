# Gafni-Tao exceptional intervals

## Status

**Active isolated formalization.**

The project has progressed well beyond foundational scaffolding.

Most of the downstream Section 2 zero-density-to-exceptional-set mechanism is now implemented in Lean, including:

- the exact Mangoldt short-interval exceptional set;
- Lebesgue-measure exceptional exponents;
- multiplicity-weighted zero counting;
- the four-zero additive-energy quantity `N*` and exponent `A*`;
- local arithmetic localization and multiplicative covering;
- Brun-Titchmarsh replacement estimates;
- a native sharp truncated explicit formula;
- finite half-open zero strips;
- physical `L-infinity`, `L2`, and `L4` zero-sum estimates;
- second- and fourth-moment Markov bounds;
- the equation (2.7) exceptional-set decomposition;
- the small-density and right-edge branches;
- epsilon and finite-strip limiting machinery;
- local-to-global exceptional-measure assembly;
- conditional assembled max-forms of Gafni-Tao Theorems 1.2 and 1.3;
- the frozen Guth-Maynard `30/13` ordinary-density consumer and associated threshold arithmetic.

The main mathematical frontier has moved upstream into Ford's source analysis.

There are now three distinct Ford layers:

1. a large **root-integrated analytic and combinatorial source chain**;
2. a **partially synchronized central audit** covering substantial pieces of that chain;
3. a still-unintegrated **development workbench** that now proves qualitative versions of Ford's exponential-sum and zeta-growth conclusions.

The strongest new development result is no longer merely infrastructure.

The workbench contains a proved qualitative exponential-sum theorem:

```lean
GafniTao.ford_exponential_sum_qualitative
```

of the form:

```math
\left\|
\sum_{N<n\le R}
(n+u)^{-it}
\right\|
\le
C
N^{1-\frac{1}{3000000\lambda^{2}}}
```

for an explicit internally constructed coefficient `C`.

It also contains a proved qualitative Richert-Ford zeta-growth theorem:

```lean
GafniTao.ford_qualitative_general_zeta_growth
```

realizing:

```math
\left|
\zeta(\sigma+it)
\right|
\le
A
|t|^{B(1-\sigma)^{3/2}}
(\log |t|)^{2/3}
```

for explicit positive internally constructed constants `A` and `B`.

A further development theorem:

```lean
GafniTao.fordLocalDiskZeroCount_le_general_majorant
```

turns such a general zeta-growth estimate into an explicit multiplicity-weighted local zero-count bound of the form needed by the Vinogradov-Korobov argument.

These results show that the qualitative Ford method has now been carried through a substantial analytic path in Lean.

They are **not yet part of the package root or central audit**, and they do **not** yet discharge the optimized source contracts used by the current Gafni-Tao endpoint.

The principal source contracts remain open:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordAsymptoticZeroFree
```

The optimized exponential-sum contract also remains open:

```lean
GafniTao.FordTheorem2
```

The complete Gafni-Tao formalization is therefore **not yet claimed**.

---

# Purpose

This directory is the isolated post-Guth-Maynard program for formalizing Ayla Gafni and Terence Tao's paper:

*On the number of exceptional intervals to the prime number theorem in short intervals*

arXiv:2505.24017v1.

The target is the paper's actual zero-density-to-exceptional-set argument, including:

- the ordinary second-moment argument;
- the fourth-moment refinement;
- the multiplicity-sensitive four-zero energy;
- the near-one zero-density and zero-free inputs;
- the ordinary-density consequences of Guth-Maynard;
- the published numerical consequences.

The intended endpoint is not merely a theorem with a numerically similar conclusion.

The objective is to formalize the mathematical dependency chain used by the paper closely enough that the final theorem can be audited against the source argument.

This work does not prove the Riemann Hypothesis, and nothing in this directory should be described as doing so.

---

# Current mathematical state

The downstream Gafni-Tao architecture is approximately:

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
\mathrm{equation\ (2.7)\ strip\ alternatives}
```

```math
\longrightarrow
\mathrm{local\ exceptional\text{-}measure\ bounds}
```

```math
\longrightarrow
\mathrm{finite\text{-}strip\ and\ }\varepsilon\mathrm{\ limits}
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

Most of this transfer chain now exists as Lean theorems.

The unresolved dependency is primarily upstream:

```text
Ford source analysis
        |
        +---------------------+
        |                     |
        v                     v
zero-free region        near-one density
        |                     |
        +----------+----------+
                   |
                   v
          right-edge decay
                   |
                   v
      existing GT Section 2 chain
                   |
                   v
       unconditional GT theorem
```

---

# Current status

| Proof layer | Current state |
|---|---|
| Exact exceptional set | Implemented |
| `mu_delta` / `mu` framework | Implemented through current consumer interfaces |
| Multiplicity-weighted `N` | Implemented |
| Multiplicity-weighted `N*` | Implemented |
| `A` / `A*` exponent machinery | Implemented through current consumer interfaces |
| Chebyshev/Mangoldt interval identities | Implemented |
| Local multiplicative cover | Implemented |
| Brun-Titchmarsh localization | Implemented |
| Sharp truncated explicit formula | Native theorem implemented |
| Complex Fourier bump | Implemented |
| Second moment | Implemented |
| Fourth moment | Implemented |
| Finite half-open strip assembly | Implemented |
| Equation (2.7) | Implemented |
| Right-edge consumer | Conditional on near-one source inputs |
| Limit assembly | Implemented |
| Global exceptional cover | Implemented |
| Refined Theorem 1.3 max-form | Implemented conditionally |
| Ordinary Theorem 1.2 max-form | Implemented conditionally |
| Frozen GM `30/13` consumer | Implemented |
| Ford analytic detector / K-formula chain | Root-integrated |
| Ford Vinogradov / Lemma 5.1 source chain | Root-integrated |
| Ford Lemma 3.2 source chain | Root-integrated |
| Ford Lemma 3.3 finite source theorem | Root-integrated and centrally audited |
| Ford Lemma 3.4 arithmetic / scheduling machinery | Substantially centrally audited |
| Effective canonical prime packet | Centrally audited |
| Ford count monotonicity | Root-integrated and centrally audited |
| Ford Lemma 6.3 moment-integral entry | Root-integrated |
| Qualitative Ford exponential-sum theorem | Proved in workbench, not root-integrated |
| Qualitative Ford zeta-growth theorem | Proved in workbench, not root-integrated |
| Qualitative local zero-count theorem | Proved in workbench, not root-integrated |
| Optimized `FordTheorem2` | Source contract still open |
| Optimized `FordZetaGrowthBound` | Source contract still open |
| `FordNearOneDensityEstimate` | Source contract still open |
| `FordAsymptoticZeroFree` | Source contract still open |
| Exact unconditional Theorem 1.3 | Open |
| Exact unconditional Theorem 1.2 | Open |
| Theorem 1.1 | Open |
| Pintz / Heath-Brown Section 3 inputs | Open |
| Published numerical sample bounds | Open |
| Certified full Section 3 optimizer | Open |
| Final isolated release audit | Open |

---

# Implemented Gafni-Tao theorem spine

## 1. Exceptional sets

The formalization defines the actual Mangoldt short-interval exceptional set rather than a finite sampling proxy.

The mathematical object is:

```math
E_{\delta}(X,\theta)
=
\left\{
x\in[X,2X]:
\left|
\psi\!\left(x+x^{\theta}\right)-\psi(x)-x^{\theta}
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
- finite-measure facts;
- threshold monotonicity;
- fixed-power bounds;
- epsilon-exponent bounds;
- eventual-empty behavior;
- countable positive-threshold reduction.

---

## 2. Zero counting and additive energy

The project contains multiplicity-sensitive infrastructure for the nontrivial zeros of the Riemann zeta function.

The ordinary count is represented by:

```math
N(\sigma,T)
```

and the four-zero additive-energy quantity by:

```math
N^{\ast}(\sigma,T)
```

The four-zero quantity counts ordered zero occurrences with analytic multiplicity.

The associated exponent interfaces `A` and `A*` feed the second- and fourth-moment branches.

---

## 3. Local arithmetic entry

The local arithmetic chain contains:

- the Mangoldt interval identity;
- prime and prime-power decomposition;
- prime-power error control;
- local Brun-Titchmarsh estimates;
- replacement of the variable short interval by the local `x/tau` scale;
- finite multiplicative covering of `[X,2X]`;
- local discrepancy and zero-sum interfaces.

This connects the original exceptional event to the local analytic argument.

---

## 4. Native sharp truncated explicit formula

The explicit-formula branch has a native endpoint:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting sharp-Perron chain handles:

- finite Mangoldt Perron identities;
- logarithmic-derivative expansions;
- contour rectangles;
- residue calculations;
- analytic zero multiplicity;
- right, horizontal, and left edges;
- functional-equation input;
- selected good heights;
- low-height treatment;
- arbitrary real endpoints;
- endpoint-uniform cutoff estimates.

The physical range includes:

```math
2 \le T \le x
```

The central audit includes:

```lean
GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The sharp explicit formula is no longer one of the principal unresolved analytic inputs.

---

## 5. Second and fourth moments

The second- and fourth-moment branches are implemented at the multiplicity-sensitive level required by the source argument.

The second moment consumes the ordinary zero count.

The fourth moment consumes the actual multiplicity-weighted four-zero energy.

The refined route therefore retains the `A*` contribution.

---

## 6. Equation (2.7)

The finite half-open strip decomposition and equation (2.7) machinery are implemented.

The strip alternatives are:

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

Representative results include:

```lean
GafniTao.equation27StripMeasure_epsilonBound_of_second_or_fourth
GafniTao.equation27StripMeasure_epsilonBound_of_exponent_upper_bounds
GafniTao.eventually_equation27StripLargeSet_eq_empty_of_rightEdge
GafniTao.equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
```

---

## 7. Limit and global-cover assembly

The project contains the limiting machinery required to pass from finite strips and epsilon-dependent estimates to fixed-power exceptional-measure bounds.

Representative theorems include:

```lean
GafniTao.exists_refined_limit_witness
GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The downstream argument therefore reaches the actual global exceptional exponent.

---

# Conditional Gafni-Tao endpoints

## Refined max-form

The current assembled refined endpoint is:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
```

Schematically:

```math
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal{R}(\theta)
\right\}
```

where the refined term retains both ordinary zero density and four-zero additive energy.

This is a genuine Lean theorem.

It remains conditional on named source inputs.

It is not yet the completed unconditional source Theorem 1.3.

---

## Ordinary max-form

The current ordinary endpoint is:

```lean
GafniTao.gafniTaoTheorem12_max_conditional
```

Schematically:

```math
\mu(\theta)
\le
\max
\left\{
1-\theta,\,
\mathcal{O}(\theta)
\right\}
```

It is also conditional.

---

# Exact source-theorem closure

The principal refined source target retains the epsilon infimum.

Schematically:

```math
\mu(\theta)
\le
\inf_{\varepsilon>0}
\sup_{\substack{
0\le\sigma<1\\
A(\sigma)\ge(1-\theta)^{-1}-\varepsilon
}}
\min
\left(
(1-\theta)(1-\sigma)A(\sigma)+2\sigma-1,\,
(1-\theta)(1-\sigma)A^{\ast}(\sigma)+4\sigma-3
\right)
```

The epsilon infimum must not be silently removed.

The final project should expose:

```text
exact source Theorem 1.3
```

and separately retain:

```text
max-form corollary
```

The same distinction applies to Theorem 1.2.

---

# Frozen Guth-Maynard consumer

The frozen Guth-Maynard density theorem is connected to the Gafni-Tao exponent language.

The central audit includes:

```lean
GafniTao.guthMaynard_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_guthMaynard
GafniTao.frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_thirty_thirteenths
GafniTao.seventeen_thirtieths_eq_uniform_all_threshold
GafniTao.two_fifteenths_eq_uniform_almost_all_threshold
```

Thus:

```math
A_{0}
=
\frac{30}{13}
```

and its elementary threshold arithmetic are already represented in Lean.

---

# Ford source program

## Layer A: integrated analytic machinery

The root-integrated Ford analytic branch contains substantial source analysis through:

```text
trigonometric positivity
Fourier kernels
Euler products and prime-power expansions
Ford Lemma 5.1
cotangent detector kernels
detector residues
finite detector rectangles
physical detector edges
left-line analysis
Laplace inversion
K-function residues and contours
K zero series
infinite-rectangle limits
native K-formula
explicit zeta estimates
logarithmic-derivative infrastructure
```

Representative audited endpoints include:

```lean
GafniTao.ford_lemma_5_1
GafniTao.fordZetaDetector_rectangleIntegral_eq_residue_sum
GafniTao.fordZetaDetector_rectangleIntegral_eq_explicit_sum
GafniTao.fordK_infinite_rectangle_native
GafniTao.fordK_formula_native
GafniTao.fordK_formula_with_log_error_native
```

This is genuine integrated Ford analysis.

It does not by itself discharge the optimized source contracts.

---

# Ford Vinogradov and Lemma 5.1 derivation

The root also contains a source-faithful derivation chain covering:

```text
Vinogradov moments
power interpolation
logarithmic Taylor estimates
phase estimates
Holder steps
fiber decompositions
equations (5.2), (5.3), and (5.4)
spacing counts
tent weights and tent series
resonance counting
shift and averaging
exponential normalization
real-parameter source interface
```

The source-scale real-parameter layer is important because Ford's published parameters are not all naturally integral.

The root also contains the algebraic branch:

```text
Vandermonde determinant
polynomial systems
finite differences
integer polynomial systems
complete counts
prime selection
Newton congruence
```

---

# Ford Lemma 3.2

Ford Lemma 3.2 has advanced from infrastructure to a root-integrated source assembly.

The chain now contains:

```text
power-residue fibres
        |
        v
Jacobian prime avoidance
        |
        v
prime-power Newton systems
        |
        v
prime-power lifts
        |
        v
B-star bounds
        |
        v
collision counts
        |
        v
S3 / S4 / S6 analysis
        |
        v
equation (3.4)
        |
        v
equation (3.7)
        |
        v
maximal K and repeated-coordinate control
        |
        v
good-prime equation (3.3)
        |
        v
finite Lemma 3.2 core
        |
        v
source-scale Lemma 3.2
```

The root imports:

```text
FordPowerResidueFiber
FordJacobianAvoidance
FordLemma32Arithmetic
FordPrimePowerNewton
FordPrimePowerTriangular
FordSourcePrimePowerSystem
FordPrimePowerLifts
FordBStarBound
FordBStarSource
FordBStarCongruence
FordFiniteCollision
FordBStarCollision
FordS6Setup
FordS6Signature
FordS6Cauchy
FordS6ToL
FordEquation37S6
FordEquation34AMGM
FordEquation34Fourier
FordFourierCollision
FordEquation34Count
FordEquation34S3Count
FordEquation34SourceS3
FordS4ToS6
FordS4BoundaryRange
FordS4Diagonal
FordS4Resolution
FordEquation37Source
FordEquation33Source
FordKMaximal
FordKRepeatedCover
FordKRepeatedBound
FordKContradiction
FordEquation33GoodPrime
FordLemma32Finite
FordLemma32Source
FordPrimeSet
```

The source-level chain includes a canonical prime-packet formulation.

The previous prime-packet placement gap has also moved forward: the central audit now includes effective estimates showing that the canonical Ford prime packet eventually lies in the required relative interval, including:

```lean
GafniTao.eventually_fordPrimeInterval_card_ge
GafniTao.fordPrimeSet_le_of_interval_card
GafniTao.eventually_fordPrimeSet_le_relative
GafniTao.eventually_fordPrimeSet_le_two_mul
GafniTao.exists_fordPrimeSet_relative_threshold
```

Thus the old standalone assumption that the selected packet lies below `2 * M` is no longer the only route available.

---

# Beyond Lemma 3.2

The root has now moved into later Ford source mathematics.

It imports:

```text
FordLemma33Finite
FordCountMonotone
FordLemma63MomentIntegral
```

The central audit explicitly includes:

```lean
GafniTao.ford_lemma_3_3_finite_source
```

along with substantial Lemma 3.4 exponent and scheduling arithmetic:

```lean
GafniTao.FordPhiSchedule.le_inv_r
GafniTao.ford_lemma_3_4_inner_exponent_eq
GafniTao.ford_lemma_3_4_exponent_cancellation
GafniTao.ford_lemma_3_4_final_exponent_eq
GafniTao.ford_lemma_3_4_terminal_constant
GafniTao.ford_lemma_3_4_terminal_power
GafniTao.ford_lemma_3_4_canonical_terminal_constant
```

The central audit also contains monotonicity of the complete Ford counts:

```lean
GafniTao.fordKCount_mono_Q
GafniTao.fordLCount_mono_Q
```

The root's `FordLemma63MomentIntegral` branch connects the Vinogradov moment machinery to the later exponential-sum analysis.

This means the formal source campaign has moved materially beyond Lemma 3.2.

---

# Qualitative Ford breakthrough in the development workbench

A still-unintegrated workbench now proves a complete qualitative exponential-sum theorem.

The theorem is:

```lean
GafniTao.ford_exponential_sum_qualitative
```

with:

```lean
FordExponentialSumEstimate
  fordQualitativeCoefficient
  3000000
```

The proof assembles six logarithmic-scale regimes and handles small integer endpoints.

The exponent has the Vinogradov-Korobov form:

```math
1-\frac{1}{3000000\lambda^{2}}
```

This does **not** identify the coefficient with Ford's optimized source constants.

It is nevertheless a complete proved qualitative exponential-sum estimate.

---

# Qualitative Richert-Ford zeta growth

The workbench also defines the general interface:

```lean
GafniTao.FordGeneralZetaGrowthBound
```

and proves:

```lean
GafniTao.ford_qualitative_general_zeta_growth
```

for explicit internally constructed positive constants.

The theorem has the source-shaped form:

```math
\left|
\zeta(\sigma+it)
\right|
\le
A
|t|^{B(1-\sigma)^{3/2}}
(\log |t|)^{2/3}
```

This is a major proof-of-method milestone.

It establishes the qualitative Richert-Ford growth shape natively without relabeling it as the optimized Ford source contract.

---

# Qualitative local zero count

The workbench further proves:

```lean
GafniTao.fordLocalDiskZeroCount_le_general_majorant
```

which turns any:

```lean
FordGeneralZetaGrowthBound A B
```

into an explicit multiplicity-weighted local zero-count majorant.

The majorant visibly contains the expected terms:

```text
B * R^(3/2) * log t
log A
log(1/R)
log log t
```

together with explicit detector-kernel constants.

This moves the qualitative Ford chain toward the zero-free side of the Gafni-Tao near-one input.

---

# What remains open in Ford

## Optimized Ford Theorem 2

The source contract:

```lean
GafniTao.FordTheorem2
```

uses Ford's optimized constants:

```text
9.463
133.66
```

The qualitative theorem does not prove this optimized statement.

The exact source constants therefore remain open.

---

## Optimized Ford zeta-growth theorem

The source contract:

```lean
GafniTao.FordZetaGrowthBound
```

records the optimized estimate:

```math
\left|
\zeta(\sigma+it)
\right|
\le
76.2\,
|t|^{4.45(1-\sigma)^{3/2}}
(\log |t|)^{2/3}
```

The qualitative general-growth theorem proves the correct analytic shape, but not these optimized constants.

The optimized contract remains open.

---

## Near-one density

The source contract:

```lean
GafniTao.FordNearOneDensityEstimate
```

has the form:

```math
N(1-\eta,T)
\le
K
T^{58.05\,\eta^{3/2}}
(\log T)^{15}
```

for sufficiently large `T`.

The normalization bridge is already proved:

```lean
GafniTao.nearOneLogDensityBound_of_fordNearOneDensityEstimate
```

and yields:

```math
N(1-\eta,T)
\le
T^{58.05\,\eta^{3/2}}
(\log T)^{16}
```

after increasing the lower height threshold.

The exact `58.05` density source theorem remains open.

---

## Asymptotic zero-free region

The source contract:

```lean
GafniTao.FordAsymptoticZeroFree
```

remains open.

The qualitative growth and local zero-count developments now make this a particularly natural next target because the downstream Gafni-Tao interface only requires some positive Vinogradov-Korobov width, not Ford's fully optimized numerical width.

The existing consumer chain is:

```text
pointwise zero-free theorem
        |
        v
rectangle-uniform zero-free theorem
        |
        v
VinogradovKorobovCountVanishing
        |
        v
Gafni-Tao right-edge branch
```

---

# Integration frontier

The distinction between a theorem proved in a development file and a theorem integrated into the release dependency path is intentional.

A source theorem counts as integrated only when:

1. its module is imported by `Extension/GafniTao.lean`;
2. the isolated package builds through that root;
3. source-sensitive endpoints are represented appropriately in `Audit.lean`;
4. the actual axiom output is inspected;
5. the result feeds the intended dependency path.

At the current snapshot:

```text
Ford Lemma 3.2 chain
Ford Lemma 3.3
Ford count monotonicity
Ford Lemma 6.3 moment-integral entry
```

are root-integrated.

The qualitative exponential-sum, qualitative zeta-growth, and qualitative local-zero-count theorems exist in the repository but remain outside the package root.

That is the next integration boundary.

---

# Central audit

The isolated dependency audit is:

```text
Extension/GafniTao/Audit.lean
```

It imports:

```lean
import GafniTao
```

and explicitly runs `#print axioms` on public and source-sensitive results.

The central audit now contains more than 600 explicit dependency checks.

It covers major parts of:

- exceptional-set measure theory;
- extended-real exponent machinery;
- multiplicity bridges;
- zero additive energy;
- near-one consumer bridges;
- frozen Guth-Maynard input;
- integrated Ford analytic infrastructure;
- Ford detector and K-formula infrastructure;
- local arithmetic entry;
- second and fourth moments;
- strip assembly;
- equation (2.7);
- limiting assembly;
- global exceptional cover;
- conditional Theorems 1.2 and 1.3;
- the native sharp-Perron chain;
- Ford Lemma 3.3;
- substantial Lemma 3.4 arithmetic;
- effective canonical prime-packet bounds;
- complete-count monotonicity.

Representative newer audit entries include:

```lean
GafniTao.ford_lemma_3_3_finite_source
GafniTao.ford_lemma_3_4_inner_exponent_eq
GafniTao.ford_lemma_3_4_exponent_cancellation
GafniTao.ford_lemma_3_4_final_exponent_eq
GafniTao.ford_lemma_3_4_terminal_constant
GafniTao.ford_lemma_3_4_terminal_power
GafniTao.eventually_fordPrimeSet_le_relative
GafniTao.eventually_fordPrimeSet_le_two_mul
GafniTao.exists_fordPrimeSet_relative_threshold
GafniTao.fordKCount_mono_Q
GafniTao.fordLCount_mono_Q
```

Some root-integrated source families still require additional representative audit entries, including the Lemma 3.2 source assembly and the Lemma 6.3 moment-integral endpoint.

The qualitative workbench results also require audit entries if and when they are promoted into the root.

---

# Theorem 1.1

After the general Gafni-Tao theorem becomes unconditional, derive the ordinary threshold consequences from a uniform density exponent `A0`.

The source thresholds are:

```math
\theta
>
1-\frac{1}{A_{0}}
```

for the all-interval regime, and:

```math
\theta
>
1-\frac{2}{A_{0}}
```

for the almost-all regime.

For the frozen Guth-Maynard value:

```math
A_{0}
=
\frac{30}{13}
```

the elementary threshold arithmetic is already present.

The final theorem must connect the almost-all statement to the actual exceptional-measure framework.

---

# Section 3 numerical consequences

The later published numerical consequences remain open.

The first principal sample target is:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}
```

The second is the quantified sufficiently-small-Delta result from the paper.

Closing these requires additional published analytic inputs, including:

- the relevant Pintz ordinary zero-density segment;
- the relevant Heath-Brown four-zero additive-energy segment;
- endpoint compatibility;
- multiplicity compatibility;
- normalization compatibility;
- exact limiting arithmetic.

A full Figure 4 envelope, if pursued, additionally requires a certified finite optimization over pinned source data.

Floating-point calculations may be used for exploration and checking.

They must not establish the final theorem.

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

A source proposition that restates the desired theorem is not a proof of that theorem.

A theorem in a workbench file is not part of the release dependency path until it is deliberately integrated.

The actual `#print axioms` output must be inspected.

---

# Source and certificate discipline

The Ford development contains several artifact classes:

```text
source reference
proof module
certificate data
certificate generator
temporary probe
development artifact
```

They must not be treated as equivalent.

Generated certificate data is acceptable when Lean independently verifies it.

External scripts may generate candidate certificates.

They are not theorem oracles.

Temporary probes and cache artifacts should not be part of the claimed final dependency path.

---

# Isolation boundary

This project is intentionally isolated from the completed Guth-Maynard foundation.

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

Do not modify the frozen `RiemannZeta/` foundation merely to make the extension easier to prove.

Do not weaken frozen public contracts.

Do not import the experimental Gafni-Tao extension back into:

```text
RiemannZeta.lean
```

The dependency direction is one-way:

```text
Frozen Guth-Maynard foundation
              |
              v
      Gafni-Tao extension
```

not the reverse.

---

# Acceptance standard

A source theorem is not DONE merely because a downstream implication has been formalized.

For a source result to be accepted, establish every applicable item below:

1. The statement matches the pinned source theorem and parameter range.
2. Analytic multiplicities are represented correctly.
3. Endpoint conventions match the source.
4. Constants and logarithmic factors are accounted for.
5. No unauthorized `T^epsilon` loss is inserted into the near-one density estimate.
6. No project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised restatement supplies the intended theorem.
7. The theorem is integrated into the intended root import graph.
8. Source-sensitive endpoints are represented in the central audit.
9. The isolated package builds.
10. The actual axiom output is inspected.
11. Certificate generators are not treated as proof evidence.
12. The Crosswalk, Architecture, Research Agenda, Shitlist, and README agree with the Lean source.
13. Public theorem names do not claim more than their hypotheses justify.

---

# Claim discipline

The strongest safe summary of the current repository is:

> Most of the downstream Gafni-Tao exceptional-interval transfer mechanism has been formalized in Lean. The exact exceptional-set framework, multiplicity-sensitive zero counts, local arithmetic entry, native sharp truncated explicit formula, second- and fourth-moment machinery, equation (2.7), limiting assembly, local-to-global covering argument, frozen Guth-Maynard consumer, and conditional max-forms of Theorems 1.2 and 1.3 are implemented. The Ford source campaign has advanced through a large root-integrated analytic chain, a source-scale Lemma 3.2 chain, a root-integrated Lemma 3.3 theorem, substantial Lemma 3.4 arithmetic, effective canonical prime-packet control, count monotonicity, and the opening of the Lemma 6.3 moment argument. Separately, the development workbench now proves a complete qualitative Ford exponential-sum estimate, a qualitative Richert-Ford zeta-growth theorem, and a qualitative local zero-count theorem. Those qualitative results are not yet root-integrated and do not supply Ford's optimized constants. The complete Gafni-Tao theorem is not yet claimed because the optimized Ford near-one density and asymptotic zero-free outputs remain open, the exact unconditional source theorem interfaces remain open, and the later Section 3 source inputs and numerical conclusions remain unfinished.

Do not shorten this to:

```text
Gafni-Tao is proved in Lean.
```

That statement is not currently justified.

Likewise, do not describe:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
GafniTao.gafniTaoTheorem12_max_conditional
```

as unconditional final source theorems.

---

# Documents

The directory contains the project-control documents used to keep the formalization synchronized with the source.

- [Gafni-Tao Sources.md](Gafni-Tao%20Sources.md)

  Source references, hashes, external inputs, and reusable Lean infrastructure.

- [Gafni-Tao Architecture.md](Gafni-Tao%20Architecture.md)

  Numbered dependency graph and module architecture.

- [Gafni-Tao Research Agenda.md](Gafni-Tao%20Research%20Agenda.md)

  Current execution plan and acceptance order.

- [Gafni-Tao Crosswalk.md](Gafni-Tao%20Crosswalk.md)

  Source-to-Lean theorem mapping.

- [Gafni-Tao Shitlist.md](Gafni-Tao%20Shitlist.md)

  Detailed acceptance checklist.

- [Gafni-Tao Goal Prompt.md](Gafni-Tao%20Goal%20Prompt.md)

  Persistent implementation objective for coding agents.

These documents are project-control artifacts, not proof objects.

When documentation and Lean disagree about implementation status:

```text
root imports
    +
central audit
    +
actual theorem dependencies
```

take precedence.

Then update the documentation.

---

# Near-term execution order

## 1. Integrate the qualitative Ford theorem chain

The development workbench now contains actual qualitative analytic theorems, not merely scaffolding.

The next integration candidate is:

```text
Ford exponential-sum qualitative theorem
                |
                v
qualitative global zeta growth
                |
                v
general local zero-count theorem
```

Bring this chain into the root only when the intended dependency path builds cleanly.

Add representative source-sensitive endpoints to `Audit.lean`.

---

## 2. Attempt qualitative zero-free closure

The qualitative zeta-growth and local-zero-count machinery has the right Vinogradov-Korobov shape.

The next major target should be an unconditional existential zero-free theorem strong enough to discharge:

```lean
GafniTao.FordAsymptoticZeroFree
```

or a theorem immediately implying it.

This source contract does not require the fully optimized Ford constants.

---

## 3. Continue optimized Ford Theorem 2

In parallel, continue the exact source-constant branch toward:

```lean
GafniTao.FordTheorem2
```

with the published constants:

```text
9.463
133.66
```

The qualitative theorem is a proof that the method closes.

It is not a proof of the optimized source theorem.

---

## 4. Close optimized `FordZetaGrowthBound`

Use the optimized exponential-sum path and existing detector/growth infrastructure to prove:

```lean
GafniTao.FordZetaGrowthBound
```

with:

```text
76.2
4.45
2/3
```

as required by the pinned source contract.

---

## 5. Prove `FordNearOneDensityEstimate`

The final near-one density target remains:

```lean
FordNearOneDensityEstimate K T0
```

with the exact `58.05` exponent coefficient.

Immediately consume the already-proved normalization theorem once this closes.

---

## 6. Package unconditional near-one inputs

Once the density and zero-free source contracts are genuine theorems, instantiate:

```lean
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

The right-edge branch can then stop accepting these inputs externally.

---

## 7. Remove already-resolved top-level premises

The native sharp truncated explicit formula already exists.

Supply it internally in the final Gafni-Tao wrapper.

Do the same for any cutoff or auxiliary object already constructible from the frozen foundation.

---

## 8. Export exact Theorem 1.3

Prove the exact source epsilon-infimum formulation.

Retain the current max-form as a separate corollary.

---

## 9. Export exact Theorem 1.2 and Theorem 1.1

Derive the ordinary theorem and the all-interval / almost-all threshold consequences.

Consume the existing frozen GM `30/13` bridge.

---

## 10. Complete Section 3

Formalize the exact Pintz and Heath-Brown source segments.

Then prove the paper's displayed sample bounds.

Only after that should the optional full piecewise optimizer become a priority.

---

## 11. Final release audit

Run the isolated package.

Execute the central audit.

Inspect every source-sensitive dependency.

Remove or classify probes and generated artifacts.

Synchronize every project-control document.

Only then make a completion claim.

---

# Repository workflow

`push_to_github.bat` is the owner-operated publication step.

It is separate from proof verification.

A GitHub push means that a selected local snapshot was published.

It does not by itself establish that the isolated package was freshly built or audited.

The public repository may therefore lag local work.

Agents must not push unless separately instructed.

After a substantive mathematical milestone, use a commit message describing the theorem actually closed.

For example, only after the corresponding theorem has genuinely been proved:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford asymptotic zero-free input"
```

or:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford near-one density input"
```

---

# Completion condition

The project should be described as a completed formalization of the intended Gafni-Tao theorem only when the dependency graph has the form:

```text
accepted Lean / Mathlib foundation
             |
             v
frozen Guth-Maynard foundation
             |
             +------------------------------+
             |                              |
             v                              v
native sharp explicit formula      proved Ford/VK source inputs
             |                              |
             +---------------+--------------+
                             |
                             v
                  Section 2 moment machinery
                             |
                             v
                     equation (2.7)
                             |
                             v
                  exceptional-set measure
                             |
                             v
                   exceptional exponent
                             |
                             v
               exact Gafni-Tao Theorem 1.3
                             |
                             v
               Theorems 1.2 and 1.1
                             |
                             v
              published numerical consumers
```

with no unresolved project-level analytic assumptions hidden inside the claimed dependency path.

Until then:

**formalization in progress, with most of the downstream Gafni-Tao transfer mechanism implemented, Ford's source combinatorics now extending well beyond Lemma 3.2, and a complete qualitative Ford exponential-sum-to-zeta-growth chain proved in the development workbench. The immediate task is to integrate that qualitative chain and convert it into an unconditional zero-free input while the optimized numerical Ford branch continues toward the exact near-one density theorem.**