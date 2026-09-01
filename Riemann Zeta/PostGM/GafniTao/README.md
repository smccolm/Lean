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

The main mathematical frontier has moved upstream into the source analytic estimates needed by the near-one argument.

A substantial Ford source-development program is now root-integrated. The root contains not only the previously integrated trigonometric, Euler-product, detector, left-line, Laplace, K-formula, and logarithmic-derivative branches, but also a newer source-faithful Vinogradov/Lemma-5.1/combinatorial chain covering:

- Vinogradov moment and counting identities;
- power interpolation and logarithmic Taylor control;
- the entry into Ford Lemma 5.1;
- first and second Holder steps;
- fiber decompositions;
- equations (5.2), (5.3), and (5.4);
- spacing counts;
- tent weights and tent series;
- resonance counting;
- shift and averaging arguments;
- exponential normalization;
- the real-parameter Ford Lemma 5.1 interface;
- Vandermonde determinants;
- polynomial systems;
- finite differences;
- complete counts;
- prime selection;
- Newton congruence machinery.

This newer chain is **root-integrated**, but its principal new endpoints have not yet been synchronized into the central `Audit.lean`.

A still newer Ford workbench also exists in the repository and remains outside the package root. It includes shifted zero-detector machinery, local zero-disk detector estimates, Ford Theorem 2 / exponential-sum analysis, cubic sum-to-integral estimates, and exact numerical certificate machinery.

The principal source contracts remain open:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordAsymptoticZeroFree
```

The unintegrated exponential-sum development also defines:

```lean
GafniTao.FordTheorem2
```

as a source contract.

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
Ford / Vinogradov-Korobov source mathematics
                    |
                    v
          near-one source outputs
                    |
                    v
      already-built right-edge branch
                    |
                    v
       already-built GT transfer chain
                    |
                    v
      unconditional source theorem
```

---

# Ford development frontiers

There are now three distinct Ford frontiers.

They must not be conflated.

---

## 1. Root-integrated and centrally audited Ford chain

The package root imports a substantial Ford analytic chain whose established source-sensitive endpoints are already represented in the central audit.

This includes:

```text
FordTrigonometric
FordFourierKernel
FordEulerProduct
FordLemma51
FordZetaBasic

FordZeroDetectorKernel
FordZeroDetectorResidues
FordCotangentPositivity
FordCotangentCorrection
FordZeroDetectorCenter
FordZeroDetectorZetaResidues
FordZeroDetectorDifferentiability
FordZeroDetectorRectangle
FordZeroDetectorFinite
FordZeroDetectorFiniteEdges
FordZeroDetectorHorizontalDecay
FordLogNormDerivative
FordZeroDetectorVerticalParts
FordZeroDetectorVerticalLog
FordZeroDetectorPhysicalEdges

FordLeftLine
FordLeftLineIntegral

FordKFiniteResidues
FordKFiniteRectangle
FordLaplaceInversion
FordLaplaceSource
FordKFiniteEdges
FordKHorizontal
FordKRightLine
FordKSourceSeries
FordKZeroSeries
FordKInfiniteRectangle
FordKLeftBound
FordKFormula

FordZeroDetectorEdges
FordZetaConvex
FordZetaBasicExplicit
FordLogDerivative
```

Representative audited endpoints include:

```lean
GafniTao.ford_lemma_5_1

GafniTao.ford_zeta_basic_upper
GafniTao.ford_zeta_basic_reciprocal_lower
GafniTao.ford_zeta_basic_logDerivative

GafniTao.fordZetaDetector_rectangleIntegral_eq_residue_sum
GafniTao.fordZetaDetector_rectangleIntegral_eq_explicit_sum

GafniTao.fordK_infinite_rectangle_native
GafniTao.fordK_formula_native
GafniTao.fordK_formula_with_log_error_native
```

This is integrated proof infrastructure.

It does not yet discharge the final Ford source contracts.

---

## 2. Newly root-integrated Ford source chain, central-audit sync pending

The package root now also imports:

```text
FordVinogradovIntegral
FordPowerInterpolation
FordLogTaylor
FordTaylorPhase
FordLemma51Entry
FordFiniteHolder
FordLemma51Holder
FordSecondHolder
FordLemma51Fibers
FordLemma51Equation53
FordIntegerInterval
FordSpacingCount
FordTentWeights
FordTentSeries
FordEquation54Setup
FordEquation54Expansion
FordEquation54Fourier
FordEquation54Interchange
FordEquation54Bound
FordEquation54Resonance
FordEquation54Counting
FordEquation54Window
FordLemma51Spacing
FordLemma51W
FordLemma51Shift
FordLemma51Average
FordEquation52
FordLemma51Exponential
FordLemma51Normalize
FordLemma51Real
FordVandermondeDeterminant
FordPolynomialSystem
FordFiniteDifference
FordIntegerPolynomialSystem
FordCompleteCounts
FordPrimeSelection
FordNewtonCongruence
```

This is no longer merely a collection of experimental files.

It is part of the package root.

The newly integrated chain contains source-oriented mathematics including:

- Ford's Vinogradov moment/counting setup;
- torus Fourier orthogonality;
- the source-equation route into Lemma 5.1;
- Holder and fiber decompositions;
- spacing and resonance estimates;
- equations (5.2), (5.3), and (5.4);
- real-valued source normalization;
- polynomial and congruence infrastructure.

Representative results include the Vinogradov torus mean identity:

```lean
GafniTao.ford_vinogradov_torus_mean_eq
GafniTao.ford_vinogradov_torus_real_mean_eq
```

the real-parameter Lemma 5.1 bridge:

```lean
GafniTao.fordLemma51SourceCore_eq_separated
GafniTao.fordLemma51_centralTerm_le_sourceCore
```

and the Newton-congruence conclusion:

```lean
GafniTao.ford_multiset_eq_of_powerSums_eq
```

These newer root-integrated theorem families are not yet represented in the central `Audit.lean`.

That audit synchronization is now an explicit project task.

---

## 3. Development workbench still outside the package root

A further Ford development layer exists under:

```text
Extension/GafniTao/
```

but remains outside `GafniTao.lean`.

It includes substantial work on:

- shifted zero-detector rectangles;
- asymmetric detector edges;
- selected shifts and heights;
- shifted detector limits;
- explicit pole corrections;
- local zero disks;
- local cotangent lower bounds;
- local detector assembly;
- local detector growth bounds;
- Ford's shifted exponential sum;
- dyadic decomposition;
- the literal cubic exponent;
- cubic scaling and unimodality;
- normalized integrals;
- exact polynomial certificates;
- exact Bernstein certificates.

Representative files include:

```text
FordShiftedZeroDetectorRectangle.lean
FordShiftedZeroDetectorAsymmetricRectangle.lean
FordShiftedZeroDetectorAsymmetricEdges.lean
FordShiftedZeroDetectorFinite.lean
FordShiftedZeroDetectorHorizontalBound.lean
FordShiftedZeroDetectorVerticalEdges.lean
FordShiftedZeroDetectorAssembly.lean
FordShiftedZeroDetectorInequality.lean
FordShiftedZeroDetectorLimit.lean

FordLocalDiskZeros.lean
FordLocalCotangentLower.lean
FordLocalCotangentUniform.lean
FordLocalCotangentSelected.lean
FordLocalDetectorAssembly.lean
FordLocalDetectorGrowthBound.lean

FordExponentialSum.lean
FordExponentialSumAbel.lean
FordDyadicDecomposition.lean
FordDyadicExponent.lean
FordCubicExponent.lean
FordCubicScaling.lean
FordCubicIntegral.lean
FordNormalizedIntegral.lean
FordNumericalIntegralUpper.lean

FordPolynomialCertificate.lean
FordBernsteinCertificate.lean
FordBernsteinDirect.lean
```

This development is mathematically significant.

It does not count as integrated proof infrastructure until deliberately imported through the root and included in the source-sensitive audit where appropriate.

---

# Current status by proof layer

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
| Ford trigonometric source infrastructure | Root-integrated and audited |
| Ford Fourier-kernel infrastructure | Root-integrated and audited |
| Ford Euler-product infrastructure | Root-integrated and audited |
| Ford source Lemma 5.1 | Root-integrated and audited |
| Ford detector kernel/residue chain | Root-integrated and audited |
| Ford finite detector rectangles and edges | Root-integrated and audited |
| Ford left-line / Laplace chain | Root-integrated and audited |
| Ford K-formula | Root-integrated and audited |
| Basic explicit Ford zeta bounds | Root-integrated and audited |
| Ford logarithmic-derivative infrastructure | Root-integrated and audited |
| Vinogradov moment/counting chain | Root-integrated, central-audit sync pending |
| Source-equation Lemma 5.1 derivation | Root-integrated, central-audit sync pending |
| Spacing / tent / resonance chain | Root-integrated, central-audit sync pending |
| Vandermonde / polynomial-system chain | Root-integrated, central-audit sync pending |
| Complete counts / prime selection / Newton congruence | Root-integrated, central-audit sync pending |
| Shifted detector workbench | Present, not root-integrated |
| Local zero-disk detector workbench | Present, not root-integrated |
| Ford Theorem 2 workbench | Present, not root-integrated |
| Exact numerical certificate workbench | Present, not root-integrated |
| `FordZetaGrowthBound` | Source contract still open |
| `FordNearOneDensityEstimate` | Source contract still open |
| `FordAsymptoticZeroFree` | Source contract still open |
| `FordTheorem2` | Source contract still open |
| Exact unconditional Theorem 1.3 | Open |
| Exact unconditional Theorem 1.2 | Open |
| Theorem 1.1 | Open |
| Pintz / Heath-Brown Section 3 inputs | Open |
| Published sample bounds | Open |
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

The project defines the fixed-threshold exceptional exponent:

```math
\mu_{\delta}(\theta)
```

and the global exceptional exponent:

```math
\mu(\theta)
```

The implementation includes:

- measurability;
- finite-measure facts;
- threshold monotonicity;
- fixed-power bounds;
- epsilon-exponent bounds;
- extended-real exponent machinery;
- eventual-empty behavior;
- countable positive-threshold reduction.

---

## 2. Zero counting and multiplicity

The project contains native infrastructure for the nontrivial zeros of the Riemann zeta function and the multiplicity-weighted zero counts required by the paper.

This includes:

```math
N(\sigma,T)
```

and:

```math
N^{\ast}(\sigma,T)
```

The four-zero quantity uses ordered zero occurrences with analytic multiplicity.

It is not replaced by an unweighted additive energy of distinct ordinates.

The associated exponent interfaces `A` and `A*` feed the ordinary and refined moment arguments.

---

## 3. Local arithmetic entry

The local arithmetic chain includes:

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

The supporting sharp-Perron chain includes:

- finite Mangoldt Perron identities;
- logarithmic-derivative expansions;
- Perron kernels;
- contour rectangles;
- residue calculations;
- analytic multiplicity in the zero shell;
- right-edge estimates;
- horizontal-edge estimates;
- left-edge estimates;
- functional-equation input;
- selected good heights;
- low-height treatment;
- arbitrary real endpoints;
- endpoint-uniform cutoff estimates.

The physical parameter range includes:

```math
2 \le T \le x
```

The central audit includes:

```lean
GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The sharp explicit formula is no longer a principal unresolved analytic source input.

A remaining interface task is to stop exposing it as a premise in public wrappers when the native theorem can be supplied internally.

---

## 5. Second and fourth moments

The second- and fourth-moment branches are implemented at the multiplicity-sensitive level required by the source argument.

The second moment consumes the actual zero count.

The fourth moment consumes the actual multiplicity-weighted four-zero energy.

The refined route therefore genuinely retains the `A*` contribution.

---

## 6. Finite half-open strips

The finite-strip layer includes:

- half-open strip indexing;
- upper-boundary treatment;
- reconstruction of the full zero sum;
- exclusion of zeros on `Re rho = 1`;
- strip-wise second-moment estimates;
- strip-wise fourth-moment estimates;
- right-edge strip handling.

This machinery feeds the equation (2.7) argument.

---

## 7. Equation (2.7)

The equation (2.7) branch is implemented downstream.

The strip alternatives are:

```text
small-density strip
        |
        v
eventually empty event
```

```text
right-edge strip
        |
        v
near-one density + zero-free input
```

```text
ordinary strip
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

These strip estimates are assembled into a measure bound for the full zero-large-value event.

Representative results include:

```lean
GafniTao.equation27StripMeasure_epsilonBound_of_second_or_fourth
GafniTao.equation27StripMeasure_epsilonBound_of_exponent_upper_bounds
GafniTao.eventually_equation27StripLargeSet_eq_empty_of_rightEdge
GafniTao.equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
```

---

## 8. Limit assembly

The project contains the limiting machinery needed to move from finite strips and epsilon-dependent estimates to fixed-power exceptional-measure bounds.

Representative theorems include:

```lean
GafniTao.exists_refined_limit_witness
GafniTao.equation27FullZeroMeasure_fixedPowerBound_of_refined_lt
GafniTao.localExceptionalMeasure_fixedPowerBound_of_source_inputs
```

The strip resolution and epsilon margins are selected relative to the candidate exponent.

The result is a fixed-power local exceptional-measure bound.

---

## 9. Local-to-global exceptional cover

The local result is promoted through the finite multiplicative cover to the original exceptional set.

The central audit contains:

```lean
GafniTao.shortIntervalExceptionalSet_subset_local_union
GafniTao.localShortIntervalExceptionalSet_subset_sourceInterval
GafniTao.exceptionalMeasure_le_sum_local
GafniTao.exceptionalMeasure_fixedPowerBound_of_local
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The downstream proof therefore reaches the actual exceptional exponent.

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

where the refined term retains both the ordinary density exponent and the four-zero energy exponent.

This is a genuine Lean theorem on the central audit surface.

It remains conditional on named analytic inputs.

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

The exact unconditional source statement remains open.

---

# Exact theorem-statement closure

The current max-form results are not automatically identical to the principal statements in the source paper.

The refined source target retains the epsilon infimum:

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

The later Section 3 numerical results require additional source inputs.

---

# Ford source contracts

## Ford zeta-growth theorem

The source contract is:

```lean
GafniTao.FordZetaGrowthBound
```

It records:

```math
\left|
\zeta(\sigma+it)
\right|
\le
76.2\,
|t|^{4.45(1-\sigma)^{3/2}}
(\log |t|)^{2/3}
```

in the source range.

This remains a proposition to be discharged by the native Ford source chain or by an explicitly accepted pinned theorem.

---

## Ford near-one density theorem

The source contract is:

```lean
GafniTao.FordNearOneDensityEstimate
```

with the form:

```math
N(1-\eta,T)
\le
K\,
T^{58.05\,\eta^{3/2}}
(\log T)^{15}
```

for sufficiently large `T`.

The normalization bridge is already proved:

```lean
GafniTao.nearOneLogDensityBound_of_fordNearOneDensityEstimate
```

It yields:

```math
N(1-\eta,T)
\le
T^{58.05\,\eta^{3/2}}
(\log T)^{16}
```

after enlarging the lower height threshold.

No `T^{\varepsilon}` loss is used in this conversion.

The missing work is the source density theorem itself.

---

## Ford asymptotic zero-free theorem

The source contract is:

```lean
GafniTao.FordAsymptoticZeroFree
```

It supplies a positive Vinogradov-Korobov width above a sufficiently large height.

The consumer bridge is already implemented:

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

The source theorem feeding the first node remains open.

---

## Near-one packaging bridge

Once the density and zero-free source outputs are proved, the project already has:

```lean
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

which packages them into:

```text
VinogradovKorobovCountVanishing
```

and:

```text
NearOneLogDensityBound 58.05 16
```

for direct use by the right-edge machinery.

The downstream normalization and packaging problem is already solved.

---

# Root-integrated Vinogradov and Lemma 5.1 source chain

The newer root-integrated source chain represents a significant architectural advance.

## Vinogradov moment identity

`FordVinogradovIntegral.lean` formalizes the finite counting and Fourier-orthogonality side of Ford's Vinogradov-system input.

Representative endpoints include:

```lean
GafniTao.ford_vinogradov_torus_mean_eq
GafniTao.ford_vinogradov_torus_real_mean_eq
```

These identify the appropriate torus mean of the Weyl sum with the finite Vinogradov moment count.

---

## Source-faithful Lemma 5.1 route

The imported chain now contains dedicated modules for:

```text
entry
first Holder step
second Holder step
fiber decomposition
equation (5.3)
integer intervals
spacing
tent weights
tent series
equation (5.4)
resonance
counting
window estimates
shift
averaging
equation (5.2)
exponential form
normalization
real-parameter endpoint
```

The real-valued endpoint layer includes source-scale statements such as:

```lean
GafniTao.fordLemma51SourceCore_eq_separated
GafniTao.fordLemma51_centralTerm_le_sourceCore
```

This matters because the paper's parameters are real-valued, while several internal combinatorial cutoffs are natural numbers.

The bridge handles that distinction explicitly rather than treating the natural-number version as the final source statement.

---

## Polynomial and congruence branch

The root also imports:

```text
FordVandermondeDeterminant
FordPolynomialSystem
FordFiniteDifference
FordIntegerPolynomialSystem
FordCompleteCounts
FordPrimeSelection
FordNewtonCongruence
```

This develops the algebraic/combinatorial machinery needed for the source argument.

A representative Newton-congruence endpoint is:

```lean
GafniTao.ford_multiset_eq_of_powerSums_eq
```

which proves that equality of the first `d` power sums modulo a prime `p > d` forces equality of the corresponding residue multisets.

---

# Central audit synchronization

The root import has moved ahead of the central audit.

The new Vinogradov/Lemma-5.1/combinatorial theorem families are imported by:

```text
Extension/GafniTao.lean
```

but are not yet represented by corresponding `#print axioms` entries in:

```text
Extension/GafniTao/Audit.lean
```

This is now an explicit synchronization task.

The immediate audit candidates include representative endpoints from:

```text
FordVinogradovIntegral
FordLemma51Equation53
FordEquation54Bound
FordLemma51Average
FordEquation52
FordLemma51Real
FordVandermondeDeterminant
FordCompleteCounts
FordPrimeSelection
FordNewtonCongruence
```

The audit should not mechanically print every helper theorem.

It should include enough source-sensitive endpoints to make the trusted dependency path visible.

---

# Shifted detector development

The still-unintegrated Ford workbench goes further toward the local zero-density argument.

It contains shifted detector machinery in which:

- detector zeros retain analytic multiplicity;
- the zeta pole contribution remains explicit;
- right- and left-edge terms remain visible;
- horizontal remainders are controlled;
- selected heights remove public boundary nonvanishing assumptions.

The local detector layer specializes this machinery to Ford's local zero disk.

Representative development endpoints include:

```lean
GafniTao.exists_fordShiftedDetector_selected_subset_inequality
GafniTao.eventually_exists_fordLocalDisk_detector_inequality
GafniTao.eventually_exists_fordLocalDisk_detector_growthBound
```

The local growth-bound theorem still consumes:

```lean
hFord : FordZetaGrowthBound
```

so it does not yet discharge Ford Theorem 1.

These files remain outside the package root at the current public snapshot.

---

# Ford Theorem 2 development

The unintegrated exponential-sum branch defines the shifted logarithmic exponential sum used in Ford's source argument.

The source contract is:

```lean
GafniTao.FordTheorem2
```

defined as:

```lean
FordExponentialSumEstimate 9.463 133.66
```

The surrounding development includes:

- finite-sum bounds;
- Abel-style transformations;
- dyadic decomposition;
- exponent normalization;
- the literal cubic exponent;
- turning-point analysis;
- unimodality;
- cubic scaling;
- normalized integrals;
- exact numerical bounds;
- polynomial and Bernstein certificate machinery.

`FordTheorem2` is still a proposition.

The project must not move an unresolved source assumption from Ford Theorem 1 to Ford Theorem 2 and then describe the source layer as closed.

---

# Exact numerical certification

The newer Ford workbench includes an exact-certification branch.

The trust model should remain:

```text
external generator
      |
      v
candidate certificate data
      |
      v
Lean exact arithmetic
      |
      v
proved inequality
```

External scripts may generate candidate rational data.

They are not proof oracles.

The final Lean theorem checking the certificate is the proof evidence.

---

# Integration criteria

A file does not count as integrated proof infrastructure merely because it exists under `Extension/GafniTao/`.

For a source module to count as integrated:

1. it is imported through the intended package root;
2. the isolated package builds with it;
3. public or source-sensitive endpoints are considered for the central audit;
4. the actual axiom output is inspected;
5. the theorem feeds the intended dependency chain or is clearly identified as reusable infrastructure.

The current root-integrated Vinogradov/Lemma-5.1 chain satisfies step 1.

Central-audit synchronization remains to be done for its new source-sensitive endpoints.

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

The second is the quantified sufficiently-small-Delta result from the source paper.

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

# Audit surface

The isolated dependency audit is:

```text
Extension/GafniTao/Audit.lean
```

It imports:

```lean
import GafniTao
```

and explicitly runs `#print axioms` on public and source-sensitive results.

The current central audit covers major parts of:

- exceptional-set measure theory;
- extended-real exponent machinery;
- multiplicity bridges;
- zero additive energy;
- Vinogradov-Korobov consumer bridges;
- near-one normalization;
- frozen Guth-Maynard input;
- Ford trigonometric infrastructure;
- Ford Fourier analysis;
- Euler-product and prime-power expansions;
- Ford Lemma 5.1;
- Ford zero-detector infrastructure;
- Ford left-line analysis;
- Ford K-formula infrastructure;
- explicit zeta and logarithmic-derivative estimates;
- local arithmetic entry;
- second and fourth moments;
- strip assembly;
- equation (2.7);
- limit assembly;
- global exceptional cover;
- conditional Theorems 1.2 and 1.3;
- the native sharp-Perron chain;
- the native sharp truncated explicit formula.

Representative final entries include:

```lean
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
GafniTao.exceptionalExponentDelta_le_refined_max_of_source_inputs
GafniTao.gafniTaoTheorem13_max_conditional
GafniTao.gafniTaoTheorem12_max_conditional

GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native

GafniTao.fordK_infinite_rectangle_native
GafniTao.fordK_formula_native
GafniTao.fordK_formula_with_log_error_native
```

The newly root-integrated Vinogradov/Lemma-5.1/combinatorial chain now needs to be added to this audit at suitable endpoints.

A declaration appearing in `Audit.lean` means it is on the explicit dependency-audit surface.

It does not by itself establish that a fresh release audit has been executed and inspected successfully.

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

A source proposition that merely restates a desired theorem is not a proof of that theorem.

A theorem being present in an unimported file is not evidence that it belongs to the final dependency path.

The actual `#print axioms` output must be inspected.

---

# Source and workbench hygiene

The Ford development contains multiple kinds of artifacts:

```text
source reference
proof module
certificate data
certificate generator
temporary probe
development artifact
```

They should not be treated as equivalent.

Generated certificate data is acceptable when Lean independently verifies the certificate.

External scripts are not theorem oracles.

Temporary probes and cache artifacts should not be part of the claimed final proof dependency.

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

> Most of the downstream Gafni-Tao exceptional-interval transfer mechanism has been formalized in Lean. The exact exceptional-set framework, multiplicity-sensitive zero counts, local arithmetic entry, native sharp truncated explicit formula, second- and fourth-moment machinery, equation (2.7), limiting assembly, local-to-global covering argument, frozen Guth-Maynard consumer, and conditional max-forms of Theorems 1.2 and 1.3 are implemented. A substantial Ford analytic source chain is root-integrated and centrally audited through detector, left-line, K-formula, explicit-zeta, and logarithmic-derivative infrastructure. A newer Vinogradov/Lemma-5.1/combinatorial source chain is now also root-integrated, although its new source-sensitive endpoints still require central-audit synchronization. A further shifted-detector, local-zero-disk, Ford-Theorem-2, cubic-integral, and exact-certificate workbench remains outside the root. The complete Gafni-Tao theorem is not yet claimed because the Ford near-one density and asymptotic zero-free outputs remain source contracts, Ford Theorem 2 remains a source contract where used, the exact unconditional source theorem interfaces remain open, and the later Section 3 inputs and numerical conclusions remain unfinished.

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

Then repair the documentation.

---

# Near-term execution order

## 1. Synchronize the central audit with the new root imports

The Vinogradov/Lemma-5.1/combinatorial chain is already root-integrated.

Add representative source-sensitive endpoints from the new chain to `Audit.lean`.

Do not wait until final release to make this dependency visible.

---

## 2. Continue the source-faithful Ford chain

Use the now-integrated:

```text
Vinogradov moments
Lemma 5.1 source derivation
spacing and averaging
polynomial systems
complete counts
prime selection
Newton congruence
```

as upstream infrastructure for the remaining Ford source theorems.

Avoid adding downstream Gafni-Tao wrappers unless they close an actual interface gap.

---

## 3. Integrate the mature shifted-detector chain

The next development branch closest to the density theorem is:

```text
shifted detector
      |
      v
selected finite-subset inequality
      |
      v
local zero-disk detector inequality
      |
      v
local detector growth bound
```

Bring this chain into the root only when the intended imported path builds cleanly.

Add its source-sensitive endpoints to the central audit.

---

## 4. Close `FordZetaGrowthBound`

The local growth-bound branch still depends on:

```lean
FordZetaGrowthBound
```

The source program must turn that contract into an actual theorem or an explicitly accepted pinned input.

---

## 5. Close `FordTheorem2`

If the exponential-sum theorem is required by the final density proof, discharge:

```lean
GafniTao.FordTheorem2
```

through the native exponential-sum/cubic/certificate development or explicitly classify it as a trusted pinned external theorem.

Do not leave it as an invisible assumption.

---

## 6. Prove `FordNearOneDensityEstimate`

The detector, Vinogradov, Lemma-5.1, congruence, and exponential-sum branches should eventually meet at:

```lean
FordNearOneDensityEstimate K T0
```

for explicit witnesses `K` and `T0`.

Immediately consume the existing normalization theorem after closure.

---

## 7. Prove `FordAsymptoticZeroFree`

Close the source zero-free theorem and consume the already-built route to:

```lean
VinogradovKorobovCountVanishing
```

---

## 8. Package unconditional near-one inputs

Once the density and zero-free contracts are genuine theorems, instantiate:

```lean
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

The right-edge branch can then stop accepting these inputs externally.

---

## 9. Remove already-resolved top-level premises

The native sharp truncated explicit formula already exists.

Supply it internally in the final Gafni-Tao wrapper.

Do the same for any cutoff or auxiliary object already constructible from the frozen foundation.

---

## 10. Export exact Theorem 1.3

Prove the exact source epsilon-infimum formulation.

Retain the current max-form as a separate corollary.

---

## 11. Export exact Theorem 1.2 and Theorem 1.1

Derive the ordinary theorem and the all-interval / almost-all threshold consequences.

Consume the existing frozen GM `30/13` bridge.

---

## 12. Complete Section 3

Formalize the exact Pintz and Heath-Brown source segments.

Then prove the paper's displayed sample bounds.

Only after that should the optional full piecewise optimizer become a priority.

---

## 13. Final release audit

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
push_to_github.bat "PostGM Gafni-Tao: close Ford near-one density input"
```

or:

```bat
push_to_github.bat "PostGM Gafni-Tao: close Ford asymptotic zero-free input"
```

Do not use completion-language commit messages before the corresponding source contract is actually discharged.

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

**formalization in progress, with most of the downstream Gafni-Tao transfer mechanism implemented, a large Ford analytic source chain centrally audited, a newer Vinogradov/Lemma-5.1/combinatorial chain now root-integrated, and the active mathematical work concentrated on turning the remaining Ford detector and exponential-sum developments into audited source theorems.**