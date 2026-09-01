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

The main mathematical frontier has moved upstream.

A substantial Ford source-development program now exists. Part of that program is integrated into the package root and central dependency audit. A newer and much larger Ford workbench also exists in the repository but has not yet been imported into the root proof graph or central `Audit.lean`.

The principal acceptance barrier remains unchanged:

```lean
GafniTao.FordZetaGrowthBound
GafniTao.FordNearOneDensityEstimate
GafniTao.FordAsymptoticZeroFree
```

are still source contracts rather than unconditional native outputs.

The newer Ford exponential-sum development also introduces:

```lean
GafniTao.FordTheorem2
```

as a source contract for Ford's Theorem 2.

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

The remaining analytic dependency has the form:

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

# Two Ford frontiers

It is important to distinguish two different notions of progress.

## Integrated Ford frontier

The package root:

```text
Extension/GafniTao.lean
```

currently imports the native Ford chain through:

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

These modules are part of the intended integrated dependency graph.

The central `Audit.lean` contains source-sensitive theorems from this chain.

---

## Development Ford frontier

A newer Ford source-development batch also exists below:

```text
Extension/GafniTao/
```

including substantial work on:

- shifted zero-detector rectangles;
- asymmetric detector edges;
- selected good shifts and heights;
- shifted detector limits;
- pole corrections;
- local zero disks;
- local cotangent lower bounds;
- local detector assembly;
- local detector growth bounds;
- Ford's shifted exponential sum;
- dyadic decomposition;
- the literal cubic exponent;
- cubic unimodality;
- normalized integrals;
- explicit numerical integration;
- exact polynomial certificates;
- exact Bernstein certificates;
- source-derived numerical data.

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

This is substantial mathematical development.

It must **not yet be described as integrated proof infrastructure** merely because the files exist.

At the current public snapshot, these newer modules are not imported by the package root and their principal results are not listed in the central `Audit.lean`.

Integration is a separate milestone.

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
| Ford trigonometric source infrastructure | Integrated |
| Ford Fourier-kernel infrastructure | Integrated |
| Ford Euler-product infrastructure | Integrated |
| Ford Lemma 5.1 | Integrated |
| Ford zero-detector kernel/residue chain | Integrated |
| Ford finite detector rectangles and edges | Integrated |
| Ford left-line / Laplace chain | Integrated |
| Ford K-formula | Integrated |
| Basic explicit Ford zeta bounds | Integrated |
| Ford logarithmic-derivative infrastructure | Integrated |
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

The exceptional-set layer is part of the actual downstream proof chain.

---

## 2. Zero counting and multiplicity

The project contains native infrastructure for the nontrivial zeros of the Riemann zeta function and the multiplicity-weighted zero counts required by the paper.

This includes:

```math
N(\sigma,T)
```

and the four-zero additive-energy quantity:

```math
N^{\ast}(\sigma,T)
```

The four-zero object uses ordered zero occurrences with analytic multiplicity.

It is not replaced by an unweighted energy of distinct ordinates.

The associated exponent interfaces `A` and `A*` feed the ordinary and refined moment arguments.

---

## 3. Local arithmetic entry

The local entry into the argument contains:

- the Mangoldt interval identity;
- decomposition of prime and prime-power terms;
- control of prime-power errors;
- local Brun-Titchmarsh estimates;
- replacement of the variable short interval by the local `x/tau` scale;
- finite multiplicative covering of `[X,2X]`;
- local discrepancy and zero-sum interfaces.

This connects the original exceptional event to the local analytic argument.

---

## 4. Native sharp truncated explicit formula

The explicit-formula branch now has a native endpoint:

```lean
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The supporting sharp-Perron chain includes:

- finite Mangoldt Perron identities;
- logarithmic-derivative expansions;
- Perron kernels;
- contour rectangles;
- residue calculations;
- zero shells with analytic multiplicity;
- right-edge estimates;
- horizontal-edge estimates;
- left-edge estimates;
- functional-equation input;
- selected good heights;
- low-height treatment;
- arbitrary real endpoints;
- endpoint-uniform cutoff estimates.

The physical range includes:

```math
2 \le T \le x
```

The native audit surface also includes:

```lean
GafniTao.sharpPsiTruncationBound_native
GafniTao.sharpTruncatedExplicitFormulaBound_native
```

The sharp explicit formula is no longer one of the primary unresolved source inputs.

A remaining interface task is to stop exposing it as a premise in public wrappers when the native theorem can be supplied internally.

---

## 5. Second and fourth moments

The second- and fourth-moment branches are implemented at the multiplicity-sensitive level required by the source argument.

The second moment consumes the actual zero count.

The fourth moment consumes the actual multiplicity-weighted four-zero energy.

The refined route therefore genuinely retains the `A*` contribution.

The current proof surface includes physical moment estimates and the epsilon-exponent forms needed by the strip argument.

---

## 6. Finite half-open strips

The finite-strip layer includes:

- half-open strip indexing;
- treatment of upper strip boundaries;
- reconstruction of the full zero sum;
- exclusion of zeros on the line `Re rho = 1`;
- strip-wise second-moment bounds;
- strip-wise fourth-moment bounds;
- right-edge strip handling.

This machinery feeds equation (2.7).

---

## 7. Equation (2.7)

The equation (2.7) branch is implemented downstream.

The proof separates the strips into the required cases:

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

Equation (2.7) is no longer merely architectural planning.

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

The central audit includes:

```lean
GafniTao.shortIntervalExceptionalSet_subset_local_union
GafniTao.localShortIntervalExceptionalSet_subset_sourceInterval
GafniTao.exceptionalMeasure_le_sum_local
GafniTao.exceptionalMeasure_fixedPowerBound_of_local
GafniTao.exceptionalMeasure_fixedPowerBound_of_source_inputs
```

The downstream proof therefore reaches the actual exceptional exponent rather than stopping at a local proxy.

---

# Conditional Gafni-Tao endpoints

## Refined max-form

The current assembled refined endpoint is:

```lean
GafniTao.gafniTaoTheorem13_max_conditional
```

It gives a bound schematically of the form:

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

It is still conditional.

The current interface includes named analytic inputs that remain to be discharged or supplied internally.

The theorem must therefore not be described as the completed unconditional source Theorem 1.3.

---

## Ordinary max-form

The current ordinary endpoint is:

```lean
GafniTao.gafniTaoTheorem12_max_conditional
```

It is obtained by discarding the fourth-moment improvement.

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

The source-level ordinary epsilon-infimum machinery is also represented internally.

The current public max-form remains conditional.

---

# Exact theorem-statement closure

The current max-form results are not automatically the exact principal statements from the paper.

The refined source target contains the mandatory epsilon infimum.

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

The epsilon infimum must remain unless its removal is independently justified.

The final project should therefore expose:

```text
exact source Theorem 1.3
```

and separately retain:

```text
max-form corollary
```

rather than conflating the two.

The same distinction applies to Theorem 1.2.

---

# Frozen Guth-Maynard consumer

The frozen Guth-Maynard density theorem is already connected to the Gafni-Tao exponent language.

The audit surface includes:

```lean
GafniTao.guthMaynard_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_guthMaynard
GafniTao.frozen_uniform_thirty_thirteenths_zeroDensityEnvelope
GafniTao.zeroDensityExponent_le_thirty_thirteenths
GafniTao.seventeen_thirtieths_eq_uniform_all_threshold
GafniTao.two_fifteenths_eq_uniform_almost_all_threshold
```

Thus the ordinary density constant:

```math
A_{0}
=
\frac{30}{13}
```

and the associated elementary threshold arithmetic already exist in Lean.

The later Section 3 numerical results require additional source inputs.

---

# Integrated Ford source program

## Ford trigonometric positivity

The integrated chain contains exact source-oriented trigonometric identities and positivity estimates.

Representative audited results include:

```lean
GafniTao.ford_cos_four_mul
GafniTao.ford_trigonometric_identity
GafniTao.ford_trigonometric_nonneg
GafniTao.fordTrigSum_eq_constant_add_oscillatory
GafniTao.ford_trigonometric_oscillatory_lower
GafniTao.ford_weighted_trigonometric_lower
GafniTao.fordTrigB0_eq_sum_squares
GafniTao.fordTrigB0_one_le
GafniTao.fordTrigB0_pos
```

---

## Ford Fourier kernel

The integrated source chain contains the Fourier-kernel identities and integrability results used in Ford's analytic estimates.

Representative results include:

```lean
GafniTao.fordFourierKernel_zero
GafniTao.fordFourierKernel_of_ne
GafniTao.fordFourierKernel_nonneg
GafniTao.fordFourierKernel_pos
GafniTao.fordFourierKernel_le_two
GafniTao.ford_beta_kernel_value
GafniTao.ford_sechFourierIntegral_eq_kernel
GafniTao.integrable_fordSechFourierIntegrand
GafniTao.integral_one_div_cosh_sq
```

---

## Euler product and prime-power expansions

The integrated Ford branch contains native Euler-product and prime-power identities for the zeta function in the required source region.

Representative results include:

```lean
GafniTao.summable_fordEulerZetaLog
GafniTao.exp_fordEulerZetaLog_eq
GafniTao.log_norm_riemannZeta_eq_re_fordEulerZetaLog
GafniTao.re_fordEulerZetaLog_eq_tsum
GafniTao.ford_prime_log_hasSum
GafniTao.re_ford_prime_log_eq_tsum
GafniTao.log_norm_riemannZeta_eq_prime_power_series
```

---

## Ford Lemma 5.1

The integrated source branch contains:

```lean
GafniTao.ford_lemma_5_1
```

with the intended source coefficients and analytic weight.

This is a real source lemma, not merely a contract definition.

---

## Ford zero-detector infrastructure

The root-integrated chain has progressed through:

- cotangent detector kernels;
- pole subtraction and correction;
- residues;
- detector centers;
- zeta residues;
- differentiability;
- detector rectangles;
- finite rectangle identities;
- finite edge identities;
- horizontal decay;
- vertical decomposition;
- physical vertical edges;
- left-line analysis.

Representative audited results include:

```lean
GafniTao.fordCotKernel_sub_inv_eq
GafniTao.continuousAt_fordCotKernel_sub_inv_zero
GafniTao.residue_fordCotKernel_translate_mul_eq
GafniTao.fordDetectorZetaLogDeriv_eq
GafniTao.fordZetaDetectorIntegrand_near_zero
GafniTao.fordZetaDetectorIntegrand_near_one
GafniTao.fordZetaDetectorIntegrand_near_center
GafniTao.mem_fordDetectorRectangle_iff
GafniTao.fordZetaDetector_rectangleIntegral_eq_residue_sum
GafniTao.fordZetaDetector_rectangleIntegral_eq_explicit_sum
```

---

# Native Ford K-formula branch

The integrated Ford source program also contains a substantial K-function contour argument.

The root imports:

```text
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
```

The central audit includes:

```lean
GafniTao.summable_fordKZeroShellSum
GafniTao.tendsto_sum_zeroSet_nat_fordKZeroTerm
GafniTao.tendsto_sum_zeroSet_selected_fordKZeroTerm
GafniTao.integrable_fordKSurrogate_leftLine
GafniTao.tendsto_fordK_leftLine_full
GafniTao.fordK_infinite_rectangle_of_selected
GafniTao.fordK_infinite_rectangle_native
GafniTao.integral_ford_leftLine_envelope_le_masses
GafniTao.norm_fordKLeftLineIntegral_le_masses
GafniTao.exists_norm_fordKLeftLineIntegral_le_log
GafniTao.fordK_formula_native
GafniTao.fordK_formula_with_log_error_native
```

This is substantial native Ford analysis.

It does not by itself establish the final Ford source contracts.

---

# Ford source contracts still open

`FordSource.lean` defines three principal source-facing propositions.

## Ford zeta-growth theorem

```lean
GafniTao.FordZetaGrowthBound
```

This records the explicit estimate:

```math
\left|
\zeta(\sigma+it)
\right|
\le
76.2\,
|t|^{4.45(1-\sigma)^{3/2}}
(\log |t|)^{2/3}
```

in the specified source range.

At the current integrated frontier this remains a contract.

The existing native zeta and logarithmic-derivative infrastructure must eventually be assembled into a proof of this statement or an exactly sufficient replacement.

---

## Ford near-one zero density

The source-facing density contract is:

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

The project already proves the exact normalization bridge:

```lean
GafniTao.nearOneLogDensityBound_of_fordNearOneDensityEstimate
```

which converts this to:

```math
N(1-\eta,T)
\le
T^{58.05\,\eta^{3/2}}
(\log T)^{16}
```

after enlarging the lower height threshold.

No `T^{\varepsilon}` loss is spent in this conversion.

The missing work is the source density theorem itself.

---

## Ford asymptotic zero-free region

The source-facing zero-free contract is:

```lean
GafniTao.FordAsymptoticZeroFree
```

It supplies a positive Vinogradov-Korobov width above a sufficiently large height.

The downstream bridge is already implemented:

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

Once the genuine zero-free and density outputs are proved, the project already has:

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

for direct consumption by the Gafni-Tao right-edge machinery.

The downstream normalization and packaging problem is therefore already solved.

---

# New shifted-detector development

The newer, currently unintegrated Ford workbench goes materially beyond the root-integrated detector chain.

It contains a shifted finite-subset inequality in which:

- detector zeros retain analytic multiplicity;
- the zeta pole contribution is explicit;
- right- and left-edge terms remain visible;
- horizontal remainders are bounded;
- selected heights eliminate public boundary nonvanishing assumptions.

A representative endpoint is:

```lean
GafniTao.exists_fordShiftedDetector_selected_subset_inequality
```

The local detector development then specializes this machinery to Ford's local zero disk.

A representative theorem is:

```lean
GafniTao.eventually_exists_fordLocalDisk_detector_inequality
```

which inserts the actual local zero count into the detector inequality.

A still later theorem:

```lean
GafniTao.eventually_exists_fordLocalDisk_detector_growthBound
```

assembles:

- the local zero contribution;
- right-edge Euler-product control;
- pole correction;
- horizontal tails;
- left-edge Ford growth control.

At present this theorem still assumes:

```lean
hFord : FordZetaGrowthBound
```

so it should not be mistaken for closure of the source theorem.

These newer results should be treated as development-frontier work until deliberately imported and audited.

---

# Ford Theorem 2 development

The newer workbench also introduces Ford's shifted logarithmic exponential sum.

The source object is:

```lean
GafniTao.fordShiftedExponentialSum
```

with endpoint convention:

```text
N < n <= R
```

and shift:

```text
0 < u <= 1.
```

The consumer proposition is:

```lean
GafniTao.FordExponentialSumEstimate
```

and the pinned source contract is:

```lean
GafniTao.FordTheorem2
```

defined using the source constants:

```text
9.463
133.66
```

This source contract is not yet proved.

The surrounding workbench contains substantial development of the source argument:

- trivial finite-sum control;
- dyadic decomposition;
- exponent normalization;
- the exact cubic exponent;
- algebraic turning-point analysis;
- unimodality;
- scaling;
- sum-to-integral reduction;
- normalized integral formulas;
- exact numerical upper bounds.

The project must not merely replace reliance on Ford Theorem 1 with an unproved Ford Theorem 2 and then call the Ford source layer complete.

Every source theorem used by the final path must be either proved natively or explicitly accepted as a pinned external theorem according to the project acceptance standard.

---

# Exact numerical certification

The newer Ford workbench contains a serious exact-certification branch.

This includes:

- rational polynomial approximations;
- exact Taylor bounds;
- explicit source-derived data;
- Bernstein-basis positivity certificates;
- subinterval maps;
- exact rational coefficient checks;
- Lean-side verification of inequalities generated during numerical exploration.

The intended trust discipline is correct:

```text
external script
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

The external generator is not proof evidence.

The Lean theorem checking the certificate is the proof evidence.

Before release, generated and probe artifacts should be distinguished clearly from the intended proof dependency path.

---

# Integration criteria for new Ford modules

A new Ford file does not count as completed integrated proof work merely because it exists under `Extension/GafniTao/`.

For a source module to count as integrated:

1. it must be imported by the intended root dependency graph;
2. the isolated package must build with it;
3. public or source-sensitive endpoints must be considered for `Audit.lean`;
4. the actual axiom output must be inspected;
5. the theorem must feed an intended downstream consumer or be clearly identified as reusable infrastructure.

This distinction is especially important while the Ford workbench is expanding rapidly.

---

# Section 3 and numerical consequences

The later published numerical consequences remain open.

The first principal sample target is:

```math
\mu\!\left(\frac{17}{30}\right)
\le
\frac{7}{12}
```

The second is the quantified sufficiently-small-Delta statement corresponding to the second displayed sample bound in the paper.

Closing these requires additional published analytic inputs, including the required:

- Pintz ordinary zero-density segment;
- Heath-Brown four-zero additive-energy segment;
- endpoint compatibility;
- multiplicity compatibility;
- normalization compatibility;
- exact limiting arithmetic.

The full Figure 4 envelope, if pursued, will additionally require a certified finite optimization over the pinned source data.

Floating-point calculations may be used to explore or check.

They must not constitute the final proof.

---

# Theorem 1.1

After the general Gafni-Tao theorem is unconditional, the project should derive the ordinary threshold consequences from a uniform density exponent `A0`.

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

the elementary threshold arithmetic is already represented in Lean.

The remaining theorem must connect the almost-all statement to the actual exceptional-measure framework.

---

# Audit surface

The isolated dependency audit is:

```text
Extension/GafniTao/Audit.lean
```

It imports the root:

```lean
import GafniTao
```

and explicitly runs `#print axioms` on public and source-sensitive results.

The current central audit contains more than just the final theorem wrappers.

It covers major parts of:

- exceptional-set measure theory;
- extended-real exponent machinery;
- multiplicity bridges;
- zero additive energy;
- near-one consumer bridges;
- frozen Guth-Maynard input;
- integrated Ford trigonometric infrastructure;
- integrated Ford Fourier analysis;
- integrated Euler-product and prime-power expansions;
- integrated Ford K-formula infrastructure;
- integrated zero-detector infrastructure;
- local arithmetic entry;
- physical zero sums;
- second and fourth moments;
- strip assembly;
- equation (2.7);
- limit assembly;
- global exceptional cover;
- conditional Theorems 1.2 and 1.3;
- the native sharp-Perron chain;
- the native sharp explicit formula.

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

A declaration appearing in `Audit.lean` means it is on the explicit dependency-audit surface.

It does **not** by itself prove that a fresh release audit has been executed and inspected successfully.

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

and a scan for unfinished or unsafe declarations:

```bash
rg -n '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --glob '*.lean' .
```

Interpret the results carefully.

Compilation alone is not enough.

A proposition that restates a desired source theorem is not a proof of that theorem.

A theorem being present in an unimported file is not evidence that it belongs to the final dependency path.

The actual `#print axioms` output must be inspected.

---

# Source and workbench hygiene

The Ford source-development batch includes:

- source TeX files;
- source archives;
- certificate generators;
- generated exact-data modules;
- temporary probe files;
- development artifacts.

These are not all equivalent.

For final release, classify them explicitly as one of:

```text
source reference
proof module
certificate data
certificate generator
temporary probe
development artifact
```

Temporary probe files and cache artifacts should not be part of the claimed proof dependency.

Generated certificate data is acceptable when Lean independently checks the certificate.

External scripts must not be treated as theorem oracles.

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
6. No project-level `axiom`, `sorry`, `admit`, unsafe shortcut, or disguised restatement supplies the intended result.
7. The theorem is integrated into the intended root import graph.
8. The theorem appears on the audit surface where appropriate.
9. The isolated package builds.
10. The actual axiom output is inspected.
11. Certificate generators are not treated as proof evidence.
12. The Crosswalk, Architecture, Research Agenda, Shitlist, and README agree with the Lean source.
13. Public theorem names do not claim more than their hypotheses justify.

---

# Claim discipline

The strongest safe summary of the current repository is:

> Most of the downstream Gafni-Tao exceptional-interval transfer mechanism has been formalized in Lean. The exact exceptional-set framework, multiplicity-sensitive zero counts, local arithmetic entry, native sharp truncated explicit formula, second- and fourth-moment machinery, equation (2.7), limiting assembly, local-to-global covering argument, frozen Guth-Maynard consumer, and conditional max-forms of Theorems 1.2 and 1.3 are implemented. A substantial Ford source branch is integrated through detector, left-line, K-formula, explicit-zeta, and logarithmic-derivative infrastructure. A newer and larger Ford workbench develops shifted detectors, local zero-disk inequalities, Ford Theorem 2 machinery, cubic sum-to-integral analysis, and exact numerical certificates, but that newer workbench is not yet part of the root or central audit. The complete Gafni-Tao theorem is not yet claimed because the Ford near-one density and asymptotic zero-free outputs remain source contracts, Ford Theorem 2 is also still a source contract where used, the exact unconditional source theorem interfaces remain open, and the later Section 3 inputs and numerical conclusions remain unfinished.

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

## 1. Triage the new Ford workbench

Separate the newer Ford files into:

```text
ready to integrate
needs proof repair
certificate support
source/reference only
probe/development only
```

Do not import 100+ files blindly.

Integrate coherent theorem chains.

---

## 2. Integrate the shifted local detector chain

The most mature new source path appears to be:

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

Bring this chain into the root only after it builds cleanly as part of the intended package.

Add its source-sensitive endpoints to `Audit.lean`.

---

## 3. Close `FordZetaGrowthBound`

The new local growth-bound theorem still consumes:

```lean
FordZetaGrowthBound
```

The source program must eventually prove this contract from the integrated Ford Theorem 1 machinery.

A downstream theorem conditional on `FordZetaGrowthBound` is progress, but it is not source closure.

---

## 4. Close the Ford Theorem 2 dependency

The newer exponential-sum branch currently defines:

```lean
FordTheorem2
```

as a source proposition.

If this theorem is required by the eventual near-one density proof, it must be either:

- proved through the native exponential-sum development; or
- explicitly accepted as a pinned external source theorem under the project's trust rules.

Do not leave it as an invisible assumption in the final path.

---

## 5. Prove `FordNearOneDensityEstimate`

The detector and exponential-sum branches should eventually meet at an explicit theorem:

```lean
FordNearOneDensityEstimate K T0
```

for explicit witnesses `K` and `T0`.

Once this closes, immediately consume the already-proved normalization:

```lean
nearOneLogDensityBound_of_fordNearOneDensityEstimate
```

---

## 6. Prove `FordAsymptoticZeroFree`

Close the pointwise source zero-free statement.

Then consume the already-built path to:

```lean
VinogradovKorobovCountVanishing
```

---

## 7. Package unconditional near-one inputs

Once the density and zero-free source outputs are genuine theorems, instantiate:

```lean
GafniTao.exists_nearOne_inputs_of_ford_outputs
```

The right-edge branch can then stop accepting those assumptions externally.

---

## 8. Remove already-resolved top-level premises

The native sharp truncated explicit formula already exists.

Supply it internally in the final Gafni-Tao wrapper.

Do the same for any cutoff or auxiliary object already available from the frozen foundation.

The final public theorem interface should expose only genuine unresolved mathematics.

---

## 9. Export exact Theorem 1.3

Prove the exact source epsilon-infimum formulation.

Retain the current max-form as a separate useful corollary.

---

## 10. Export exact Theorem 1.2 and Theorem 1.1

Derive the ordinary theorem and the all-interval / almost-all consequences.

Consume the existing frozen GM `30/13` bridge.

---

## 11. Complete Section 3

Formalize the exact Pintz and Heath-Brown source segments.

Then prove the paper's displayed sample bounds.

Only after that should the full optional piecewise optimizer become a priority.

---

## 12. Final release audit

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

**formalization in progress, with most of the downstream Gafni-Tao transfer mechanism implemented, a substantial Ford source chain already integrated, and the active mathematical work concentrated on converting the rapidly growing Ford detector and exponential-sum workbench into audited native source theorems.**