# Riemann Zeta Formalization in Lean 4

[![Riemann Zeta Lean CI](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml/badge.svg)](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml)

Mechanized formalization of finite Dirichlet polynomial conjugation dualities, fourfold completed Zeta function orbits, and complex-valued Hardy-type phase normalization identities in **Lean 4** (pinned to toolchain `leanprover/lean4:v4.30.0-rc2`, package version `0.1.0`). The repository also contains provisional infrastructure for the Guth–Maynard (2026) zero-density program. The Section 13.1 transfer and its analytic inputs are not yet proved; the executable dependency audit intentionally fails while project postulates remain.

Author: **S. McColm**

---

## Package Structure

- **[`RiemannZeta/FiniteDirichletPolynomial.lean`](RiemannZeta/FiniteDirichletPolynomial.lean)**: Finite Dirichlet polynomials over positive naturals $\mathbb{N}_+$, conjugation invariance $\overline{A(s)} = A^*(\overline{s})$, norm equality, threshold equivalence, and two-way zero conjugation.
- **[`RiemannZeta/CrossNormProduct.lean`](RiemannZeta/CrossNormProduct.lean)**: Cross-norm product quantity $\text{crossNormProduct}(a, S, \sigma_1, \sigma_2, t) = \|A(\sigma_1+it)\| \cdot \|A^*(\sigma_2-it)\|$, factor swap invariance, real-part upper bound, and zero-factor characterization.
- **[`RiemannZeta/CompletedZetaSymmetry.lean`](RiemannZeta/CompletedZetaSymmetry.lean)**: Coordinate representation of Mathlib's completed Riemann Zeta functional equation $\Lambda(\sigma+it) = \Lambda(1-\sigma-it)$ and fourfold zero orbit under two assumed conjugate zeros.
- **[`RiemannZeta/HardyZ.lean`](RiemannZeta/HardyZ.lean)**: Classical Riemann-Siegel theta angle $\theta(t)$, complex-valued Hardy-type phase normalization $H(t) = e^{i\theta(t)}\zeta(1/2+it)$, norm equivalence $\|H(t)\| = \|\zeta(1/2+it)\|$, zero equivalence $H(t)=0 \iff \zeta(1/2+it)=0$, and conditional norm parameter negation symmetry $\|H(-t)\| = \|H(t)\|$.
- **[`RiemannZeta/Nonvanishing.lean`](RiemannZeta/Nonvanishing.lean)**: Classical non-vanishing along $\mathrm{Re}(s) = 1$ for $t \neq 0$ excluding the pole at $s = 1$, with Mathlib totalization disclosure.
- **[`RiemannZeta/GuthMaynard/Asymptotics.lean`](RiemannZeta/GuthMaynard/Asymptotics.lean)**: Asymptotic relations matching the Guth-Maynard epsilon-power convention $T^{o(1)}$, equipped with `EpsilonPowerBound` defining properties.
- **[`RiemannZeta/GuthMaynard/Separated.lean`](RiemannZeta/GuthMaynard/Separated.lean)**: Properties and translation symmetries for bounded 1-separated sets, plus kernel-checked unweighted and multiplicity-weighted selection from unit-bin occupancy bounds.
- **[`RiemannZeta/GuthMaynard/Statements.lean`](RiemannZeta/GuthMaynard/Statements.lean)**: Exact kernel-checked propositions mapping the Guth-Maynard Large Values Estimate and Zero-Density exponents over polynomial bases.
- **[`RiemannZeta/GuthMaynard/ZeroCount.lean`](RiemannZeta/GuthMaynard/ZeroCount.lean)**: Exact multiplicity counts of `riemannZeta` zeros in rectangles. Rectangle compactness and zero-set finiteness are now proved from Mathlib rather than postulated.
- **[`RiemannZeta/GuthMaynard/ExponentArithmetic.lean`](RiemannZeta/GuthMaynard/ExponentArithmetic.lean)**: Zero-`sorry` formulation of exact rational inequalities, integer parameter bounds, and rational exponent limits utilized in Section 13.1.
- **[`RiemannZeta/GuthMaynard/ZeroDetector.lean`](RiemannZeta/GuthMaynard/ZeroDetector.lean)**: The actual truncated Möbius divisor sum with exponential smoothing, exact divisor-variable support, a cutoff-uniform magnitude estimate in `n` for each fixed `T`, the resulting detector polynomial, finite admissible dyadic scales with an `O(log T)` count, and distinct Type I and residual-zero specifications. The stronger `T`-uniform form needed for powering is exposed separately as `UniformDetectorCoeffBoundProp`.
- **[`RiemannZeta/GuthMaynard/ExtractSeparated.lean`](RiemannZeta/GuthMaynard/ExtractSeparated.lean)**: Kernel-checked weighted dyadic pigeonholing, shifted-multiplicity aggregation, and a corrected uniform/eventual Type-I extraction theorem conditional on explicit beta-shift and local-multiplicity inputs. The output uses the justified enlarged height interval.
- **[`RiemannZeta/GuthMaynard/PolynomialPowers.lean`](RiemannZeta/GuthMaynard/PolynomialPowers.lean)**: Powered-polynomial and convolution-coefficient definitions plus the kernel-checked conditional theorem `powCoeff_bound_of_uniform_detector_and_factorization`. The theorem derives the source-faithful coefficient bound from explicit `UniformDetectorCoeffBoundProp` and `FactorizationCountBoundProp` inputs. The former general divisor axiom is removed; proving those two classical arithmetic inputs and the coefficient expansion of `powPoly` remain open.
- **[`RiemannZeta/GuthMaynard/MeanValue.lean`](RiemannZeta/GuthMaynard/MeanValue.lean)**: Source-faithful statement of the discrete Dirichlet-polynomial mean-value input with one absolute implied constant. It is an unproved proposition specification, not a project axiom or an unconditional theorem.
- **[`RiemannZeta/GuthMaynard/InghamBound.lean`](RiemannZeta/GuthMaynard/InghamBound.lean)**: Statement of the Ingham bound hypothesis and definition of the combined zero-density transfer (F-12).
- **[`RiemannZeta/GuthMaynard/HalaszMontgomery.lean`](RiemannZeta/GuthMaynard/HalaszMontgomery.lean)**: Kernel-checked derivation of the large-value counting consequence from an explicit `MontgomeryMeanValue` parameter. It no longer contains or claims the unrelated Type II bound.
- **[`RiemannZeta/GuthMaynard/TypeIIZeros.lean`](RiemannZeta/GuthMaynard/TypeIIZeros.lean)**: Source-facing short Möbius polynomial and Gamma–zeta contour Type II definitions, explicit coverage/reduction/fourth-moment proposition inputs, and an audit-clean generic deduction of the residual-zero bound from those inputs. The analytic inputs and concrete zeta-zero instantiation remain unproved.
- **[`RiemannZeta/GuthMaynard/Decoupling.lean`](RiemannZeta/GuthMaynard/Decoupling.lean)**: Compiling decoupling statement infrastructure whose broad–narrow, incidence, and final bounds remain axiomatic.
- **[`RiemannZeta/GuthMaynard/LargeValues.lean`](RiemannZeta/GuthMaynard/LargeValues.lean)**: Production module reserving the F-06 proof boundary; it currently makes no large-values proof claim.
- **[`RiemannZeta/GuthMaynard/Transfer.lean`](RiemannZeta/GuthMaynard/Transfer.lean)**: Conditional zero-density transfer theorem parameterizing the final exponent over explicit hypotheses from F-01 through F-10.
- **[`RiemannZeta/Audit.lean`](RiemannZeta/Audit.lean)**: Executable transitive dependency audit covering all 123 exported source-level theorems across every production module.

---

## 5. Build Instructions

### Verification

Ensure you have Lean `v4.30.0-rc2` installed. On Windows, the principal human-facing verification is:
```powershell
run_lake_build.bat
```

For CI or a terminal session, use `run_lake_build.bat --no-pause`. The audit can also be run directly with `lake env lean RiemannZeta/Audit.lean`.

The default root imports every intended production module and builds with zero Lean warnings. The audit list and discovered production theorem set currently both contain 123 declarations. The audit exits nonzero because 6 theorems have project-specific axiom dependencies; no audited theorem depends on `sorryAx`. The zeta-zero finiteness, dyadic-scale, weighted-selection, finite-extraction, and conditional Type-I extraction results all pass, as do the earlier detector, powered-coefficient, mean-value consequence, and generic Type II deductions. Fourteen direct project axioms remain, so the principal proof runner correctly reports overall `FAIL` until those obligations are discharged.

---

## Contribution Taxonomy & AI Tool Disclosure

- **Contribution Layers**:
  1. *New Definitions & Finite Dualities*: `dirichletPoly`, `conjCoeff`, `crossNormProduct`, conjugation invariance.
  2. *Coordinate Wrappers*: Packaging Mathlib's `completedRiemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re` into coordinate representations.
  3. *Complex Phase Normalization*: Formalizing $H(t) = e^{i \theta(t)} \zeta(1/2 + i t)$ as a complex-valued phase normalization ($H : \mathbb{R} \to \mathbb{C}$).
  4. *Inherited Analytic Foundations*: Functional equation and boundary non-vanishing inherited directly from Mathlib 4.
  5. *Guth-Maynard Target Infrastructure*: Statement formulations and explicit asymptotic machinery required for the zero-density deduction sequence.

- **AI Tool Disclosure**: All Lean 4 proof developments, manuscript drafts, and verification steps were assisted by AI coding agents (Antigravity/Gemini). S. McColm performed overall mathematical oversight, project specification, design review, and accepts full responsibility for the mathematical content.

---

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
