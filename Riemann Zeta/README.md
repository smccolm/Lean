# Riemann Zeta Formalization in Lean 4

[![Riemann Zeta Lean CI](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml/badge.svg)](https://github.com/smccolm/Lean/actions/workflows/riemann-zeta-ci.yml)

Mechanized formalization of finite Dirichlet polynomial conjugation dualities, fourfold completed Zeta function orbits, and complex-valued Hardy-type phase normalization identities in **Lean 4** (pinned to toolchain `leanprover/lean4:v4.30.0-rc2`, package version `0.1.0`). The repository also contains an audit-clean conditional formalization of the Guth–Maynard (2026) Section 13.1 zero-density transfer. Its zeta vertical-growth foundation, Jensen local-zero theorem, Montgomery mean-value theorem, beta-removal theorem, separated Type-I extraction, classical finite mollifier algebra, and detector-to-Jensen bridge are now kernel-checked without project axioms. The fully quantified interior Ingham/Huxley estimates and other remaining primitive inputs are not yet proved, and the executable dependency audit intentionally fails on the one surviving project-postulate dependency.

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
- **[`RiemannZeta/GuthMaynard/DirichletPolynomial.lean`](RiemannZeta/GuthMaynard/DirichletPolynomial.lean)**: Exact interval-indexed Dirichlet polynomials, normalized coefficients, convolution support, and the exact coefficient phase twist induced by translating ordinates, including norm preservation.
- **[`RiemannZeta/GuthMaynard/Statements.lean`](RiemannZeta/GuthMaynard/Statements.lean)**: Exact kernel-checked propositions mapping the Guth-Maynard Large Values Estimate and Zero-Density exponents over polynomial bases.
- **[`RiemannZeta/GuthMaynard/ZetaBounds.lean`](RiemannZeta/GuthMaynard/ZetaBounds.lean)** and **[`ZeroCount.lean`](RiemannZeta/GuthMaynard/ZeroCount.lean)**: Abel-integral continuation, pole-safe polynomial vertical growth, exact multiplicity counts in rectangles, rectangle compactness, zero-set finiteness, right-half-plane control, and a concrete Euler/Möbius lower bound. The zero-count layer contains no project axiom.
- **[`RiemannZeta/GuthMaynard/ExponentArithmetic.lean`](RiemannZeta/GuthMaynard/ExponentArithmetic.lean)**: Complete bounded equation-(13.1) scale selection and kernel-checked F-09/F-10 power-term comparisons, including equation (13.2).
- **[`RiemannZeta/GuthMaynard/PolynomialPowers.lean`](RiemannZeta/GuthMaynard/PolynomialPowers.lean)**: Exact powered expansion, lower-endpoint removal, dyadic block decomposition, translated coefficient normalization, and simultaneous block/ordinate pigeonholing.
- **[`RiemannZeta/GuthMaynard/Transfer.lean`](RiemannZeta/GuthMaynard/Transfer.lean)**: Noncircular primitive-input conditional transfer combining Type-I/residual slabs, the explicit F-01 boundary, and Huxley's high-`σ` branch. Five analytic inputs remain open; its arithmetic inputs now have native proofs.
- **[`RiemannZeta/GuthMaynard/ZeroDetector.lean`](RiemannZeta/GuthMaynard/ZeroDetector.lean)**: The actual truncated Möbius divisor sum with exponential smoothing, exact support inside the full divisor set, cutoff and full-divisor-cardinality magnitude estimates, and the kernel-checked deduction `uniformDetectorCoeffBound_of_divisorCount`. `ArithmeticCoefficients.lean` now supplies its classical divisor premise unconditionally.
- **[`RiemannZeta/GuthMaynard/ExtractSeparated.lean`](RiemannZeta/GuthMaynard/ExtractSeparated.lean)**: Kernel-checked pole-safe Jensen proof of the ordinary unit-zero multiplicity bound, plus weighted dyadic pigeonholing, shifted-multiplicity aggregation, and normalized Type-I separated extraction. Lean proves the shifted-bin finite covering, raw enlarged-interval estimate, simultaneous ordinate/coefficient translation to `[0,3T]`, phase-norm preservation, and absorption of the `T^δ (log T)^2` loss into a pure epsilon power.
- **[`RiemannZeta/GuthMaynard/BetaDependence.lean`](RiemannZeta/GuthMaynard/BetaDependence.lean)**: Axiom-free beta removal by rational right-half-plane localization and Phragmén–Lindelöf. `beta_dependence_removal` supplies the exact pointwise fixed-line shift, and `extractSeparated_native` combines it with the Jensen theorem to make separated extraction unconditional.
- **[`RiemannZeta/GuthMaynard/PolynomialPowers.lean`](RiemannZeta/GuthMaynard/PolynomialPowers.lean)**: Powered-polynomial and convolution-coefficient definitions, the kernel-checked exact expansion `polynomial_power_identity`, and the conditional coefficient-bound assembly. The expansion handles all `k`, including the empty-product case.
- **[`RiemannZeta/GuthMaynard/ArithmeticCoefficients.lean`](RiemannZeta/GuthMaynard/ArithmeticCoefficients.lean)**: Unconditional subpolynomial divisor and ordered-factorization bounds, with `powCoeffBound_native` specializing the powered detector-coefficient estimate without arithmetic premises.
- **[`RiemannZeta/GuthMaynard/MeanValueProof.lean`](RiemannZeta/GuthMaynard/MeanValueProof.lean)**: Unconditional proof of `MontgomeryMeanValue` from exact continuous mean square, a finite reciprocal-log Hilbert inequality, and local Sobolev sampling on separated sets.
- **[`RiemannZeta/GuthMaynard/ClassicalDensity.lean`](RiemannZeta/GuthMaynard/ClassicalDensity.lean)**: Exact finite Möbius mollifier convolution and coefficient cancellation, a globally analytic pole-free Ingham detector, zeta-zero multiplicity inheritance, detector-to-Jensen divisor bounds, a full unit-bin Jensen estimate down to `σ = 1/2`, dyadic and symmetric exponent-one bounds, and the exact Ingham/Huxley boundary cases currently accessible from those bounds. The interior density estimates remain open.
- **[`RiemannZeta/GuthMaynard/ClassicalMoments.lean`](RiemannZeta/GuthMaynard/ClassicalMoments.lean)**: Exact continuous mean-square expansion and Hilbert-kernel estimate on the full interval `1 ≤ n ≤ X`, specialized to the actual Möbius mollifier to prove `∫₀ᵀ |M_X(1/2+it)|² dt ≤ (T + O(X))(1 + log X)`. The stronger contour moments remain open, but they are retained as optional infrastructure rather than mandatory #15 blockers.
- **[`RiemannZeta/GuthMaynard/ClassicalArgumentPrinciple.lean`](RiemannZeta/GuthMaynard/ClassicalArgumentPrinciple.lean)**: Project specialization of the vendored PNT+ rectangle-residue framework. It proves the multiplicity-aware logarithmic-derivative argument principle for analytic functions and for the pole-free Ingham detector, with finite order and boundary nonvanishing kept explicit, and derives `‖ζ(s)‖ ≤ 20 |Im(s)|` on `1/2 ≤ Re(s) < 3`, `|Im(s)| ≥ 1`. Weighted Littlewood and the remaining edge estimates are optional unfinished extensions, not the selected #15 path.
- **[`RiemannZeta/GuthMaynard/ZetaTruncation.lean`](RiemannZeta/GuthMaynard/ZetaTruncation.lean)**: Kernel-checked first-order Euler–Maclaurin truncation on `Re(s) > 0`, proved from the project Abel continuation and Mathlib finite Abel summation. It includes the exact specialization at an off-axis zeta zero and the uniform error `‖ρ‖ b⁻ᴿᵉ⁽ρ⁾ / Re(ρ)`.
- **[`RiemannZeta/External/PNT`](RiemannZeta/External/PNT)**: Apache-2.0 PNT+ rectangle geometry, divisor-support finiteness, residue calculus, and argument-principle infrastructure adapted to the pinned Lean 4.30 toolchain. Every one of its 107 public theorems is included in the synchronized transitive audit; provenance is recorded in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).
- **[`RiemannZeta/GuthMaynard/InghamBound.lean`](RiemannZeta/GuthMaynard/InghamBound.lean)**: Faithful statements of the Ingham and Huxley endpoints and the kernel-checked combined-exponent transfer. The two concrete endpoint theorems remain open.
- **[`RiemannZeta/GuthMaynard/HalaszMontgomery.lean`](RiemannZeta/GuthMaynard/HalaszMontgomery.lean)**: Kernel-checked derivation of the basic `V⁻²` large-value counting consequence, now with native specialization `halasz_montgomery_lemma_native` from the proved mean-value theorem. It does not yet contain the stronger classical Montgomery–Halász–Huxley `T * N^4 * V⁻⁶` branch required for the concrete Huxley density endpoint.
- **Selected #15 path**: The zero-specialized Euler–Maclaurin package is complete. The remaining work is targeted van der Corput B/A and Weyl estimates; the full classical Montgomery–Halász–Huxley large-values theorem; and a finite exact-`σ` zero-density transfer. Final assembly must prove the concrete Ingham and Huxley propositions; `huxley_zero_density_at_three_quarters_of_ingham` already supplies the Huxley `σ = 3/4` boundary from Ingham because both exponents equal `3/5` there.
- **[`RiemannZeta/GuthMaynard/TypeIIZeros.lean`](RiemannZeta/GuthMaynard/TypeIIZeros.lean)**: Source-facing short Möbius polynomial and Gamma–zeta contour Type II definitions, eventual-in-height coverage, and audit-clean generic and concrete deductions of `ResidualZeroBoundProp` from explicit coverage, Appendix C reduction, and fourth-moment inputs. The three analytic inputs remain unproved.
- **[`RiemannZeta/GuthMaynard/Decoupling.lean`](RiemannZeta/GuthMaynard/Decoupling.lean)**: Compiling decoupling statement infrastructure whose broad–narrow, incidence, and final bounds remain axiomatic.
- **[`RiemannZeta/GuthMaynard/LargeValues.lean`](RiemannZeta/GuthMaynard/LargeValues.lean)**: Production module reserving the F-06 proof boundary; it currently makes no large-values proof claim.
- **[`RiemannZeta/GuthMaynard/Transfer.lean`](RiemannZeta/GuthMaynard/Transfer.lean)**: Conditional zero-density transfer theorem parameterizing the final exponent over explicit hypotheses from F-01 through F-10.
- **[`RiemannZeta/Audit.lean`](RiemannZeta/Audit.lean)**: Executable transitive dependency audit covering all 447 exported source-level theorems across every production module, including the globally named public declarations in the vendored PNT+ modules.

---

## 5. Build Instructions

### Verification

Ensure you have Lean `v4.30.0-rc2` installed. On Windows, the principal human-facing verification is:
```powershell
run_lake_build.bat
```

For CI or a terminal session, use `run_lake_build.bat --no-pause`. The audit can also be run directly with `lake env lean RiemannZeta/Audit.lean`.

The runner performs five warning-failing Lean stages: the default production build, redundant explicit production-module coverage, both retained examples, and the transitive axiom audit. Its integrity scans use `--no-ignore`. The latest completed run, `logs/overall_proof_20260809_032335.log`, passed stages 1–4 with zero warnings and synchronized 447/447 declarations. Every new #15 truncation theorem is audit-clean. Only `l2_decoupling_bound_native` has a project-specific axiom dependency. Two direct project axioms remain, both in `Decoupling.lean`, so the principal runner correctly reports overall `FAIL` with exit code `1` until #19 is discharged.

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
