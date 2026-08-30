# Publication Readiness and Semantic Audit

Status date: 29 August 2026

This document is the project's adversarial review packet. It records an internal source-to-Lean comparison, but it is not an independent referee report and does not claim publication, community acceptance, or canonicalization. The distinction is deliberate: the principal runner establishes that Lean accepts the declarations and that the repository's stated integrity gates pass. It cannot establish that the formal statements are the best, most natural, or universally accepted translations of the cited mathematics.

## 1. One-page claim sheet

### What is claimed

- Lean 4, using the pinned toolchain and dependencies, accepts the public theorems listed below.
- The public zero count is a finite sum of analytic vanishing orders of Mathlib's Riemann zeta function over closed rectangles. It therefore counts analytic multiplicity, not merely distinct zeros.
- The project proves five frozen publication-facing contracts: the displayed form of Guth--Maynard Theorem 1.1, the full-range form of Theorem 1.2, the classical Ingham and Huxley bounds, and the combined exponent `30 * (1 - σ) / 13` for that zero count.
- The conditional theorem `guthMaynardZeroDensity_of_largeValues_native` has exactly one visible premise, `GuthMaynardLargeValues`; its proof supplies the other nine inputs to the Section 13.1 transfer from named project theorems.
- The root import graph contains 301 production modules; the two remaining Lean modules are explicit audit/lint regressions. `RiemannZeta/Audit.lean` checks 7,636 registered public declarations and all 14,290 discovered nonprivate project theorems, including generated declarations.
- The source correspondences in this document have been checked internally against the declarations and proof consumers named here. This is an **internal semantic audit**, not independent expert validation.

### What is not claimed

- The repository has not been independently semantically reviewed by an analytic number theorist or Lean expert acting as an external referee.
- This manuscript has not been archived as a public preprint, accepted by a journal, peer reviewed, or canonically integrated into the mathematical literature.
- Kernel acceptance does not prove that citations, exposition, source attribution, or design choices are optimal.
- `twistedZetaFourthMoment_native` is not the full shifted asymptotic formula of Hughes--Young. It is the project-specific mollified fourth-moment upper bound needed by the zero-density transfer.
- The public DFI result is a localized, signed, dyadic specialization of the DFI quadratic-divisor estimate, with the equation-(2) weight and physical scale hypotheses visible. It is not a claim that every theorem in Duke--Friedlander--Iwaniec has been formalized.
- `gmQuantitativeSmoothReflection_native` is a source-strength quantitative consequence modeled on Guth--Maynard Lemma 6.2. It is not a literal transcription of the paper's typography or all surrounding prose.
- No AI system is an author. The human project owner retains responsibility for mathematical claims, source fidelity, attribution, and any future submission.

## 2. Status vocabulary

| Term | Meaning in this repository |
|---|---|
| **Stated** | Lean accepts a definition or proposition; no proof is implied. |
| **Conditionally proved** | Lean proves a conclusion from visible, mathematically narrower hypotheses. |
| **Kernel-checked** | The theorem compiles and its transitive axiom set contains only permitted Lean/Mathlib logical axioms. |
| **Project-integrated** | It is root-imported, included in the dependency audit, and covered by the principal runner. |
| **Internally semantically audited** | A project maintainer has compared the unfolded statement, proof consumers, conventions, and cited source as recorded below. |
| **Externally reviewed** | An independent qualified expert has reviewed the mathematics and formal translation. This status has **not** been reached. |
| **Preprint** | A manuscript is publicly archived. This status has **not** been reached. |
| **Peer reviewed / published** | A journal or equivalent human review process has accepted the work. This status has **not** been reached. |
| **Canonicalized** | The community has digested the result into natural formulations, standard references, or reusable libraries. This status has **not** been reached. |

“Unconditional” is used only when a theorem has no extra mathematical premise beyond the quantified objects and side conditions in the intended statement. It never means “free of Lean's foundational axioms”: ordinary uses of `propext`, `Classical.choice`, and `Quot.sound` remain visible.

## 3. Definitions and conventions

### 3.1 Zero rectangles and multiplicity

`RiemannZeta.GuthMaynard.ZeroRectangle σ₁ σ₂ T₁ T₂` is the closed set

\[
\{s\in\mathbf C: σ₁\leq\Re s\leq σ₂,\;T₁\leq\Im s\leq T₂\}.
\]

`zerosInRect` is the finite set of zeros of Mathlib's `riemannZeta` in that rectangle. `analyticVanishingOrder riemannZeta s` is the natural-number analytic order at `s`. Thus

\[
\operatorname{zeroCountRect}(σ₁,σ₂,T₁,T₂)
=\sum_{\substack{\zeta(s)=0\\s\text{ in the closed rectangle}}}
\operatorname{ord}_s\zeta .
\]

The global convention is

\[
N(σ,T)=\operatorname{zeroCountRect}(σ,1,-T,T).
\]

Endpoints are inclusive. The vertical upper real boundary is `Re(s) = 1`; zeros at the pole are excluded because zeta is not zero there. Negative heights are restored by the proved conjugation/multiplicity bridge in `ZeroCount.lean`; `dyadicToGlobalZeroCount` turns positive slabs into the symmetric count.

### 3.2 Epsilon-power bounds

`EpsilonPowerBound f g` unfolds to

```lean
∀ ε : ℝ, ε > 0 →
  (fun T => |f T|) =O[Filter.atTop] (fun T => T ^ ε * |g T|)
```

Hence each positive `ε` may have its own eventual threshold and Big-O constant. No uniformity in `ε` is asserted. Other parameters outside the `T -> infinity` filter are fixed by the surrounding theorem quantifiers. This represents a `T^{o(1)}` or `T^ε` loss, not a numerical finite-height estimate.

### 3.3 Large-values normalization

`sourceDirichletPoly N b t` uses the source sign convention and interval encoded in `Statements.lean`; `InBaseInterval T W` places the finite set in `[0,T]`, and `IsSeparated 1 W` is pairwise unit separation. Coefficients are globally bounded by one. The theorem's constant and height threshold are selected after `ε` and before `N,V,T,b,W`.

### 3.4 Smoothing and localization

The Guth--Maynard proof passes from a sharp source polynomial to three smooth pieces and selects one piece with a cardinality loss. Fourier transforms, trace expansions, reflected polynomials, and energy estimates operate on that selected smooth object. `sourceDirichletPoly_eq_three_gmSmooth` and `source_large_values_localize_to_matrix` are the entry bridges; without them, the matrix argument would concern a detached model.

### 3.5 The project-specific fourth moment

The short mollifier is exactly

```lean
shortMobiusPolynomial T s =
  ∑ m ∈ Finset.Ico 1 (detectorCutoff T),
    (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
```

and

```lean
twistedZetaMomentIntegrand T t =
  ‖shortMobiusPolynomial T (1/2 + t*I) * riemannZeta (1/2 + t*I)‖ ^ 4

twistedZetaFourthMoment T =
  ∫ t in T/2..3*T, twistedZetaMomentIntegrand T t
```

This is why the theorem is a mollifier-specific upper bound rather than the general shifted asymptotic of Hughes--Young.

### 3.6 DFI finite sum and error scale

The finite shifted divisor sum unfolds to

```lean
∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
  if quadraticDivisorShift a b m n = r then
    divisorWeight m * divisorWeight n * f (a*m) (b*n)
  else 0
```

and the error scale in the public localized theorem is exactly

\[
P^{5/4}(X+Y)^{1/4}(XY)^{1/4+ε}.
\]

For a nonnegative shift the signed central term is `dfiEquation27CentralSeries a b r.toNat f`; for a negative shift it is the corresponding series with `a,b` and coordinates swapped. `DFIEquation2` is the source weight's support/derivative profile, while `DFILocalizedBox` is the literal dyadic-box support condition. These are genuine analytic side conditions, not proof certificates for the desired error estimate.

## 4. Public theorem/source crosswalk

All names below are in namespace `RiemannZeta.GuthMaynard`. The canonical verifier's environment-level transitive audit reports every result below as `PASS` with exactly the dependency set

```text
[propext, Classical.choice, Quot.sound]
```

and no project axiom or `sorryAx`. The five publication contracts have exact-type gates and explicit `#print axioms` commands. This is not a claim that Lean is axiom-free. A future implementation refactor can change the harmless subset, so the executable audit remains authoritative.

### 4.0 Frozen publication contracts

`RiemannZeta/PublicationContract.lean` defines and proves:

- `guthMaynardLargeValues_published_native : PublishedGuthMaynardLargeValues`;
- `guthMaynardZeroDensity_published_native : PublishedGuthMaynardZeroDensity (fun sigma T => N sigma T)`;
- `inghamZeroDensity_published_native : PublishedInghamZeroDensity (fun sigma T => N sigma T)`;
- `huxleyZeroDensity_published_native : PublishedHuxleyZeroDensity (fun sigma T => N sigma T)`; and
- `combinedZeroDensity_published_native : PublishedCombinedZeroDensity (fun sigma T => N sigma T)`.

The first contract uses the closed displayed sum `N ≤ n ≤ 2N`, positive phase, one-separated ordinates in `[0,T]`, and the coefficient bound only on that support. Its proof restricts coefficients, proves the open/closed endpoint identity, handles the left endpoint by a triangle inequality, and absorbs the bounded-`V` case using separation. The second contract covers the literal range `1/2 ≤ sigma ≤ 1`; below `7/10` it consumes native Ingham plus `ingham_exponent_le_guthMaynard_exponent`, and above `7/10` it consumes the internal native Guth--Maynard theorem. Thus neither contract is a renamed internal proposition.

The exact source editions and conventions are frozen in [`verification/SOURCE_FREEZE.md`](verification/SOURCE_FREEZE.md).

### 4.1 `ingham_zero_density_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.ingham_zero_density_native`.
- **Unfolded statement:** for every real `σ` with `1/2 ≤ σ ≤ 1` and every `ε>0`,
  \[
  |N(σ,T)|=O_{T\to\infty}\left(T^ε\left|T^{3(1-σ)/(2-σ)}\right|\right).
  \]
  Here `N(σ,T)=zeroCountRect σ 1 (-T) T` counts analytic multiplicity.
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Source:** the classical Ingham density exponent as used in Guth--Maynard Section 13.1 and in the ANTEDB classical zero-density chapter.
- **Bridges:** exact endpoint theorems at `σ=1/2,1`; `ingham_endpoint_positive_slab_native` for the strict interior; nonnegative-exponent arithmetic; `dyadicToGlobalZeroCount` for positive-slab to symmetric height.
- **Dependencies:** `classical_endpoint_positive_slab_native`, the Ingham endpoint scale certificate, endpoint lemmas, zeta conjugation with analytic order, and dyadic summation.
- **Convention differences:** the source's `T^{o(1)}` is `EpsilonPowerBound`; rectangles are closed and multiplicity-weighted; all endpoint cases are explicit.
- **Module/import path:** `NativeZeroDensity.lean`, imported by `RiemannZeta.lean`; listed and axiom-printed in `Audit.lean`.

### 4.2 `huxley_zero_density_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.huxley_zero_density_native`.
- **Unfolded statement:** for every `3/4 ≤ σ ≤ 1` and `ε>0`,
  \[
  |N(σ,T)|=O\left(T^ε\left|T^{3(1-σ)/(3σ-1)}\right|\right).
  \]
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Source:** Huxley's classical zero-density exponent, used by Guth--Maynard for the high-`σ` range.
- **Bridges:** `σ=3/4` is inherited from the already proved Ingham theorem because the exponents agree; `σ=1` is separate; the strict interior uses the Huxley endpoint certificate and the same positive-slab/symmetric-count bridge.
- **Dependencies:** `ingham_zero_density_native`, `huxley_endpoint_positive_slab_native`, endpoint and dyadic-transfer lemmas.
- **Module/import path:** `NativeZeroDensity.lean` -> `RiemannZeta.lean` -> `Audit.lean`.

### 4.3 `classical_endpoint_positive_slab_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.classical_endpoint_positive_slab_native`.
- **Unfolded statement:** for `1/2<σ<1`, if `EndpointScaleCertificate σ τ₀` holds, then for every `ε>0`,
  \[
  zeroCountRect(σ,1,T,2T)=O\left(T^εT^{3(1-σ)/τ₀}\right).
  \]
- **Status:** conditionally proved from the explicit arithmetic certificate; the Ingham and Huxley specializations construct that certificate natively. Kernel-checked and project-integrated.
- **Source:** the finite classical zero-density engine organized around the ANTEDB Type-I/Type-II treatment and the Ingham/Huxley scale choices; the certificate packages elementary endpoint exponent inequalities rather than assuming the density conclusion.
- **Actual consumer:** `classical_endpoint_positive_slab_of_medium_native` calls `classical_typeI_typeII_dichotomy_native`, destructs the zero, Type-I, and Type-II alternatives, and passes their literal witness sets and multiplicity bounds to the native consumers.
- **Dangerous bridges checked:** the Type-I logarithmic scale `τ=log_N T`; low/basic/powered/short/medium dispatch; arbitrary-`X` Type-II powering; `Nat.clog` and harmonic losses; enlarged ordinate intervals; the common `ε/100` budget; analytic multiplicity factors.
- **Module/import path:** `ClassicalEndpointDensity.lean` -> `NativeZeroDensity.lean` -> root and audit.

### 4.4 `guthMaynardLargeValues_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.guthMaynardLargeValues_native`.
- **Unfolded statement:** for every `ε>0`, there are `C>0` and `T₀≥1` such that for every positive natural `N`, `T≥T₀`, `V>0`, coefficient function `b` with `||b n||≤1`, and finite unit-separated `W⊆[0,T]` satisfying `V≤||sourceDirichletPoly N b t||` for `t∈W`,
  \[
  |W|\le C T^ε\left(N^2V^{-2}+N^{18/5}V^{-4}+T N^{12/5}V^{-4}\right).
  \]
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Source:** Guth--Maynard, *New large value estimates for Dirichlet polynomials*, Theorem 1.1, Annals of Mathematics 203 (2026), 623--675, DOI `10.4007/annals.2026.203.2.6`.
- **Proof architecture:** sharp-to-smooth three-piece localization; matrix/trace reduction (Lemmas 4.1--4.2); Poisson and trace splitting; `S1`, `S2`, and `S3`; Lemma 6.2 reflection; affine localization; GCD/spacing energy; Sections 3 and 12 assembly; classical complementary ranges.
- **Convention bridges:** this internal theorem uses `(N,2N]` and a global coefficient bound. The published theorem display uses `[N,2N]` and a support-only coefficient bound; `guthMaynardLargeValues_published_native` proves the bridge. Source polynomial sign, coefficient normalization, one-separated finite sets, physical height, and low/high/near-height ranges all have named consumers. The constant order matches the source asymptotic quantifier order.
- **Module/import path:** `LargeValuesFinal.lean` -> `LargeValues.lean`/`NativeZeroDensity.lean` -> root and audit.

### 4.5 `gmQuantitativeSmoothReflection_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.gmQuantitativeSmoothReflection_native`.
- **Unfolded statement:** for a `GMSmoothCutoff cutoff`, for every `A,ε>0` there are `C>0`, `T_min≥1` such that whenever
  `T≥T_min`, `N>0`, `N≤T`, `T^ε≤T₀≤|t|≤2T₀`, and `|t|≤T`,
  \[
  \|\operatorname{NonzeroFourierSum}(cutoff,N,t)\|
  \le {C\over\sqrt{T₀}}
  \int_{-T^η}^{T^η}\!\|D_{M(t)}(t,u)\|\,du+{C\over T^A},
  \]
  where `η=min(ε/16,1/16)` and `M(t)=ceil((1+|t|)T^η/N)` through the named definitions.
- **Status:** kernel-checked consequence for any admissible cutoff; project-integrated and internally audited. `gmQuantitativeSmoothReflection_hundred` sets `A=100`.
- **Source:** Guth--Maynard Lemma 6.2 and its Section 6 use in the `S2` estimate.
- **Bridges:** the complete nonzero integer `tsum`, positive/negative frequency symmetry, exact scaling by `N`, finite core/tail split, Mellin decay order, `T₀^{-1/2}` stationary factor, and the `T^{-A}` tail are explicit. The downstream scaled cubic-`S2` consumer is part of the audited chain.
- **Caution:** this is a strengthened quantitative formulation adapted to Lean and does not claim textual identity with every display in Lemma 6.2.
- **Module/import path:** `QuantitativeSmoothReflection.lean` -> `LargeValuesS2.lean` -> final large-values chain -> root and audit.

### 4.6 Localized signed DFI theorem

- **Fully qualified name:** `RiemannZeta.GuthMaynard.exists_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale_native`.
- **Unfolded statement:** given reals `P,X,Y,U,Q,ε`, a weight `f`, the equation-(2) derivative/profile hypothesis `DFIEquation2 f P X Y`, literal box localization `DFILocalizedBox f X Y`, `U≤P^{-1}min(X,Y)`, `Q≥8`, `U=Q²`, `Q²=P^{-1}(X+Y)^{-1}XY`, and `0<ε<4`, there is `C>0` such that for positive coprime naturals `a,b`, natural `M,N`, and nonzero integer shift `r`, with the displayed size and sign-dependent shift bounds,
  \[
  \|D_f(a,b,M,N,r)-\mathcal C_{\rm signed}(a,b,r;f)\|
  \le C\,\operatorname{DFIErrorScale}(P,X,Y,ε).
  \]
- **Status:** conditionally proved from the source weight and physical scale hypotheses; the auxiliary cutoffs and both shift signs are constructed inside the proof. Kernel-checked and project-integrated.
- **Source:** Duke--Friedlander--Iwaniec, *A quadratic divisor problem*, Invent. Math. 115 (1994), 209--217, DOI `10.1007/BF01231758`, especially equation (2), equations (9)--(30), and Theorem 1. The project theorem is the localized signed specialization used by Hughes--Young.
- **Bridges:** negative shifts are converted by coordinate swap; the error scale is proved symmetric in `X,Y`; redundant cutoff and delta weight are constructed; the central series uses the sign-aware equation-(27) form.
- **Caution:** “DFI theorem complete” in old prose meant complete for this consumer. It must not be read as formalizing every result or every generality in the DFI article.
- **Module/import path:** `DFITheorem1.lean` -> Hughes--Young consumer modules -> `HughesYoungNativeCompletion.lean` -> root and audit.

### 4.7 `twistedZetaFourthMoment_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.twistedZetaFourthMoment_native`.
- **Unfolded statement:** for every `ε>0`,
  \[
  |\operatorname{twistedZetaFourthMoment}(T)|=O\left(T^{1+ε}\right),
  \]
  where the moment is the interval integral over `[T/2,3T]` of `twistedZetaMomentIntegrand T t`; that integrand contains the project's actual detector/mollifier and `|ζ(1/2+it)|^4`.
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Source:** the upper-bound consequence extracted from Hughes--Young, *The twisted fourth moment of the Riemann zeta function*, J. Reine Angew. Math. 641 (2010), 203--236, arXiv:0709.2345, using their approximate functional equation, diagonal/off-diagonal split, DFI application around equations (78)--(80), and error estimate.
- **Dependencies:** exact sharp-to-smooth majorant; completed-zeta-square AFE; diagonal estimate; localized signed DFI theorem; Hughes--Young finite off-diagonal and complementary-tail assemblies.
- **Convention bridges:** the paper's shifted asymptotic is specialized to an upper bound, smoothed, summed over the actual mollifier coefficients, and then transferred back to the nonnegative sharp moment. The interval is `[T/2,3T]`, not the paper's generic compactly supported weight interval.
- **Caution:** this theorem is not the full Hughes--Young asymptotic formula. Its correct name in exposition is “native twisted-fourth-moment input bound.”
- **Module/import path:** `HughesYoungNativeCompletion.lean` -> `NativeZeroDensity.lean` -> root and audit.

### 4.8 `guthMaynardZeroDensity_of_largeValues_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.guthMaynardZeroDensity_of_largeValues_native`.
- **Unfolded statement:** assuming `GuthMaynardLargeValues`, for every `7/10≤σ≤1` and `ε>0`,
  \[
  |N(σ,T)|=O\left(T^ε\left|T^{15(1-σ)/(3+5σ)}\right|\right).
  \]
- **Status:** conditionally proved from one explicit narrower source theorem; kernel-checked and project-integrated.
- **Source:** Guth--Maynard Section 13.1 and Theorem 1.2.
- **Actual supplied inputs:** `montgomery_mean_value_native`, `beta_dependence_removal`, `localZeroMultiplicityBound_native`, divisor and factorization bounds, Appendix C coverage, fourth-moment reduction, `twistedZetaFourthMoment_native`, and `huxley_zero_density_native`.
- **Consumer check:** `conditionalZeroDensityTransfer` derives separated extraction, powered coefficient bounds, Type-I and residual slab bounds, destructs the central/high-`σ` split, and performs dyadic-to-global conversion. It does not return a conclusion-equivalent premise.
- **Module/import path:** `NativeZeroDensity.lean` -> root and audit.

### 4.9 `guthMaynardZeroDensity_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.guthMaynardZeroDensity_native`.
- **Unfolded statement:** the same `7/10≤σ≤1` multiplicity-weighted estimate as §4.8, with no mathematical hypothesis.
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Proof:** specializes the one-premise consumer with `guthMaynardLargeValues_native`.
- **Source:** the high-range Section 13.1 component of Guth--Maynard Theorem 1.2. This restricted internal proposition is not the literal full-range published statement; §4.0 records the full-range consumer.
- **Module/import path:** `NativeZeroDensity.lean` -> root and audit.

### 4.10 `combined_zero_density_native`

- **Fully qualified name:** `RiemannZeta.GuthMaynard.combined_zero_density_native`.
- **Unfolded statement:** for every `1/2≤σ≤1` and `ε>0`,
  \[
  |N(σ,T)|=O\left(T^ε\left|T^{30(1-σ)/13}\right|\right).
  \]
- **Status:** kernel-checked, project-integrated, internally semantically audited.
- **Source:** Guth--Maynard equation (1.4), obtained by combining their new density estimate with Ingham's classical estimate.
- **Actual consumer:** `combined_zero_density_transfer_native` branches on `σ≤7/10`; it proves both exponent comparisons and consumes `ingham_zero_density_native` and `guthMaynardZeroDensity_native`.
- **Module/import path:** `NativeZeroDensity.lean` -> `RiemannZeta.lean`; explicit audit and output gate.

## 5. Human-readable proof guide

### 5.1 The #15 classical chain

The classical detector produces a finite alternative for a positive height slab: the zero count is zero, a Type-I polynomial is large on a separated witness family, or a Type-II polynomial is large on such a family. The central idea is that zeros force a large finite Dirichlet-polynomial witness, and separated large-value estimates bound how many witnesses can occur.

The zero case is immediate. The Type-I case is the delicate routing problem: define the physical logarithmic scale `τ=log_N T`, then send it to a direct Montgomery--Halász--Huxley bound, a powered version, a weighted Weyl estimate, a short-gap estimate, or the medium reflected B-process. The Type-II case normalizes the actual cutoff, raises the polynomial to a bounded natural power, extracts a dyadic block, and applies the coefficient-uniform MHH theorem. All branches restore the multiplicity loss from selecting representative ordinates.

The real analytic burden lies in the MHH/Weyl estimates and the medium reflection machinery. Floors, `Nat.clog`, harmonic sums, bounded powers, interval displacement, and `ε/100` allocation are lengthy but conceptually bookkeeping. Expert readers should slow down at the source normalization `N^σ`, the identity linking `τ,N,T`, and the conversion from witness cardinality back to analytic multiplicity.

Substituting `τ₀=2-σ` gives Ingham; substituting `τ₀=3σ-1` gives Huxley. Conjugation and dyadic summation turn `[T,2T]` into `[-T,T]` without discarding multiplicity.

### 5.2 The #18 contour and twisted-moment chain

Appendix C separates Type-I zeros from a contour-defined Type-II residual. Mellin inversion, cancellation of the detector at zeros, a rectangle shift, the single residue, gamma decay, and dyadic extraction reduce the residual count to a fourth moment on the critical line.

The zeta-square approximate functional equation is opened with a smooth completed-xi contour. The diagonal `hm=kn` contribution is regrouped and bounded directly. The off-diagonal `hm-kn≠0` contribution is the hard part: the DFI delta method yields a signed central series plus an optimized error; Hughes--Young's cleaning and summation turn that pointwise shifted-divisor estimate into the finite mollified fourth-moment bound.

This chain contains convention-changing bridges that deserve independent checking: completed versus ordinary zeta, sharp versus smooth moment, sign of the shift, coprime reduction, dyadic box support, and the final nonnegative sharp-moment majorization. The project proves the upper bound needed for zero density, not every main-term identity in Hughes--Young.

### 5.3 The #19 large-values chain

Start with a sharp source Dirichlet polynomial large on a one-separated set. Split it exactly into three smooth pieces; retain a common piece on at least one third of the set. Encode the evaluations as a sampling matrix. Operator and trace inequalities reduce the cardinality question to first and cubic trace estimates.

Poisson summation exposes frequency zero and nonzero modes. The cubic trace is partitioned into `S1`, `S2`, and `S3`. `S1` is separated and rapidly decaying. `S2` uses the quantitative smooth reflection theorem and the Heath--Brown difference-set mean square. `S3` uses approximate-energy moments, localization, affine descent, refined spacing, and the GCD/energy estimates of Section 11. Sections 3 and 12 assemble these estimates; classical large-value bounds cover low-`V`, high-`V`, near-height, and bounded-length complements.

The conceptual burden is concentrated in Poisson/reflection, the `S2` mean-square step, the affine `S3` descent, and the Section 11 energy theorem. Matrix algebra and dyadic partitions are substantial formal bookkeeping. The sharp-to-smooth source entry and the final return to the physical source polynomial are the two most dangerous semantic bridges.

### 5.4 Large values to zero density

Section 13.1 builds a mollified detector at each zero, removes the real-part displacement, extracts separated ordinates, raises a polynomial to a bounded power `k`, and selects a dyadic block. The choice of `k` places the powered logarithmic scale in the admissible range. Large-values handles one case; Montgomery mean value handles the complementary long scale. All coefficient, logarithmic, harmonic, displacement, multiplicity, and finite-power losses are assigned to a single positive epsilon budget.

This proves `15(1-σ)/(3+5σ)` for `σ≥7/10`. Comparing exponents with Ingham at the split `σ=7/10` gives `30(1-σ)/13` on the full interval `1/2≤σ≤1`.

## 6. Dependency overview

```text
Mathlib + pinned PNT analytic infrastructure
  -> zero count with analytic multiplicity
  -> #15 finite detector/dichotomy -> Ingham and Huxley
  -> #18 contour reduction -> smooth AFE + diagonal + DFI off-diagonal
       -> native twisted-fourth-moment input bound
  -> #19 sharp-source localization -> matrix/Poisson -> S1/S2/S3 -> energy
       -> Guth--Maynard large-values theorem
  -> Section 13.1 transfer consumes #15/#18/#19 inputs
       -> Guth--Maynard zero density
  -> Ingham + Guth--Maynard exponent comparison
       -> combined exponent 30(1-σ)/13
```

The machine-readable dependency view is `Proof Architecture.md`. It is a project-maintained map, not a community-canonical proof organization.

## 7. Ten semantically dangerous bridges

1. **Zero multiplicity:** proving the finite sum uses analytic order and survives conjugation, rather than counting distinct points.
2. **Closed rectangle conventions:** reconciling `[T,2T]`, `[-T,T]`, and paper endpoint conventions without double-counting errors.
3. **`T^{o(1)}` semantics:** quantifier order for `ε`, constants, thresholds, and external parameters.
4. **Source polynomial entry:** the exact three-piece sharp-to-smooth identity and common subfamily selection before matrix analysis.
5. **Sign normalization:** `n^{it}` versus `n^{-it}` and the coefficient phase twist used under translations.
6. **Type-I physical scale:** the equality connecting `τ=log_N T` to the actual `N,T`, followed by complete endpoint routing.
7. **Finite powering:** choosing a positive bounded `k`, handling floors/ceilings/`Nat.clog`, and absorbing coefficient and harmonic losses.
8. **DFI shift sign:** converting negative shifts by coordinate swap while preserving box support and the error scale.
9. **Sharp/smooth fourth moment:** showing the actual nonnegative sharp mollified moment is bounded by the smooth moment assembled from the AFE and DFI estimates.
10. **Conditional-to-native transfer:** verifying that the final theorem supplies each of the ten genuine upstream inputs and never assumes a disguised density conclusion.

## 8. Known limitations and external obligations

- No independent expert has signed off on the source-to-Lean correspondence.
- The prose exposition has not undergone journal refereeing or specialist copy-editing.
- Bibliographic page/equation mappings are stable for the cited versions; a later source edition may renumber them.
- The audit checks declared dependencies, not naturalness of definitions or mathematical importance.
- The formalization is large and sometimes proves strengthened technical interfaces. External reviewers should confirm that strengthening did not alter a source consumer's intended domain.
- The canonical verifier is a PowerShell script used by local Windows runs and available to the optional Linux CI mirror. The batch file is only a Windows convenience wrapper; a PowerShell 7 runtime is still required for the canonical verifier.
- Upstreaming reusable lemmas to Mathlib/PNT and refactoring toward community-standard APIs remain future canonicalization work.
- Open external gates: expert exposition review, independent semantic review, public preprint decision, peer-reviewed publication, and eventual canonicalization.

## 9. Reproduction from a fresh clone

1. Clone the repository and enter the `Riemann Zeta` directory.
2. Install `elan`; allow it to install the version in `lean-toolchain` (`v4.30.0`).
3. Confirm that `lakefile.toml` pins Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` and PNT+ revision `4ecb950126c4290293c5662dfe0e884123171df5`.
4. On any supported platform with PowerShell 7 run:

   ```powershell
   pwsh -NoProfile -File scripts/verify_release.ps1 -Mode release
   ```

   On Windows, `cmd /c run_lake_build.bat --no-pause` runs the same verifier in development mode.
5. Release mode must report a clean tree. Preserve the emitted `logs/foundation_freeze_*.log` and matching JSON manifest. A valid PASS requires every classification, build, warning, dependency, exact-contract, output, linter, and prohibited-proof gate to pass.
6. Independently run `lake env lean RiemannZeta/Audit.lean` and inspect the five publication-contract `#print axioms` lines.
7. Run the repository scans listed in `AGENTS.md`; do not rely only on `lake build`. If optional hosted CI succeeds, inspect its SHA-named artifact as supplemental evidence rather than substituting it for the local verifier or semantic review.

Reproduction proves acceptance of the checked declarations in that environment. It is not a substitute for reviewing this crosswalk or the cited mathematics.

## 10. Independent checking instructions

For each public theorem:

1. Locate its declaration with `rg -n "theorem <name>" RiemannZeta`.
2. Unfold its proposition definitions (`N`, `zeroCountRect`, `EpsilonPowerBound`, and the named density proposition).
3. Read the proof body far enough to identify the actual upstream consumer; do not stop at the final one-line specialization.
4. Search the upstream theorem name through the import graph and confirm the source-facing object is supplied.
5. Add or inspect `#print axioms Fully.Qualified.Name` in `Audit.lean`.
6. Compare endpoints, signs, coefficient bounds, multiplicity, and quantifier order against the cited paper version.
7. Run the full principal runner and record the exact exit code and log, including warnings.
8. Report semantic and kernel verdicts separately.

## 11. Expert talk outline (50 minutes)

1. **0--5 min: Claim discipline.** State the five density theorems, the exact zero-count convention, the runner's limited meaning, and the uncompleted external-review gates.
2. **5--10 min: Formal asymptotics.** Unfold `EpsilonPowerBound`; explain constant/threshold dependencies and closed-rectangle analytic multiplicity.
3. **10--18 min: Classical engine (#15).** Detector identity, three-way dichotomy, representative ordinates, Type-I scale routing, Type-II powering, endpoint certificates, and positive-to-symmetric slabs.
4. **18--28 min: Type-II contour and fourth moment (#18).** Appendix C contour shift, Gamma tails, smooth zeta-square AFE, diagonal, DFI shifted divisor estimate, Hughes--Young consumer. Explicitly say the final theorem is an upper-bound specialization, not the full Hughes--Young asymptotic.
5. **28--41 min: Large values (#19).** Sharp-to-smooth localization; sampling matrix; first/cubic traces; Poisson; `S1/S2/S3`; reflection; Heath--Brown; affine descent and energy; complementary ranges.
6. **41--47 min: Section 13.1.** Beta removal, separated extraction, finite `k`, block selection, large-values/mean-value split, Huxley high range, and epsilon budget.
7. **47--50 min: Final exponent and audit.** Branch at `7/10`, exponent comparisons, the five final declarations, transitive axioms, reproduction, and the external work still open.

This outline is preparation for Tao's “talk test”; it is not evidence that the author has passed such a test before independent experts.

## 12. Hostile-review questions

1. Does `zeroCountRect` count a boundary zero twice under dyadic decomposition, and where is the inequality that prevents this from invalidating the bound?
2. Why does analytic vanishing order agree after conjugation for the function actually used by Mathlib?
3. Which parameters may the Big-O constant in `EpsilonPowerBound` depend on?
4. Where is the exact identity connecting the physical scale `N,T` to `τ`, rather than merely assuming an exponent inequality?
5. Which theorem destructs the real zero/Type-I/Type-II output, and where does analytic multiplicity re-enter?
6. Why is the powered Type-II coefficient sequence bounded after normalization, including its actual cutoff `X`?
7. What exactly is assumed by `EndpointScaleCertificate`, and why is it narrower than the density conclusion?
8. Where does the sharp source Dirichlet polynomial enter the Guth--Maynard matrix chain?
9. Does the reflection theorem sum all nonzero integer frequencies or only a finite truncation?
10. Where is the `T₀^{-1/2}` factor proved uniformly, and how is the omitted tail summed to `T^{-100}`?
11. Which DFI hypotheses remain visible in the public localized theorem?
12. How are negative DFI shifts reduced to positive shifts without silently assuming symmetry of the test weight?
13. Why does `twistedZetaFourthMoment_native` not amount to the full Hughes--Young Theorem 1.1?
14. What is the exact sharp-to-smooth inequality for the mollified fourth moment?
15. Which proof term supplies each of the ten premises of `conditionalZeroDensityTransfer`?
16. At `σ=7/10`, which branch supplies the bound, and are the exponent inequalities directionally correct?
17. What does `#print axioms` fail to tell us about semantic fidelity?
18. Which retained Lean files are outside the root graph, and how does the runner cover them?
19. What evidence would be required before calling this work peer reviewed?
20. What refactoring or independent adoption would justify calling the formalization canonicalized?

## 13. Attribution and stable sources

- L. Guth and J. Maynard, “New large value estimates for Dirichlet polynomials,” *Annals of Mathematics* 203 (2026), 623--675. [DOI](https://doi.org/10.4007/annals.2026.203.2.6), [arXiv v2](https://arxiv.org/html/2405.20552v2).
- C. P. Hughes and M. P. Young, “The twisted fourth moment of the Riemann zeta function,” *J. Reine Angew. Math.* 641 (2010), 203--236. [arXiv](https://arxiv.org/abs/0709.2345).
- W. Duke, J. B. Friedlander, and H. Iwaniec, “A quadratic divisor problem,” *Inventiones Mathematicae* 115 (1994), 209--217. [DOI](https://doi.org/10.1007/BF01231758), [author-hosted PDF](https://www.math.ucla.edu/~wdduke/preprints/quadraticdiv.pdf).
- D. R. Heath-Brown, “A large values estimate for Dirichlet polynomials,” *J. London Math. Soc.* (2) 20 (1979), no. 1, 8--18. [DOI](https://doi.org/10.1112/jlms/s2-20.1.8). This is the `[HB]` source cited by Guth--Maynard for the difference-set double sum; the earlier fourth-moment attribution was incorrect.
- J. Maynard and K. Pratt, “Half-isolated zeros and zero-density estimates,” *International Mathematics Research Notices* 2024 (2024), no. 19, 12978--13014. [DOI](https://doi.org/10.1093/imrn/rnae191), [arXiv](https://arxiv.org/abs/2206.11729).
- ANTEDB/Expdb at commit [`2b1aea3de263996c4da3042c115126bff601c618`](https://github.com/teorth/expdb/tree/2b1aea3de263996c4da3042c115126bff601c618). Stable labels used by this project are `thm:ingham_zero_density2`, `huxley-bound`, `guth-maynard-density`, `reflect`, `hb-double`, `guth-maynard-lvt`, and `huxley-lv`; bare historical “Lemma 11.5/11.10” references are not used as frozen identifiers.
- T. Tao, “Mathematics in the age of AI,” arXiv:2608.16753 (2026), especially the separation of verification, exposition, publication, community digestion, and canonicalization. [arXiv](https://arxiv.org/abs/2608.16753).
- T. Tao, “What is good mathematics?”, arXiv:math/0702396. [arXiv](https://arxiv.org/abs/math/0702396).
- [Leiden Declaration on AI and Mathematics](https://leidendeclaration.ai/), archived at [Zenodo](https://doi.org/10.5281/zenodo.20302944).
- D. Loeffler and M. Stoll, “Formalizing zeta and L-functions in Lean,” arXiv:2503.00959. This describes relevant upstream formal infrastructure; it is not credited for project-specific density arguments.

Full source/version details and convention decisions are in `verification/SOURCE_FREEZE.md`. Remaining historical-source questions, including the preferred primary Huxley edition, are explicit external-review obligations rather than invitations to invent attribution.

## 14. Tool and computational-resource disclosure

The Lean development, proof search, refactoring, repository audits, and documentation were assisted by language-model coding agents, including OpenAI Codex and earlier Antigravity/Gemini sessions. AI assistance included generating candidate Lean terms, translating paper arguments into formal sublemmas, locating APIs and sources, reorganizing proof chains, drafting exposition, and identifying consistency defects. Generated material was accepted only when elaborated by Lean and passed the project checks; that does not make the AI output semantically self-validating.

Lean 4 and Mathlib perform formal elaboration and kernel checking. The project uses Lean `v4.30.0`, Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`, and pinned PNT+ revision `4ecb950126c4290293c5662dfe0e884123171df5`. The canonical verifier requires PowerShell; the Windows wrapper invokes it locally and the optional Linux workflow attempts to mirror it. No AI system is listed as an author. S. McColm, as human project owner, retains responsibility for semantic fidelity, correct attribution, release decisions, and any publication claim.

## 15. External digestion ledger

| Gate | Status | Evidence required to close it |
|---|---|---|
| Internal kernel and integrity verification | Project-complete for the recorded revision | Reproducible runner PASS, zero warnings, clean transitive audit and scans. |
| Internal semantic audit and review packet | Complete for this documentation revision | This crosswalk, synchronized claims, and verified theorem consumers. |
| Expert exposition review | **Open** | A qualified independent reader can reconstruct and challenge the proof from the exposition and code. |
| Independent source-to-Lean semantic review | **Open** | Written review of statements, conventions, and dangerous bridges by independent experts. |
| Public preprint | **Open / not authorized by this task** | Human-approved manuscript deposited in a stable public archive. |
| Peer-reviewed publication | **Open** | External refereeing and formal acceptance. |
| Canonicalization | **Open** | Community digestion, natural refactoring, reuse, and adoption into standard references/libraries. |
