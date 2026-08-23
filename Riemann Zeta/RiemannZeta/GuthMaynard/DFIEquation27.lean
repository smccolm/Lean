import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.DFIEquation26
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon
import Mathlib.Analysis.PSeries

/-!
# DFI equation (27): complex delta approximation for the main branch

The source main kernel is complex-valued, whereas equation (18) was first
proved for real test functions.  This file supplies the exact real/imaginary
projection bridge and then recombines the two estimates.  It is the analytic
input for evaluating the double-main term in equation (27).
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology

namespace RiemannZeta.GuthMaynard

/-- Iterated real derivatives commute with real projection from `ℂ`. -/
theorem iteratedDeriv_complex_re
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x).re) =
      fun x => (iteratedDeriv k g x).re := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hkTop : (k : WithTop ℕ∞) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)
      have hd : HasDerivAt (iteratedDeriv k g)
          (deriv (iteratedDeriv k g) x) x :=
        (hg.differentiable_iteratedDeriv k hkTop).differentiableAt.hasDerivAt
      simpa [Function.comp_def] using
        (Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt).hasDerivAt.deriv

/-- Iterated real derivatives commute with imaginary projection from `ℂ`. -/
theorem iteratedDeriv_complex_im
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x).im) =
      fun x => (iteratedDeriv k g x).im := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hkTop : (k : WithTop ℕ∞) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)
      have hd : HasDerivAt (iteratedDeriv k g)
          (deriv (iteratedDeriv k g) x) x :=
        (hg.differentiable_iteratedDeriv k hkTop).differentiableAt.hasDerivAt
      simpa [Function.comp_def] using
        (Complex.imCLM.hasFDerivAt.comp x hd.hasFDerivAt).hasDerivAt.deriv

theorem contDiff_complex_re
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (g x).re) :=
  Complex.reCLM.contDiff.comp hg

theorem contDiff_complex_im
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (g x).im) :=
  Complex.imCLM.contDiff.comp hg

theorem hasCompactSupport_complex_re
    {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x).re) :=
  hg.comp_left rfl

theorem hasCompactSupport_complex_im
    {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x).im) :=
  hg.comp_left rfl

/-- Complex-valued form of the left side of DFI equation (12). -/
noncomputable def dfiEquation12LeftComplex {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∫ u : ℝ, g u * dfiDeltaKernel w q u

/-- Real projection of the complex equation-(12) integral. -/
theorem dfiEquation12LeftComplex_re
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (dfiEquation12LeftComplex w q g).re =
      dfiEquation12Left w q (fun u => (g u).re) := by
  have hδ : Continuous (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    (Complex.ofRealCLM.continuous.comp (contDiff_dfiDeltaKernel w q hq).continuous)
  have hint : Integrable (fun u : ℝ => g u * (dfiDeltaKernel w q u : ℂ)) :=
    (hg.continuous.mul hδ).integrable_of_hasCompactSupport hgc.mul_right
  unfold dfiEquation12LeftComplex dfiEquation12Left
  calc
    (∫ u : ℝ, g u * (dfiDeltaKernel w q u : ℂ)).re =
        ∫ u : ℝ, (g u * (dfiDeltaKernel w q u : ℂ)).re :=
      (integral_re hint).symm
    _ = ∫ u : ℝ, (g u).re * dfiDeltaKernel w q u := by
      congr 1
      funext u
      simp

/-- Imaginary projection of the complex equation-(12) integral. -/
theorem dfiEquation12LeftComplex_im
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (dfiEquation12LeftComplex w q g).im =
      dfiEquation12Left w q (fun u => (g u).im) := by
  have hδ : Continuous (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) :=
    (Complex.ofRealCLM.continuous.comp (contDiff_dfiDeltaKernel w q hq).continuous)
  have hint : Integrable (fun u : ℝ => g u * (dfiDeltaKernel w q u : ℂ)) :=
    (hg.continuous.mul hδ).integrable_of_hasCompactSupport hgc.mul_right
  unfold dfiEquation12LeftComplex dfiEquation12Left
  calc
    (∫ u : ℝ, g u * (dfiDeltaKernel w q u : ℂ)).im =
        ∫ u : ℝ, (g u * (dfiDeltaKernel w q u : ℂ)).im :=
      (integral_im hint).symm
    _ = ∫ u : ℝ, (g u).im * dfiDeltaKernel w q u := by
      congr 1
      funext u
      simp

theorem integral_abs_re_le_integral_norm
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ u : ℝ, |(g u).re|) ≤ ∫ u : ℝ, ‖g u‖ := by
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  exact integral_mono hgint.re.abs hgint.norm
    (fun u => Complex.abs_re_le_norm (g u))

theorem integral_abs_im_le_integral_norm
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ u : ℝ, |(g u).im|) ≤ ∫ u : ℝ, ‖g u‖ := by
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  exact integral_mono hgint.im.abs hgint.norm
    (fun u => Complex.abs_im_le_norm (g u))

/-- Complex form of DFI equation (18), with the same source scales and one
explicit constant obtained by combining the real and imaginary estimates. -/
theorem dfiEquation18_complex
    {Q : ℝ} (w : DFIDeltaWeight Q) (U j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q → ∀ g : ℝ → ℂ,
        ContDiff ℝ ∞ g → HasCompactSupport g →
        tsupport g ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) →
      ‖dfiEquation12LeftComplex w q g - g 0‖ ≤
        C * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ, ‖iteratedDeriv j g u‖) := by
  obtain ⟨C₀, hC₀, hreal⟩ := dfiEquation18 w U j hj
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro q hq g hg hgc hsupp
  let gr : ℝ → ℝ := fun u => (g u).re
  let gi : ℝ → ℝ := fun u => (g u).im
  have hgr : ContDiff ℝ ∞ gr := contDiff_complex_re hg
  have hgi : ContDiff ℝ ∞ gi := contDiff_complex_im hg
  have hgrc : HasCompactSupport gr := hasCompactSupport_complex_re hgc
  have hgic : HasCompactSupport gi := hasCompactSupport_complex_im hgc
  have hgrsupp : tsupport gr ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gr, hzero])
  have hgisupp : tsupport gi ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gi, hzero])
  have hr := hreal q hq gr hgr hgrc hgrsupp
  have hi := hreal q hq gi hgi hgic hgisupp
  let E : ℝ :=
    (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
      (q : ℝ) ^ j * Q ^ (j - 1) *
        ∫ u : ℝ, ‖iteratedDeriv j g u‖
  have hderivSmooth : ContDiff ℝ ∞ (iteratedDeriv j g) :=
    ContDiff.contDiff_iteratedDeriv_top hg j
  have hderivCompact : HasCompactSupport (iteratedDeriv j g) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k g) := by
      intro k
      induction k with
      | zero => simpa using hgc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have hmassRe : (∫ u : ℝ, |gr u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_re_le_integral_norm g hg hgc
  have hmassIm : (∫ u : ℝ, |gi u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_im_le_integral_norm g hg hgc
  have hderivRe : (∫ u : ℝ, |iteratedDeriv j gr u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_re g hg j]
    exact integral_abs_re_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hderivIm : (∫ u : ℝ, |iteratedDeriv j gi u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_im g hg j]
    exact integral_abs_im_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hqpow : 0 ≤ (q : ℝ) ^ j := by positivity
  have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)
  have hQpow : 0 ≤ Q ^ (j - 1) := pow_nonneg w.Q_pos.le _
  have hEr :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gr u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gr u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassRe (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivRe (mul_nonneg hqpow hQpow))
  have hEi :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gi u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gi u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassIm (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivIm (mul_nonneg hqpow hQpow))
  let z := dfiEquation12LeftComplex w q g - g 0
  have hzre : z.re = dfiEquation12Left w q gr - gr 0 := by
    dsimp [z, gr]
    rw [dfiEquation12LeftComplex_re w q hq g hg hgc]
  have hzim : z.im = dfiEquation12Left w q gi - gi 0 := by
    dsimp [z, gi]
    rw [dfiEquation12LeftComplex_im w q hq g hg hgc]
  have hre : |z.re| ≤ C₀ * E := by
    rw [hzre]
    exact hr.trans (mul_le_mul_of_nonneg_left hEr hC₀.le)
  have him : |z.im| ≤ C₀ * E := by
    rw [hzim]
    exact hi.trans (mul_le_mul_of_nonneg_left hEi hC₀.le)
  change ‖z‖ ≤ (2 * C₀) * E
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ C₀ * E + C₀ * E := add_le_add hre him
    _ = (2 * C₀) * E := by ring

/-- The profile-controlled real equation-(18) constant. -/
noncomputable def dfiEquation18ProfileConstant
    (D E : ℕ → ℝ) (j : ℕ) (Cpsi CpsiSucc : ℝ) : ℝ :=
  (4 * CpsiSucc * D (j + 1)) * (2 + 2 * Real.pi) +
    4 * Cpsi * E j + Cpsi * (4 * D 0 * 2 ^ j)

theorem dfiEquation18ProfileConstant_pos
    {D E : ℕ → ℝ} (hD : ∀ k, 0 < D k) (hE : ∀ k, 0 < E k)
    (j : ℕ) {Cpsi CpsiSucc : ℝ}
    (hCpsi : 0 < Cpsi) (hCpsiSucc : 0 < CpsiSucc) :
    0 < dfiEquation18ProfileConstant D E j Cpsi CpsiSucc := by
  unfold dfiEquation18ProfileConstant
  have hpi : 0 < 2 + 2 * Real.pi := by positivity
  have hDj : 0 < D (j + 1) := hD _
  have hEj : 0 < E j := hE _
  have hD0 : 0 < D 0 := hD _
  positivity

/-- Complex DFI equation (18) with the cutoff constants fixed by profiles
before the physical scale. -/
theorem dfiEquation18_complex_of_profiles
    {Q : ℝ} {w : DFIDeltaWeight Q} {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    (U j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc) :
    ∀ (q : ℕ), 0 < q → ∀ g : ℝ → ℂ,
      ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) →
      ‖dfiEquation12LeftComplex w q g - g 0‖ ≤
        (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
          ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
            (q : ℝ) ^ j * Q ^ (j - 1) *
              ∫ u : ℝ, ‖iteratedDeriv j g u‖) := by
  intro q hq g hg hgc hsupp
  let gr : ℝ → ℝ := fun u => (g u).re
  let gi : ℝ → ℝ := fun u => (g u).im
  have hgr : ContDiff ℝ ∞ gr := contDiff_complex_re hg
  have hgi : ContDiff ℝ ∞ gi := contDiff_complex_im hg
  have hgrc : HasCompactSupport gr := hasCompactSupport_complex_re hgc
  have hgic : HasCompactSupport gi := hasCompactSupport_complex_im hgc
  have hgrsupp : tsupport gr ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gr, hzero])
  have hgisupp : tsupport gi ⊆ Set.Icc (-(U : ℝ)) (U : ℝ) := by
    apply (closure_mono ?_).trans hsupp
    intro u hu hzero
    exact hu (by simp [gi, hzero])
  have hr := dfiEquation18_of_profiles hD hEprofile U j hj
    hCpsi hpsi hCpsiSucc hpsiSucc q hq gr hgr hgrc hgrsupp
  have hi := dfiEquation18_of_profiles hD hEprofile U j hj
    hCpsi hpsi hCpsiSucc hpsiSucc q hq gi hgi hgic hgisupp
  let E : ℝ :=
    (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
      (q : ℝ) ^ j * Q ^ (j - 1) *
        ∫ u : ℝ, ‖iteratedDeriv j g u‖
  have hderivSmooth : ContDiff ℝ ∞ (iteratedDeriv j g) :=
    ContDiff.contDiff_iteratedDeriv_top hg j
  have hderivCompact : HasCompactSupport (iteratedDeriv j g) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k g) := by
      intro k
      induction k with
      | zero => simpa using hgc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  have hmassRe : (∫ u : ℝ, |gr u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_re_le_integral_norm g hg hgc
  have hmassIm : (∫ u : ℝ, |gi u|) ≤ ∫ u : ℝ, ‖g u‖ :=
    integral_abs_im_le_integral_norm g hg hgc
  have hderivRe : (∫ u : ℝ, |iteratedDeriv j gr u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_re g hg j]
    exact integral_abs_re_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hderivIm : (∫ u : ℝ, |iteratedDeriv j gi u|) ≤
      ∫ u : ℝ, ‖iteratedDeriv j g u‖ := by
    rw [iteratedDeriv_complex_im g hg j]
    exact integral_abs_im_le_integral_norm
      (iteratedDeriv j g) hderivSmooth hderivCompact
  have hqpow : 0 ≤ (q : ℝ) ^ j := by positivity
  have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)
  have hQpow : 0 ≤ Q ^ (j - 1) := pow_nonneg w.Q_pos.le _
  have hEr :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gr u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gr u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassRe (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivRe (mul_nonneg hqpow hQpow))
  have hEi :
      (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, |gi u|) +
        (q : ℝ) ^ j * Q ^ (j - 1) *
          (∫ u : ℝ, |iteratedDeriv j gi u|) ≤ E := by
    dsimp [E]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmassIm (mul_nonneg hqpow hQinv))
      (mul_le_mul_of_nonneg_left hderivIm (mul_nonneg hqpow hQpow))
  let C₀ := dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc
  have hC₀ : 0 < C₀ := dfiEquation18ProfileConstant_pos
    hD.positive hEprofile.positive j hCpsi hCpsiSucc
  let z : ℂ := dfiEquation12LeftComplex w q g - g 0
  have hzre : z.re = dfiEquation12Left w q gr - gr 0 := by
    dsimp [z, gr]
    rw [dfiEquation12LeftComplex_re w q hq g hg hgc]
  have hzim : z.im = dfiEquation12Left w q gi - gi 0 := by
    dsimp [z, gi]
    rw [dfiEquation12LeftComplex_im w q hq g hg hgc]
  have hre : |z.re| ≤ C₀ * E := by
    rw [hzre]
    exact hr.trans (mul_le_mul_of_nonneg_left hEr hC₀.le)
  have him : |z.im| ≤ C₀ * E := by
    rw [hzim]
    exact hi.trans (mul_le_mul_of_nonneg_left hEi hC₀.le)
  change ‖z‖ ≤ (2 * C₀) * E
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ C₀ * E + C₀ * E := add_le_add hre him
    _ = (2 * C₀) * E := by ring

/-- The scale expression on the right of complex DFI equation (18). -/
noncomputable def dfiEquation18ComplexMajorant
    {Q : ℝ} (q j : ℕ) (g : ℝ → ℂ) : ℝ :=
  (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ * (∫ u : ℝ, ‖g u‖) +
    (q : ℝ) ^ j * Q ^ (j - 1) *
      ∫ u : ℝ, ‖iteratedDeriv j g u‖

/-- Uniform equation-(18) estimates may be integrated over a family of test
functions.  This is the analytic quantifier bridge used in DFI equation
(27); the three integrability premises are later discharged from the source
dyadic support and equation-(21) derivative bounds. -/
theorem dfiEquation18_complex_family_integral
    {Q : ℝ} (w : DFIDeltaWeight Q) (U j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ), 0 < q → ∀ (g : ℝ → ℝ → ℂ),
      (∀ x, ContDiff ℝ ∞ (g x)) →
      (∀ x, HasCompactSupport (g x)) →
      (∀ x, tsupport (g x) ⊆ Set.Icc (-(U : ℝ)) (U : ℝ)) →
      Integrable (fun x => dfiEquation12LeftComplex w q (g x)) →
      Integrable (fun x => g x 0) →
      Integrable (fun x => dfiEquation18ComplexMajorant
        (Q := Q) q j (g x)) →
      ‖(∫ x : ℝ, dfiEquation12LeftComplex w q (g x)) -
          ∫ x : ℝ, g x 0‖ ≤
        C * ∫ x : ℝ,
          dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
  obtain ⟨C, hC, hbound⟩ := dfiEquation18_complex w U j hj
  refine ⟨C, hC, ?_⟩
  intro q hq g hsmooth hcompact hsupp hleft hcenter hmajor
  have hdiff : Integrable (fun x =>
      dfiEquation12LeftComplex w q (g x) - g x 0) := hleft.sub hcenter
  have hpoint : ∀ x : ℝ,
      ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
    intro x
    simpa [dfiEquation18ComplexMajorant] using
      hbound q hq (g x) (hsmooth x) (hcompact x) (hsupp x)
  rw [← MeasureTheory.integral_sub hleft hcenter]
  calc
    ‖∫ x : ℝ, dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        ∫ x : ℝ, ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ,
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      exact MeasureTheory.integral_mono hdiff.norm (hmajor.const_mul C) hpoint
    _ = C * ∫ x : ℝ,
        dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      rw [MeasureTheory.integral_const_mul]

/-- Family-integrated complex equation (18) with one profile-controlled
The constant fixed before the physical scale. -/
theorem dfiEquation18_complex_family_integral_of_profiles
    {Q : ℝ} {w : DFIDeltaWeight Q} {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    (U j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc)
    (q : ℕ) (hq : 0 < q) (g : ℝ → ℝ → ℂ)
    (hsmooth : ∀ x, ContDiff ℝ ∞ (g x))
    (hcompact : ∀ x, HasCompactSupport (g x))
    (hsupp : ∀ x, tsupport (g x) ⊆ Set.Icc (-(U : ℝ)) (U : ℝ))
    (hleft : Integrable (fun x => dfiEquation12LeftComplex w q (g x)))
    (hcenter : Integrable (fun x => g x 0))
    (hmajor : Integrable (fun x => dfiEquation18ComplexMajorant
      (Q := Q) q j (g x))) :
    ‖(∫ x : ℝ, dfiEquation12LeftComplex w q (g x)) -
        ∫ x : ℝ, g x 0‖ ≤
      (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
        ∫ x : ℝ, dfiEquation18ComplexMajorant
          (Q := Q) q j (g x) := by
  let C := 2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc
  have hC : 0 < C := mul_pos two_pos
    (dfiEquation18ProfileConstant_pos hD.positive hEprofile.positive
      j hCpsi hCpsiSucc)
  have hdiff : Integrable (fun x =>
      dfiEquation12LeftComplex w q (g x) - g x 0) := hleft.sub hcenter
  have hpoint : ∀ x : ℝ,
      ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
    intro x
    simpa only [C, dfiEquation18ComplexMajorant] using
      dfiEquation18_complex_of_profiles hD hEprofile U j hj
        hCpsi hpsi hCpsiSucc hpsiSucc q hq (g x)
          (hsmooth x) (hcompact x) (hsupp x)
  rw [← MeasureTheory.integral_sub hleft hcenter]
  calc
    ‖∫ x : ℝ, dfiEquation12LeftComplex w q (g x) - g x 0‖ ≤
        ∫ x : ℝ, ‖dfiEquation12LeftComplex w q (g x) - g x 0‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ,
        C * dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      exact MeasureTheory.integral_mono hdiff.norm (hmajor.const_mul C) hpoint
    _ = C * ∫ x : ℝ,
        dfiEquation18ComplexMajorant (Q := Q) q j (g x) := by
      rw [MeasureTheory.integral_const_mul]

/-- The DFI delta kernel is even in its displacement variable.  This is the
sign correction needed when the change of variables in source equation (27)
is written as `y = x - h + u`. -/
theorem dfiDeltaKernel_neg
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (u : ℝ) :
    dfiDeltaKernel w q (-u) = dfiDeltaKernel w q u := by
  unfold dfiDeltaKernel dfiDeltaRadius
  rw [abs_neg]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (-u) / (q * r : ℕ) = -(u / (q * r : ℕ)) by ring]
  rw [w.even]

/-- The one-dimensional test function occurring after the exact affine
change of variables in DFI equation (27). -/
noncomputable def dfiEquation27Slice
    (C : ℝ → ℝ → ℂ) (h x u : ℝ) : ℂ :=
  C x (x - h + u)

/-- Exact inner-integral change of variables in DFI equation (27). -/
theorem dfiEquation27_inner_change_variables
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (C : ℝ → ℝ → ℂ) (h x : ℝ) :
    (∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) =
      dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) := by
  let G : ℝ → ℂ := fun y =>
    C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)
  have hshift : (∫ u : ℝ, G (u + (x - h))) = ∫ y : ℝ, G y :=
    integral_add_right_eq_self G (x - h)
  rw [← hshift]
  unfold dfiEquation12LeftComplex dfiEquation27Slice G
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [show x - (u + (x - h)) - h = -u by ring, dfiDeltaKernel_neg]
  congr 2
  ring

/-- Exact two-dimensional version of the change of variables displayed at
the start of DFI equation (27). -/
theorem dfiEquation27_double_change_variables
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (C : ℝ → ℝ → ℂ) (h : ℝ) :
    (∫ x : ℝ, ∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) =
      ∫ x : ℝ,
        dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  exact dfiEquation27_inner_change_variables w q C h x

/-- DFI equation (18), applied to the literal equation-(27) affine slice.
This theorem is the quantitative pointwise input to the subsequent
integration in `x`. -/
theorem dfiEquation27_slice_approximation
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (C : ℝ → ℝ → ℂ) (h x : ℝ)
    (U j : ℕ)
    (hsmooth : ContDiff ℝ ∞ (dfiEquation27Slice C h x))
    (hcompact : HasCompactSupport (dfiEquation27Slice C h x))
    (hsupp : tsupport (dfiEquation27Slice C h x) ⊆
      Set.Icc (-(U : ℝ)) (U : ℝ))
    (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ‖dfiEquation12LeftComplex w q (dfiEquation27Slice C h x) -
          C x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ, ‖dfiEquation27Slice C h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j (dfiEquation27Slice C h x) u‖) := by
  obtain ⟨K, hK, hbound⟩ := dfiEquation18_complex w U j hj
  refine ⟨K, hK, ?_⟩
  simpa [dfiEquation27Slice] using
    hbound q hq (dfiEquation27Slice C h x) hsmooth hcompact hsupp

/-- The physical-variable logarithmic factor produced by a Voronoi main
term after the substitution `x = a m`.  Here `qred` is the reduced
denominator `q / gcd(a,q)`. -/
noncomputable def dfiEquation27LogFactor
    (a qred : ℕ) (x : ℝ) : ℂ :=
  (Real.log x : ℂ) - Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qred : ℂ)

/-- A completely explicit pointwise majorant for the two logarithms in the
DFI main kernel.  Keeping absolute values here makes the statement valid at
all inputs; source positivity later removes them on the dyadic support. -/
theorem norm_dfiEquation27LogFactor_le
    (a qred : ℕ) (x : ℝ) :
    ‖dfiEquation27LogFactor a qred x‖ ≤
      |Real.log x| + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qred| := by
  unfold dfiEquation27LogFactor
  have haLog : Complex.log (a : ℂ) = (Real.log a : ℂ) :=
    Complex.natCast_log.symm
  have hqLog : Complex.log (qred : ℂ) = (Real.log qred : ℂ) :=
    Complex.natCast_log.symm
  rw [haLog, hqLog]
  calc
    ‖(Real.log x : ℂ) - (Real.log a : ℂ) +
        2 * Real.eulerMascheroniConstant - 2 * (Real.log qred : ℂ)‖ ≤
        ‖(Real.log x : ℂ) - (Real.log a : ℂ) +
          2 * Real.eulerMascheroniConstant‖ +
          ‖2 * (Real.log qred : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(Real.log x : ℂ) - (Real.log a : ℂ)‖ +
          ‖(2 : ℂ) * (Real.eulerMascheroniConstant : ℂ)‖) +
          ‖(2 : ℂ) * (Real.log qred : ℂ)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖(Real.log x : ℂ)‖ + ‖(Real.log a : ℂ)‖) +
          ‖(2 : ℂ) * (Real.eulerMascheroniConstant : ℂ)‖) +
          ‖(2 : ℂ) * (Real.log qred : ℂ)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = |Real.log x| + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qred| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_ofNat]

/-- Every positive-order derivative of the real logarithm, viewed in
`ℂ`, is the expected signed inverse power.  This is the quantitative
distinction used in DFI equation (27): only the undifferentiated factor
retains a reduced-modulus logarithm. -/
theorem iteratedDeriv_ofReal_log_succ
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (n + 1) (fun y : ℝ => (Real.log y : ℂ)) x =
      ((((-1 : ℝ) ^ n * n.factorial * x ^ (-(n + 1 : ℕ) : ℤ)) : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero =>
      rw [show 0 + 1 = 1 by omega, iteratedDeriv_one]
      simpa using (Real.hasDerivAt_log hx.ne').ofReal_comp.deriv
  | succ n ih =>
      rw [show (n + 1) + 1 = (n + 1) + 1 by rfl, iteratedDeriv_succ]
      have heq : Set.EqOn
          (iteratedDeriv (n + 1) (fun y : ℝ => (Real.log y : ℂ)))
          (fun y : ℝ =>
            ((((-1 : ℝ) ^ n * n.factorial *
              y ^ (-(n + 1 : ℕ) : ℤ)) : ℝ) : ℂ))
          (Set.Ioi 0) := by
        intro y hy
        exact ih hy
      rw [heq.deriv isOpen_Ioi hx]
      have hpow : HasDerivAt
          (fun y : ℝ => y ^ (-(n + 1 : ℕ) : ℤ))
          ((-(n + 1 : ℕ) : ℤ) * x ^ (-(n + 1 : ℕ) - 1 : ℤ)) x :=
        hasDerivAt_zpow _ _ (Or.inl hx.ne')
      have hderiv :=
        ((hpow.const_mul ((-1 : ℝ) ^ n * n.factorial)).ofReal_comp).deriv
      rw [hderiv]
      push_cast
      norm_num [pow_succ, Nat.factorial_succ]
      ring

/-- On a positive dyadic range, every positive-order logarithmic
derivative is bounded at the localization scale. -/
theorem norm_iteratedDeriv_ofReal_log_succ_le
    (n : ℕ) {U x : ℝ} (hU : 0 < U) (hUx : U ≤ x) :
    ‖iteratedDeriv (n + 1) (fun y : ℝ => (Real.log y : ℂ)) x‖ ≤
      n.factorial * U⁻¹ ^ (n + 1) := by
  rw [iteratedDeriv_ofReal_log_succ n (hU.trans_le hUx)]
  have hinv : 0 ≤ x⁻¹ ∧ x⁻¹ ≤ U⁻¹ := by
    constructor
    · exact inv_nonneg.mpr (hU.trans_le hUx).le
    · simpa only [one_div] using one_div_le_one_div_of_le hU hUx
  rw [zpow_neg, zpow_natCast]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, Nat.cast_nonneg, abs_of_nonneg,
    abs_inv, abs_of_nonneg (hU.trans_le hUx).le]
  rw [← inv_pow]
  simp only [one_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv.1 hinv.2 _) (by positivity)

/-- Positive-order derivatives of the DFI logarithmic main-term factor do
not see either arithmetic constant. -/
theorem iteratedDeriv_dfiEquation27LogFactor_succ
    (a q : ℕ) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (dfiEquation27LogFactor a q) x =
      iteratedDeriv (n + 1) (fun y : ℝ => (Real.log y : ℂ)) x := by
  let c : ℂ := -Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (q : ℂ)
  have hfun : dfiEquation27LogFactor a q =
      fun y : ℝ => (Real.log y : ℂ) + c := by
    funext y
    simp only [dfiEquation27LogFactor, c]
    ring
  rw [hfun]
  have h := iteratedDeriv_const_add (𝕜 := ℝ) (F := ℂ)
    (f := fun y : ℝ => (Real.log y : ℂ)) (x := x)
    (n := n + 1) (by omega) c
  simpa only [add_comm] using h

/-- A single explicit expression bounds every derivative order of a DFI
logarithmic factor on its positive dyadic source interval. -/
theorem norm_iteratedDeriv_dfiEquation27LogFactor_le
    (a q s : ℕ) {Y U y : ℝ}
    (hY : 1 ≤ Y) (hU : 0 < U) (hUY : U ≤ Y)
    (hy : y ∈ Set.Icc Y (2 * Y)) :
    ‖iteratedDeriv s (dfiEquation27LogFactor a q) y‖ ≤
      s.factorial *
        (1 + Real.log (2 * Y) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
        U⁻¹ ^ s := by
  have hL0 : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith)
  have hL1 : 1 ≤ 1 + Real.log (2 * Y) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q| := by
    linarith [hL0, abs_nonneg (Real.log a),
      abs_nonneg Real.eulerMascheroniConstant, abs_nonneg (Real.log q)]
  cases s with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        one_mul, pow_zero, mul_one]
      exact (norm_dfiEquation27LogFactor_le a q y).trans (by
        have hyOne : 1 ≤ y := hY.trans hy.1
        have hyPos : 0 < y := zero_lt_one.trans_le hyOne
        have hylog : |Real.log y| ≤ Real.log (2 * Y) := by
          rw [abs_of_nonneg (Real.log_nonneg hyOne)]
          exact Real.log_le_log hyPos hy.2
        linarith [abs_nonneg (Real.log a),
          abs_nonneg Real.eulerMascheroniConstant, abs_nonneg (Real.log q)])
  | succ n =>
      rw [iteratedDeriv_dfiEquation27LogFactor_succ]
      have hbase := norm_iteratedDeriv_ofReal_log_succ_le n hU
        (hUY.trans hy.1)
      calc
        ‖iteratedDeriv (n + 1) (fun y : ℝ => (Real.log y : ℂ)) y‖ ≤
            n.factorial * U⁻¹ ^ (n + 1) := hbase
        _ ≤ (n + 1).factorial *
              (1 + Real.log (2 * Y) + |Real.log a| +
                2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
              U⁻¹ ^ (n + 1) := by
          have hfac : (n.factorial : ℝ) ≤ (n + 1).factorial := by
            exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 1)
          have hpow : 0 ≤ U⁻¹ ^ (n + 1) := by positivity
          exact mul_le_mul_of_nonneg_right
            (hfac.trans (le_mul_of_one_le_right (by positivity) hL1)) hpow

/-- The finite Leibniz coefficient appearing when one logarithmic main
term is differentiated together with the localized source weight. -/
noncomputable def dfiEquation27LogLeibnizConstant (j : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (j + 1), (j.choose s : ℝ) * s.factorial

theorem dfiEquation27LogLeibnizConstant_pos (j : ℕ) :
    0 < dfiEquation27LogLeibnizConstant j := by
  unfold dfiEquation27LogLeibnizConstant
  have hnonneg : ∀ s ∈ Finset.range (j + 1),
      0 ≤ (j.choose s : ℝ) * s.factorial := by
    intro s hs
    positivity
  have hmem : 0 ∈ Finset.range (j + 1) := by simp
  have hsingle := Finset.single_le_sum hnonneg hmem
  norm_num at hsingle ⊢
  exact lt_of_lt_of_le zero_lt_one hsingle

/-- On a positive dyadic source box the absolute logarithm is controlled by
the logarithm of the upper endpoint. -/
theorem abs_log_le_log_two_mul_of_mem_Icc
    {S x : ℝ} (hS : 1 ≤ S) (hx : x ∈ Set.Icc S (2 * S)) :
    |Real.log x| ≤ Real.log (2 * S) := by
  have hxOne : 1 ≤ x := hS.trans hx.1
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  rw [abs_of_nonneg (Real.log_nonneg hxOne)]
  exact Real.log_le_log hxPos hx.2

/-- Exact cancellation of the physical scaling logarithm against the
`-log a` term. -/
theorem dfiEquation27LogFactor_nat_mul
    (a qred : ℕ) (ha : 0 < a) (x : ℝ) (hx : 0 < x) :
    dfiEquation27LogFactor a qred ((a : ℝ) * x) =
      (Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (qred : ℂ) := by
  unfold dfiEquation27LogFactor
  rw [Real.log_mul (by exact_mod_cast ha.ne') hx.ne']
  rw [Complex.ofReal_add, Complex.natCast_log]
  ring

/-- The literal `C(x,y)` used in section 6 of DFI, with both changes of
scale from the divisor variables exposed. -/
noncomputable def dfiEquation27C
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  dfiEquation27LogFactor a qx x *
    dfiEquation27LogFactor b qy y * F x y

/-- Product majorant for the exact logarithmic kernel `C(x,y)` in source
equation (27). -/
theorem norm_dfiEquation27C_le
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    ‖dfiEquation27C a b qx qy F x y‖ ≤
      (|Real.log x| + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
        (|Real.log y| + |Real.log b| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
        ‖F x y‖ := by
  rw [dfiEquation27C, norm_mul, norm_mul]
  exact mul_le_mul
    (mul_le_mul (norm_dfiEquation27LogFactor_le a qx x)
      (norm_dfiEquation27LogFactor_le b qy y)
      (norm_nonneg _) (by positivity))
    le_rfl (norm_nonneg _) (by positivity)

/-- Equation (21) at order zero, combined with the dyadic support, gives a
source-uniform pointwise bound for the full logarithmic kernel in (27).
The displayed logarithmic factors retain every dependence on the arithmetic
scalings and reduced moduli. -/
theorem exists_norm_dfiEquation27C_source_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ) (x y : ℝ),
      ‖dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h) x y‖ ≤
        (Real.log (2 * X) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
        (Real.log (2 * Y) + |Real.log b| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    dfiEquation21_uniform_in_shift hf hbox hφ hscale 0 0
  refine ⟨C, hC, ?_⟩
  intro h a b qx qy x y
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith [hf.one_le_X])
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith [hf.one_le_Y])
  have hLX : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| := by
    positivity
  have hLY : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| := by
    positivity
  by_cases hF : dfiLocalizedWeight f φ h x y = 0
  · rw [dfiEquation27C, hF, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hLX hLY) hC.le
  · have hxy : (x, y) ∈ Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      support_uncurry_dfiLocalizedWeight_subset hbox hF
    have hxlog := abs_log_le_log_two_mul_of_mem_Icc hf.one_le_X hxy.1
    have hylog := abs_log_le_log_two_mul_of_mem_Icc hf.one_le_Y hxy.2
    have hFnorm : ‖dfiLocalizedWeight f φ h x y‖ ≤ C := by
      have hzero := (hbound h x y).2
      simpa using hzero
    calc
      ‖dfiEquation27C a b qx qy
          (dfiLocalizedWeight f φ h) x y‖ ≤
          (|Real.log x| + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (|Real.log y| + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          ‖dfiLocalizedWeight f φ h x y‖ :=
        norm_dfiEquation27C_le a b qx qy _ x y
      _ ≤ (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) * C := by
        gcongr

/-- Profile-explicit order-zero equation-(27) kernel estimate.  The source
The constant is now a fixed expression in the equation-(2) and equation-(21)
profiles rather than an existential selected after the scales. -/
theorem norm_dfiEquation27C_source_le_of_profiles
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (h : ℝ) (a b qx qy : ℕ) (x y : ℝ) :
    ‖dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h) x y‖ ≤
      (Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
      (Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
      (dfiEquation2FiniteConstant Cf 0 * dfiCutoffFiniteConstant Cφ 0) := by
  let C := dfiEquation2FiniteConstant Cf 0 * dfiCutoffFiniteConstant Cφ 0
  have hCf : 0 < dfiEquation2FiniteConstant Cf 0 := hfC.finiteConstant_pos 0
  have hCφ : 0 < dfiCutoffFiniteConstant Cφ 0 := by
    simpa [dfiCutoffFiniteConstant] using hφC.positive 0
  have hC : 0 < C := mul_pos hCf hCφ
  have hbound :=
    dfiEquation21_of_profiles_uniform_in_shift hf hfC hbox hφ hφC hscale 0 0 h x y
  have hFnorm : ‖dfiLocalizedWeight f φ h x y‖ ≤ C := by
    simpa only [dfiMixedDeriv_zero_zero, pow_zero, mul_one, max_self,
      Nat.zero_add, one_mul] using hbound.2
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith [hf.one_le_X])
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith [hf.one_le_Y])
  have hLX : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| := by
    positivity
  have hLY : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| := by
    positivity
  by_cases hF : dfiLocalizedWeight f φ h x y = 0
  · rw [dfiEquation27C, hF, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hLX hLY) hC.le
  · have hxy : (x, y) ∈ Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      support_uncurry_dfiLocalizedWeight_subset hbox hF
    have hxlog := abs_log_le_log_two_mul_of_mem_Icc hf.one_le_X hxy.1
    have hylog := abs_log_le_log_two_mul_of_mem_Icc hf.one_le_Y hxy.2
    calc
      ‖dfiEquation27C a b qx qy
          (dfiLocalizedWeight f φ h) x y‖ ≤
          (|Real.log x| + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (|Real.log y| + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          ‖dfiLocalizedWeight f φ h x y‖ :=
        norm_dfiEquation27C_le a b qx qy _ x y
      _ ≤ (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) * C := by
        gcongr
      _ = _ := by rfl

/-- The explicit source-profile constant controlling all derivatives needed
in the logarithmically weighted equation-(27) source slice.  Its definition
depends only on the two fixed derivative profiles and the derivative order,
not on any physical or arithmetic scale. -/
noncomputable def dfiEquation27SourceDerivativeConstant
    (Cf : ℕ → ℕ → ℝ) (Cφ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    dfiEquation2FiniteConstant Cf k * dfiCutoffFiniteConstant Cφ k * 2 ^ k

theorem dfiEquation27SourceDerivativeConstant_pos
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hfC : DFIEquation2Profile f P X Y Cf)
    {hφ : DFIRedundantCutoff φ U}
    (hφC : DFIRedundantCutoffProfile hφ Cφ) (j : ℕ) :
    0 < dfiEquation27SourceDerivativeConstant Cf Cφ j := by
  unfold dfiEquation27SourceDerivativeConstant
  apply Finset.sum_pos
  · intro k hk
    have hfpos := hfC.finiteConstant_pos k
    have hφpos : 0 < dfiCutoffFiniteConstant Cφ k := by
      dsimp [dfiCutoffFiniteConstant]
      exact Finset.sum_pos (fun i _hi ↦ hφC.positive i) ⟨0, by simp⟩
    positivity
  · exact ⟨0, by simp⟩

/-- Equation (21) and the explicit logarithmic derivatives give the full
`y`-derivative bound required in DFI equation (27).  The constant is chosen
before the shift and all arithmetic moduli; their logarithms remain in the
displayed factors. -/
theorem norm_iteratedDeriv_dfiEquation27C_source_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b qx qy : ℕ) (x y : ℝ),
      x ∈ Set.Icc X (2 * X) → y ∈ Set.Icc Y (2 * Y) →
      ‖iteratedDeriv j
          (fun y' => dfiEquation27C a b qx qy
            (dfiLocalizedWeight f φ h) x y') y‖ ≤
        (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          dfiEquation27SourceDerivativeConstant Cf Cφ j *
            dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
  let C : ℕ → ℝ := fun k =>
    dfiEquation2FiniteConstant Cf k * dfiCutoffFiniteConstant Cφ k * 2 ^ k
  have hC : ∀ k, 0 < C k := by
    intro k
    dsimp [C]
    have hfpos := hfC.finiteConstant_pos k
    have hφpos : 0 < dfiCutoffFiniteConstant Cφ k := by
      dsimp [dfiCutoffFiniteConstant]
      exact Finset.sum_pos (fun i _hi ↦ hφC.positive i) ⟨0, by simp⟩
    positivity
  have hbound : ∀ k h x y,
      ‖dfiMixedDeriv 0 k (dfiLocalizedWeight f φ h) x y‖ ≤
        C k * U⁻¹ ^ k := by
    intro k h x y
    have hb := (dfiEquation21_of_profiles_uniform_in_shift
      hf hfC hbox hφ hφC hscale 0 k h x y).2
    simpa [C] using hb
  let Csum : ℝ := ∑ k ∈ Finset.range (j + 1), C k
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    apply Finset.sum_pos
    · intro k hk
      exact hC k
    · exact ⟨0, by simp⟩
  intro h a b qx qy x y hx hy
  have hCsum_eq : Csum = dfiEquation27SourceDerivativeConstant Cf Cφ j := by
    simp only [Csum, C, dfiEquation27SourceDerivativeConstant]
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hmin : 0 ≤ min X Y := by
    exact le_min (zero_le_one.trans hf.one_le_X)
      (zero_le_one.trans hf.one_le_Y)
  have hPinv : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hf.one_le_P
  have hUmin : U ≤ min X Y := hscale.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hPinv hmin)
  have hUX : U ≤ X := hUmin.trans (min_le_left X Y)
  have hUY : U ≤ Y := hUmin.trans (min_le_right X Y)
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  have hLX : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hlogX : ‖dfiEquation27LogFactor a qx x‖ ≤ LX := by
    have hb := norm_iteratedDeriv_dfiEquation27LogFactor_le
      a qx 0 hf.one_le_X hφ.U_pos hUX hx
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, pow_zero, mul_one] using hb
  have hFsmooth : ContDiff ℝ ∞
      (fun y' : ℝ => dfiLocalizedWeight f φ h x y') :=
    (contDiff_uncurry_dfiLocalizedWeight (h := h) hf hφ).comp
      (contDiff_prodMk_right x)
  have hlogSmooth : ContDiffAt ℝ j (dfiEquation27LogFactor b qy) y := by
    have hypos : 0 < y := zero_lt_one.trans_le (hf.one_le_Y.trans hy.1)
    have hlog : ContDiffAt ℝ j (fun z : ℝ => (Real.log z : ℂ)) y :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (Real.contDiffAt_log.2 hypos.ne')).of_le (by exact_mod_cast le_top)
    let c : ℂ := -Complex.log (b : ℂ) +
      2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
    have hfun : dfiEquation27LogFactor b qy =
        fun z : ℝ => (Real.log z : ℂ) + c := by
      funext z
      simp only [dfiEquation27LogFactor, c]
      ring
    rw [hfun]
    exact hlog.add contDiffAt_const
  have hprod :
      iteratedDeriv j
          (fun y' => dfiEquation27C a b qx qy
            (dfiLocalizedWeight f φ h) x y') y =
        dfiEquation27LogFactor a qx x *
          (∑ s ∈ Finset.range (j + 1),
            (j.choose s : ℂ) *
              iteratedDeriv s (dfiEquation27LogFactor b qy) y *
              iteratedDeriv (j - s)
                (fun y' => dfiLocalizedWeight f φ h x y') y) := by
    have hmul := iteratedDeriv_mul hlogSmooth
      (hFsmooth.contDiffAt.of_le (by exact_mod_cast le_top))
    have hconst := iteratedDeriv_const_mul
      (dfiEquation27LogFactor a qx x)
      ((hlogSmooth.mul
        (hFsmooth.contDiffAt.of_le (by exact_mod_cast le_top))))
    rw [show (fun y' => dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) x y') =
        fun y' => dfiEquation27LogFactor a qx x *
          (dfiEquation27LogFactor b qy y' *
            dfiLocalizedWeight f φ h x y') by
      funext y'
      simp only [dfiEquation27C]
      ring]
    rw [hconst]
    exact congrArg (fun z : ℂ => dfiEquation27LogFactor a qx x * z) hmul
  rw [hprod]
  calc
    ‖dfiEquation27LogFactor a qx x *
        (∑ s ∈ Finset.range (j + 1),
          (j.choose s : ℂ) *
            iteratedDeriv s (dfiEquation27LogFactor b qy) y *
            iteratedDeriv (j - s)
              (fun y' => dfiLocalizedWeight f φ h x y') y)‖ ≤
        LX * ∑ s ∈ Finset.range (j + 1),
          ‖(j.choose s : ℂ) *
            iteratedDeriv s (dfiEquation27LogFactor b qy) y *
            iteratedDeriv (j - s)
              (fun y' => dfiLocalizedWeight f φ h x y') y‖ := by
      rw [norm_mul]
      exact mul_le_mul hlogX (norm_sum_le _ _)
        (norm_nonneg _) hLX
    _ ≤ LX * ∑ s ∈ Finset.range (j + 1),
        ((j.choose s : ℝ) * s.factorial * LY * U⁻¹ ^ s) *
          (Csum * U⁻¹ ^ (j - s)) := by
      apply mul_le_mul_of_nonneg_left _ hLX
      apply Finset.sum_le_sum
      intro s hs
      have hsle : s ≤ j := by simpa using hs
      have hlog := norm_iteratedDeriv_dfiEquation27LogFactor_le
        b qy s hf.one_le_Y hφ.U_pos hUY hy
      have hlog' : ‖iteratedDeriv s (dfiEquation27LogFactor b qy) y‖ ≤
          s.factorial * LY * U⁻¹ ^ s := by
        simpa only [LY] using hlog
      have hkMem : j - s ∈ Finset.range (j + 1) := by simp
      have hC_le : C (j - s) ≤ Csum := by
        dsimp [Csum]
        exact Finset.single_le_sum (fun k _ => (hC k).le) hkMem
      have hFraw := hbound (j - s) h x y
      have hF : ‖iteratedDeriv (j - s)
          (fun y' => dfiLocalizedWeight f φ h x y') y‖ ≤
          Csum * U⁻¹ ^ (j - s) := by
        have hpow : 0 ≤ U⁻¹ ^ (j - s) :=
          pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _
        have := hFraw.trans (mul_le_mul_of_nonneg_right hC_le hpow)
        simpa [dfiMixedDeriv] using this
      simp only [norm_mul, Complex.norm_natCast]
      have hcoeff : 0 ≤ (j.choose s : ℝ) := by positivity
      have hlogRhs : 0 ≤ (s.factorial : ℝ) * LY * U⁻¹ ^ s := by
        exact mul_nonneg (mul_nonneg (by positivity) hLY)
          (pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _)
      have hfirst : (j.choose s : ℝ) *
          ‖iteratedDeriv s (dfiEquation27LogFactor b qy) y‖ ≤
          (j.choose s : ℝ) * s.factorial * LY * U⁻¹ ^ s := by
        calc
          (j.choose s : ℝ) *
              ‖iteratedDeriv s (dfiEquation27LogFactor b qy) y‖ ≤
              (j.choose s : ℝ) *
                ((s.factorial : ℝ) * LY * U⁻¹ ^ s) :=
            mul_le_mul_of_nonneg_left hlog' hcoeff
          _ = (j.choose s : ℝ) * s.factorial * LY * U⁻¹ ^ s := by ring
      have hfirstNonneg : 0 ≤
          (j.choose s : ℝ) * s.factorial * LY * U⁻¹ ^ s := by
        simpa only [mul_assoc] using mul_nonneg hcoeff hlogRhs
      exact mul_le_mul
        hfirst hF (norm_nonneg _) hfirstNonneg
    _ = LX * LY * Csum * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
      rw [dfiEquation27LogLeibnizConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      have hsle : s ≤ j := by simpa using hs
      have hpow : U⁻¹ ^ s * U⁻¹ ^ (j - s) = U⁻¹ ^ j := by
        rw [← pow_add, Nat.add_sub_of_le hsle]
      calc
        LX * ((j.choose s : ℝ) * s.factorial * LY * U⁻¹ ^ s *
            (Csum * U⁻¹ ^ (j - s))) =
            LX * LY * Csum * ((j.choose s : ℝ) * s.factorial) *
              (U⁻¹ ^ s * U⁻¹ ^ (j - s)) := by ring
        _ = LX * LY * Csum * ((j.choose s : ℝ) * s.factorial) *
              U⁻¹ ^ j := by rw [hpow]
    _ = (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          dfiEquation27SourceDerivativeConstant Cf Cφ j *
            dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
      rw [← hCsum_eq]

/-- Compatibility form of the explicit source derivative estimate. -/
theorem exists_norm_iteratedDeriv_dfiEquation27C_source_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ) (x y : ℝ),
      x ∈ Set.Icc X (2 * X) → y ∈ Set.Icc Y (2 * Y) →
      ‖iteratedDeriv j
          (fun y' => dfiEquation27C a b qx qy
            (dfiLocalizedWeight f φ h) x y') y‖ ≤
        (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
  refine ⟨dfiEquation27SourceDerivativeConstant Cf Cφ j,
    dfiEquation27SourceDerivativeConstant_pos hfC hφC j, ?_⟩
  exact norm_iteratedDeriv_dfiEquation27C_source_le
    hf hfC hbox hφ hφC hscale j

/-- The affine family of one-variable slices occurring when equation (27)
is integrated first in the displacement variable. -/
noncomputable def dfiEquation27SourceSliceFamily
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (h x u : ℝ) : ℂ :=
  dfiEquation27Slice (dfiEquation27C a b qx qy F) h x u

/-- A Voronoi logarithmic main term after the exact positive scaling
`X = a x`.  This is one of the two Jacobian identities used in equation
(27). -/
theorem dfiVoronoiMainTerm_scale_nat
    (a q : ℕ) (ha : 0 < a) (G : ℝ → ℂ) :
    dfiVoronoiMainTerm q (fun x => G ((a : ℝ) * x)) =
      (q : ℂ)⁻¹ * (a : ℂ)⁻¹ *
        ∫ X in Set.Ioi (0 : ℝ),
          dfiEquation27LogFactor a q X * G X := by
  let H : ℝ → ℂ := fun X => dfiEquation27LogFactor a q X * G X
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hinter :
      (∫ x in Set.Ioi (0 : ℝ),
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * G ((a : ℝ) * x)) =
        ∫ x in Set.Ioi (0 : ℝ), H (x * (a : ℝ)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [H]
    rw [show x * (a : ℝ) = (a : ℝ) * x by ring]
    rw [dfiEquation27LogFactor_nat_mul a q ha x hx]
  unfold dfiVoronoiMainTerm
  rw [hinter, integral_comp_mul_right_Ioi H 0 haR]
  simp only [zero_mul, Complex.real_smul]
  rw [ofReal_inv, Complex.ofReal_natCast]
  simp only [H]
  ring

/-- The physical double integral denoted `I` in DFI section 6, after both
divisor-variable scalings have been made explicit. -/
noncomputable def dfiEquation27PhysicalMainIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ X in Set.Ioi (0 : ℝ), ∫ Y in Set.Ioi (0 : ℝ),
    dfiEquation27C a b qx qy F X Y *
      (dfiDeltaKernel w q (X - Y - h) : ℂ)

/-- The diagonal integral obtained from the physical main integral by the
uniform delta approximation in DFI equation (27).  The reduced moduli remain
visible because their logarithms are part of the source main term. -/
noncomputable def dfiEquation27CentralIntegral
    (a b qx qy : ℕ) (F : ℝ → ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ, dfiEquation27C a b qx qy F x (x - h)

/-- Applying the two Voronoi main branches and then returning to physical
variables gives exactly the DFI section-6 integral, including both
Jacobians and both reduced-modulus logarithms. -/
theorem dfiEquation27_doubleVoronoiMain_eq_physical
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (a b qx qy : ℕ) (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ → ℂ) (h : ℤ) :
    dfiVoronoiMainTerm qx (fun x =>
      dfiVoronoiMainTerm qy
        (dfiEquation23Weight w F a b h q x)) =
      (qx : ℂ)⁻¹ * (qy : ℂ)⁻¹ *
        (a : ℂ)⁻¹ * (b : ℂ)⁻¹ *
          dfiEquation27PhysicalMainIntegral w q a b qx qy F h := by
  let K : ℝ → ℂ := fun X =>
    ∫ Y in Set.Ioi (0 : ℝ),
      dfiEquation27LogFactor b qy Y * F X Y *
        (dfiDeltaKernel w q (X - Y - h) : ℂ)
  have hinner (x : ℝ) :
      dfiVoronoiMainTerm qy
          (dfiEquation23Weight w F a b h q x) =
        (qy : ℂ)⁻¹ * (b : ℂ)⁻¹ * K ((a : ℝ) * x) := by
    let G : ℝ → ℂ := fun Y =>
      F ((a : ℝ) * x) Y *
        (dfiDeltaKernel w q ((a : ℝ) * x - Y - h) : ℂ)
    have hfun :
        dfiEquation23Weight w F a b h q x =
          fun y => G ((b : ℝ) * y) := by
      funext y
      simp only [dfiEquation23Weight, G]
    rw [hfun, dfiVoronoiMainTerm_scale_nat b qy hb G]
    simp only [K, G]
    congr 1
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro Y hY
    ring
  rw [show (fun x => dfiVoronoiMainTerm qy
      (dfiEquation23Weight w F a b h q x)) =
      fun x => ((qy : ℂ)⁻¹ * (b : ℂ)⁻¹) *
        K ((a : ℝ) * x) by
      funext x
      exact hinner x]
  rw [dfiVoronoiMainTerm_const_mul,
    dfiVoronoiMainTerm_scale_nat a qx ha K]
  have hphys :
      (∫ X in Set.Ioi (0 : ℝ), dfiEquation27LogFactor a qx X * K X) =
        dfiEquation27PhysicalMainIntegral w q a b qx qy F h := by
    unfold dfiEquation27PhysicalMainIntegral
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only [K, dfiEquation27C]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro Y hY
    ring
  rw [hphys]
  ring

/-- Under the source coprimality condition `(a,b)=1`, the two reduced
Voronoi denominators produce exactly the arithmetic prefactor
`gcd(ab,q)/(ab q^2)` in DFI equations (24) and (27). -/
theorem dfiEquation27_reduced_main_prefactor
    (a b q : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    (((dfiReducedModulus a q).denominator : ℂ)⁻¹ *
          ((dfiReducedModulus b q).denominator : ℂ)⁻¹) *
        (a : ℂ)⁻¹ * (b : ℂ)⁻¹ =
      (Nat.gcd (a * b) q : ℂ) / ((q : ℂ) ^ 2 * (a : ℂ) * (b : ℂ)) := by
  let Ra := dfiReducedModulus a q
  let Rb := dfiReducedModulus b q
  have hga : Ra.gcd * Ra.denominator = q := Ra.denominator_reconstruct
  have hgb : Rb.gcd * Rb.denominator = q := Rb.denominator_reconstruct
  have hgprod : Nat.gcd (a * b) q = Ra.gcd * Rb.gcd := by
    change Nat.gcd (a * b) q = Nat.gcd a q * Nat.gcd b q
    rw [Nat.gcd_comm (a * b) q, hab.gcd_mul q,
      Nat.gcd_comm q a, Nat.gcd_comm q b]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hRa : (Ra.denominator : ℂ) ≠ 0 := by
    exact_mod_cast Ra.denominator_pos.ne'
  have hRb : (Rb.denominator : ℂ) ≠ 0 := by
    exact_mod_cast Rb.denominator_pos.ne'
  have hnat : q ^ 2 =
      Ra.denominator * Rb.denominator * Nat.gcd (a * b) q := by
    calc
      q ^ 2 = q * q := pow_two q
      _ = (Ra.gcd * Ra.denominator) *
          (Rb.gcd * Rb.denominator) :=
        congrArg₂ (· * ·) hga.symm hgb.symm
      _ = Ra.denominator * Rb.denominator * Nat.gcd (a * b) q := by
        rw [hgprod]
        ring
  dsimp only [Ra, Rb] at hga hgb hgprod hRa hRb ⊢
  field_simp
  exact_mod_cast hnat

/-- The complete primitive-residue main branch of equation (24), after both
Voronoi main terms are evaluated, is exactly the per-modulus summand used in
DFI equation (27). -/
theorem dfiEquation27_main_summand_exact
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b q : ℕ) [NeZero q]
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) (h : ℤ) :
    dfiEquation24MainCoefficient q h
        (dfiVoronoiMainTerm (dfiReducedModulus a q).denominator (fun x =>
          dfiVoronoiMainTerm (dfiReducedModulus b q).denominator
            (dfiEquation23Weight w F a b h q x))) =
      ((Nat.gcd (a * b) q : ℂ) /
          ((q : ℂ) ^ 2 * (a : ℂ) * (b : ℂ))) *
        ramanujanSumInt q (-h) *
          dfiEquation27PhysicalMainIntegral w q a b
            (dfiReducedModulus a q).denominator
            (dfiReducedModulus b q).denominator F h := by
  rw [dfiEquation24MainCoefficient_eq_ramanujan q (NeZero.pos q) h]
  rw [dfiEquation27_doubleVoronoiMain_eq_physical w q a b
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator ha hb F h]
  rw [dfiEquation27_reduced_main_prefactor a b q ha hb hab]
  ring

/-- Multiplication by a logarithm preserves global smoothness when the
other factor is smooth and supported a positive distance from zero. -/
theorem contDiff_log_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.Ici A) :
    ContDiff ℝ ∞ (fun y => ((Real.log y : ℂ) + c) * g y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have hEventually :
        (fun y : ℝ => ((Real.log y : ℂ) + c) * g y) =ᶠ[nhds 0] 0 := by
      filter_upwards [Iio_mem_nhds hA] with z hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_le_of_gt (show z < A from hz)) (hsupp hne)
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.2 hy
    have hlogC : ContDiffAt ℝ ∞ (fun z : ℝ => (Real.log z : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- Product-space version of logarithmic multiplication in the first
coordinate.  The apparent singularity at zero is removable because the
second factor is supported a positive distance from that axis. -/
theorem contDiff_log_fst_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.Ici A ×ˢ Set.univ) :
    ContDiff ℝ ∞ (fun p => ((Real.log p.1 : ℂ) + c) * g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 = 0
  · have hEventually :
        (fun z : ℝ × ℝ => ((Real.log z.1 : ℂ) + c) * g z) =ᶠ[nhds p] 0 := by
      have hmem : Set.Iio A ∈ nhds p.1 := by
        rw [hp]
        exact Iio_mem_nhds hA
      have hev : (Prod.fst ⁻¹' Set.Iio A) ∈ nhds p :=
        continuous_fst.continuousAt hmem
      filter_upwards [hev] with z hz
      change z.1 < A at hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_lt_of_ge (hsupp hne).1) hz
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.log z.1) p :=
      (Real.contDiffAt_log.2 hp).comp p contDiff_fst.contDiffAt
    have hlogC : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => (Real.log z.1 : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- Product-space version of logarithmic multiplication in the second
coordinate. -/
theorem contDiff_log_snd_add_const_mul_of_support_pos
    {A : ℝ} (hA : 0 < A) (c : ℂ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.univ ×ˢ Set.Ici A) :
    ContDiff ℝ ∞ (fun p => ((Real.log p.2 : ℂ) + c) * g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have hEventually :
        (fun z : ℝ × ℝ => ((Real.log z.2 : ℂ) + c) * g z) =ᶠ[nhds p] 0 := by
      have hmem : Set.Iio A ∈ nhds p.2 := by
        rw [hp]
        exact Iio_mem_nhds hA
      have hev : (Prod.snd ⁻¹' Set.Iio A) ∈ nhds p :=
        continuous_snd.continuousAt hmem
      filter_upwards [hev] with z hz
      change z.2 < A at hz
      have hgz : g z = 0 := by
        by_contra hne
        exact (not_lt_of_ge (hsupp hne).2) hz
      simp [hgz]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hlog : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.log z.2) p :=
      (Real.contDiffAt_log.2 hp).comp p contDiff_snd.contDiffAt
    have hlogC : ContDiffAt ℝ ∞
        (fun z : ℝ × ℝ => (Real.log z.2 : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p hlog
    exact (hlogC.add contDiffAt_const).mul hg.contDiffAt

/-- The literal two-variable coefficient `C(x,y)` in DFI equation (27) is
smooth for the source-localized weight.  The apparent singularities of the
two logarithms at zero are removable because equation (2) places the support
inside the positive dyadic box. -/
theorem contDiff_uncurry_dfiEquation27C_source
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h))) := by
  let F : ℝ × ℝ → ℂ :=
    Function.uncurry (dfiLocalizedWeight f φ h)
  let cx : ℂ := -Complex.log (a : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qx : ℂ)
  let cy : ℂ := -Complex.log (b : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
  have hFsmooth : ContDiff ℝ ∞ F := by
    exact contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hFsupp : Function.support F ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    exact support_uncurry_dfiLocalizedWeight_subset hbox
  have hFfst : Function.support F ⊆ Set.Ici X ×ˢ Set.univ := by
    intro p hp
    exact ⟨(hFsupp hp).1.1, Set.mem_univ _⟩
  let G : ℝ × ℝ → ℂ := fun p => ((Real.log p.1 : ℂ) + cx) * F p
  have hGsmooth : ContDiff ℝ ∞ G := by
    exact contDiff_log_fst_add_const_mul_of_support_pos
      (zero_lt_one.trans_le hf.one_le_X) cx hFsmooth hFfst
  have hGsupp : Function.support G ⊆ Set.univ ×ˢ Set.Ici Y := by
    intro p hp
    have hpF : F p ≠ 0 := by
      intro hzero
      exact hp (by simp [G, hzero])
    exact ⟨Set.mem_univ _, (hFsupp hpF).2.1⟩
  have hfinal := contDiff_log_snd_add_const_mul_of_support_pos
    (zero_lt_one.trans_le hf.one_le_Y) cy hGsmooth hGsupp
  convert hfinal using 1
  funext p
  simp only [Function.uncurry, dfiEquation27C, dfiEquation27LogFactor,
    F, G, cx, cy]
  ring

/-- Uniform pointwise derivative bound for the actual affine family in
equation (27).  Vanishing outside the dyadic source box is proved from
topological support, so the logarithmic estimate is never applied at its
singularity. -/
theorem norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b qx qy : ℕ) (x u : ℝ),
      ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖ ≤
        (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          dfiEquation27SourceDerivativeConstant Cf Cφ j *
            dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
  have hC := dfiEquation27SourceDerivativeConstant_pos hfC hφC j
  have hbound := norm_iteratedDeriv_dfiEquation27C_source_le
    hf hfC hbox hφ hφC hscale j
  intro h a b qx qy x u
  let G : ℝ × ℝ → ℂ := Function.uncurry
    (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h))
  let y : ℝ := x - h + u
  have hGsmooth : ContDiff ℝ ∞ G := by
    exact contDiff_uncurry_dfiEquation27C_source
      (h := h) hf hbox hφ a b qx qy
  have hshift :
      iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u =
        iteratedDeriv j
          (fun y' => dfiEquation27C a b qx qy
            (dfiLocalizedWeight f φ h) x y') y := by
    have ht := congrFun (iteratedDeriv_comp_const_add j
      (fun y' => dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) x y') (x - h)) u
    simpa only [dfiEquation27SourceSliceFamily, dfiEquation27Slice, y] using ht
  rw [hshift]
  by_cases hz : iteratedDeriv j
      (fun y' => dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) x y') y = 0
  · rw [hz, norm_zero]
    have hlogX : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| := by
      have hlog : 0 ≤ Real.log (2 * X) :=
        Real.log_nonneg (by nlinarith [hf.one_le_X])
      positivity
    have hlogY : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| := by
      have hlog : 0 ≤ Real.log (2 * Y) :=
        Real.log_nonneg (by nlinarith [hf.one_le_Y])
      positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hlogX hlogY) hC.le)
        (dfiEquation27LogLeibnizConstant_pos j).le)
      (pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _)
  · have hpartial : dfiPartialY j G (x, y) ≠ 0 := by
      rw [dfiPartialY_apply j hGsmooth x y]
      simpa only [G, Function.uncurry_apply_pair] using hz
    have hpDeriv : (x, y) ∈ tsupport (dfiPartialY j G) :=
      subset_tsupport _ hpartial
    have hpG : (x, y) ∈ tsupport G :=
      tsupport_dfiPartialY_subset j G hpDeriv
    have hsupport : Function.support G ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
      intro p hp
      have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
        intro hzero
        apply hp
        change dfiEquation27C a b qx qy
          (dfiLocalizedWeight f φ h) p.1 p.2 = 0
        rw [dfiEquation27C, hzero, mul_zero]
      exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
    have htsupport : tsupport G ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      closure_minimal hsupport (isClosed_Icc.prod isClosed_Icc)
    exact hbound h a b qx qy x y (htsupport hpG).1 (htsupport hpG).2

/-- Compatibility form of the explicit affine-slice derivative estimate. -/
theorem exists_norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ) (x u : ℝ),
      ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖ ≤
        (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j := by
  refine ⟨dfiEquation27SourceDerivativeConstant Cf Cφ j,
    dfiEquation27SourceDerivativeConstant_pos hfC hφC j, ?_⟩
  exact norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
    hf hfC hbox hφ hφC hscale j

/-- Joint smoothness of the affine slices used to turn the physical
two-variable integral in equation (27) into an outer integral of equation
(18). -/
theorem contDiff_uncurry_dfiEquation27_sourceSliceFamily
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) := by
  have hC := contDiff_uncurry_dfiEquation27C_source
    (h := h) hf hbox hφ a b qx qy
  exact hC.comp (by
    fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.1 - h + p.2)))

/-- The full affine slice family has compact support in the explicit
rectangle forced by the two dyadic source intervals. -/
theorem support_uncurry_dfiEquation27_sourceSliceFamily_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    Function.support (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) ⊆
      Set.Icc X (2 * X) ×ˢ
        Set.Icc (Y - 2 * X + h) (2 * Y - X + h) := by
  intro p hp
  have hlocal : dfiLocalizedWeight f φ h p.1 (p.1 - h + p.2) ≠ 0 := by
    intro hz
    exact hp (by simp [Function.uncurry, dfiEquation27SourceSliceFamily,
      dfiEquation27Slice, dfiEquation27C, hz])
  have hlocal' : (p.1, p.1 - h + p.2) ∈ Function.support
      (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
  have hmem := support_uncurry_dfiLocalizedWeight_subset hbox hlocal'
  constructor
  · exact hmem.1
  · constructor <;> linarith [hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2]

theorem hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    HasCompactSupport (Function.uncurry
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc)
  exact support_uncurry_dfiEquation27_sourceSliceFamily_subset
    hbox a b qx qy

theorem hasCompactSupport_dfiPartialY
    (j : ℕ) {g : ℝ × ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (dfiPartialY j g) := by
  induction j with
  | zero => simpa [dfiPartialY] using hg
  | succ j ih =>
      rw [dfiPartialY]
      exact ih.fderiv_apply (𝕜 := ℝ) (0, 1)

/-- The equation-(18) left side is integrable in the outer variable for the
literal source slice family. -/
theorem integrable_dfiEquation27_source_left
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy q : ℕ) (hq : 0 < q) :
    Integrable (fun x => dfiEquation12LeftComplex w q
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x)) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) := by
    exact hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hδSmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      (dfiDeltaKernel w q p.2 : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_dfiDeltaKernel w q hq).comp contDiff_snd)
  have hleftJoint : Integrable (fun p : ℝ × ℝ =>
      g p.1 p.2 * (dfiDeltaKernel w q p.2 : ℂ)) :=
    (hgSmooth.mul hδSmooth).continuous.integrable_of_hasCompactSupport
      hgCompact.mul_right
  change Integrable (fun x => dfiEquation12LeftComplex w q (g x))
  simpa only [dfiEquation12LeftComplex] using hleftJoint.integral_prod_left

/-- The central source slice is supported in the first dyadic interval. -/
theorem support_dfiEquation27_source_center_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {X Y h : ℝ}
    (hbox : DFILocalizedBox f X Y) (a b qx qy : ℕ) :
    Function.support (fun x => dfiEquation27SourceSliceFamily a b qx qy
      (dfiLocalizedWeight f φ h) h x 0) ⊆ Set.Icc X (2 * X) := by
  intro x hx
  have hlocal : dfiLocalizedWeight f φ h x (x - h) ≠ 0 := by
    intro hz
    exact hx (by simp [dfiEquation27SourceSliceFamily, dfiEquation27Slice,
      dfiEquation27C, hz])
  have hp : (x, x - h) ∈ Function.support
      (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
  exact (support_uncurry_dfiLocalizedWeight_subset hbox hp).1

/-- The central value in equation (18) is integrable in the outer variable
for the source family. -/
theorem integrable_dfiEquation27_source_center
    {P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (a b qx qy : ℕ) :
    Integrable (fun x => dfiEquation27SourceSliceFamily a b qx qy
      (dfiLocalizedWeight f φ h) h x 0) := by
  have hjoint := contDiff_uncurry_dfiEquation27_sourceSliceFamily
    (h := h) hf hbox hφ a b qx qy
  have hcenterCD := hjoint.comp (contDiff_prodMk_left (0 : ℝ))
  have hcenterSmooth : Continuous (fun x : ℝ =>
      dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x 0) := by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
      hcenterCD.continuous
  have hcenterCompact : HasCompactSupport (fun x : ℝ =>
      dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x 0) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact support_dfiEquation27_source_center_subset
      (h := h) hbox a b qx qy
  exact hcenterSmooth.integrable_of_hasCompactSupport hcenterCompact

/-- The complete equation-(18) derivative majorant is integrable in the
outer variable for the source family. -/
theorem integrable_dfiEquation27_source_majorant
    {Q P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy q j : ℕ) :
    Integrable (fun x => dfiEquation18ComplexMajorant
      (Q := Q) q j (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x)) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) := by
    exact contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) := by
    exact hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hgIntegrable : Integrable (Function.uncurry g) :=
    hgSmooth.continuous.integrable_of_hasCompactSupport hgCompact
  have hzeroMajor : Integrable (fun x => ∫ u : ℝ, ‖g x u‖) :=
    hgIntegrable.integral_norm_prod_left
  have hderivSmooth : ContDiff ℝ ∞
      (dfiPartialY j (Function.uncurry g)) :=
    contDiff_dfiPartialY j hgSmooth
  have hderivCompact : HasCompactSupport
      (dfiPartialY j (Function.uncurry g)) :=
    hasCompactSupport_dfiPartialY j hgCompact
  have hderivIntegrable : Integrable
      (dfiPartialY j (Function.uncurry g)) :=
    hderivSmooth.continuous.integrable_of_hasCompactSupport hderivCompact
  have hjMajor : Integrable (fun x =>
      ∫ u : ℝ, ‖iteratedDeriv j (g x) u‖) := by
    convert hderivIntegrable.integral_norm_prod_left using 1
    funext x
    apply integral_congr_ae
    filter_upwards [] with u
    rw [dfiPartialY_apply j hgSmooth x u]
    simp only [Function.uncurry_apply_pair]
  change Integrable (fun x => dfiEquation18ComplexMajorant
    (Q := Q) q j (g x))
  unfold dfiEquation18ComplexMajorant
  exact (hzeroMajor.const_mul
      ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹)).add
    (hjMajor.const_mul ((q : ℝ) ^ j * Q ^ (j - 1)))

/-- For fixed `x`, the source-localized weight is smooth in `y` and is
supported in the positive dyadic interval `[Y,2Y]`. -/
theorem dfiLocalizedWeight_fixed_left_smooth_support
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U h : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => dfiLocalizedWeight f φ h x y) ∧
      Function.support (fun y => dfiLocalizedWeight f φ h x y) ⊆
        Set.Icc Y (2 * Y) := by
  constructor
  · exact (contDiff_uncurry_dfiLocalizedWeight hf hφ).comp
      (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => (x, y)))
  · intro y hy
    have hp : (x, y) ∈ Function.support
        (Function.uncurry (dfiLocalizedWeight f φ h)) := hy
    exact (support_uncurry_dfiLocalizedWeight_subset hbox hp).2

/-- The actual equation-(27) slice has the smoothness required by the
complex delta approximation. -/
theorem contDiff_dfiEquation27_sourceSlice
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    ContDiff ℝ ∞ (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  obtain ⟨hgy, hgysupp⟩ :=
    dfiLocalizedWeight_fixed_left_smooth_support (h := h) hf hbox hφ x
  let cx : ℂ := dfiEquation27LogFactor a qx x
  let cy : ℂ := -Complex.log (b : ℂ) +
    2 * Real.eulerMascheroniConstant - 2 * Complex.log (qy : ℂ)
  have hweighted : ContDiff ℝ ∞ (fun y =>
      cx * ((Real.log y : ℂ) + cy) * dfiLocalizedWeight f φ h x y) := by
    simpa only [mul_assoc] using contDiff_const.mul
      (contDiff_log_add_const_mul_of_support_pos
        (lt_of_lt_of_le zero_lt_one hf.one_le_Y) cy hgy
        (hgysupp.trans Set.Icc_subset_Ici_self))
  have hcomp := hweighted.comp
    (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => x - h + u))
  convert hcomp using 1
  funext u
  simp only [Function.comp_def, dfiEquation27Slice, dfiEquation27C,
    dfiEquation27LogFactor, cx, cy]
  ring

/-- The redundant cutoff confines the actual equation-(27) slice to the
source interval `[-U,U]`. -/
theorem support_dfiEquation27_sourceSlice_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    Function.support (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
        Set.Icc (-U) U := by
  intro u hu
  have hlocal : dfiLocalizedWeight f φ h x (x - h + u) ≠ 0 := by
    intro hz
    exact hu (by simp [dfiEquation27Slice, dfiEquation27C, hz])
  have hcut : φ (x - (x - h + u) - h) ≠ 0 := by
    intro hz
    exact hlocal (by simp [dfiLocalizedWeight, hz])
  have hmem := hφ.support_subset hcut
  rw [show x - (x - h + u) - h = -u by ring] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

/-- Iterated derivatives do not enlarge the topological support of a
complex-valued one-variable function. -/
theorem tsupport_iteratedDeriv_complex_subset
    (g : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j g) ⊆ tsupport g := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

/-- Every derivative of an equation-(27) source slice remains supported
in the exact redundant-cutoff interval. -/
theorem support_iteratedDeriv_dfiEquation27_sourceSlice_subset
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy j : ℕ) (h x : ℝ) :
    Function.support (iteratedDeriv j (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x)) ⊆
        Set.Icc (-U) U := by
  have htop : tsupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
      Set.Icc (-U) U :=
    closure_minimal
      (support_dfiEquation27_sourceSlice_subset hφ a b qx qy h x)
      isClosed_Icc
  intro u hu
  exact htop (tsupport_iteratedDeriv_complex_subset _ j
    (subset_tsupport _ hu))

/-- A whole-line integral of a nonnegative norm, supported in a compact
interval and bounded pointwise, is at most interval length times the
pointwise bound. -/
theorem integral_norm_le_interval_length_mul
    (g : ℝ → ℂ) {A B M : ℝ} (hAB : A ≤ B)
    (hg : Integrable (fun u => ‖g u‖))
    (hsupp : Function.support g ⊆ Set.Icc A B)
    (hbound : ∀ u : ℝ, ‖g u‖ ≤ M) :
    (∫ u : ℝ, ‖g u‖) ≤ (B - A) * M := by
  have hzero : ∀ u ∉ Set.Icc A B, ‖g u‖ = 0 := by
    intro u hu
    have hgu : g u = 0 := by
      by_contra hne
      exact hu (hsupp hne)
    rw [hgu, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    (∫ u : ℝ in Set.Icc A B, ‖g u‖) ≤
        ∫ _u : ℝ in Set.Icc A B, M := by
      exact setIntegral_mono_on hg.integrableOn
        (continuousOn_const.integrableOn_compact isCompact_Icc)
        measurableSet_Icc (fun u hu => hbound u)
    _ = (B - A) * M := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def,
        Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hAB)]

/-- Compact support of the source equation-(27) slice, derived rather than
left as a theorem parameter. -/
theorem hasCompactSupport_dfiEquation27_sourceSlice
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    HasCompactSupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  exact support_dfiEquation27_sourceSlice_subset hφ a b qx qy h x

/-- Real-valued companion to `integral_norm_le_interval_length_mul`. -/
theorem integral_le_interval_length_mul
    (g : ℝ → ℝ) {A B M : ℝ} (hAB : A ≤ B)
    (hg : Integrable g) (hsupp : Function.support g ⊆ Set.Icc A B)
    (hbound : ∀ u : ℝ, g u ≤ M) :
    (∫ u : ℝ, g u) ≤ (B - A) * M := by
  have hzero : ∀ u ∉ Set.Icc A B, g u = 0 := by
    intro u hu
    by_contra hne
    exact hu (hsupp hne)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    (∫ u : ℝ in Set.Icc A B, g u) ≤
        ∫ _u : ℝ in Set.Icc A B, M := by
      exact setIntegral_mono_on hg.integrableOn
        (continuousOn_const.integrableOn_compact isCompact_Icc)
        measurableSet_Icc (fun u hu => hbound u)
    _ = (B - A) * M := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def,
        Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hAB)]

/-- The inner derivative mass in DFI equation (27), with exact support
length `2U` and the source-uniform `U⁻ʲ` derivative scale. -/
theorem integral_norm_iteratedDeriv_dfiEquation27_sourceSlice_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b qx qy : ℕ) (x : ℝ),
      (∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
        2 * U *
          ((1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            dfiEquation27SourceDerivativeConstant Cf Cφ j *
              dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
  have hpoint := norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
    hf hfC hbox hφ hφC hscale j
  intro h a b qx qy x
  let g : ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h x
  have hsmooth : ContDiff ℝ ∞ g := by
    exact contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x
  have hderivSmooth : ContDiff ℝ ∞ (iteratedDeriv j g) :=
    ContDiff.contDiff_iteratedDeriv_top hsmooth j
  have hsupp : Function.support (iteratedDeriv j g) ⊆ Set.Icc (-U) U := by
    exact support_iteratedDeriv_dfiEquation27_sourceSlice_subset
      hφ a b qx qy j h x
  have hcompact : HasCompactSupport (iteratedDeriv j g) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable (fun u => ‖iteratedDeriv j g u‖) :=
    hderivSmooth.continuous.norm.integrable_of_hasCompactSupport
      hcompact.norm
  have hraw := integral_norm_le_interval_length_mul
    (iteratedDeriv j g) (by linarith [hφ.U_pos]) hint hsupp
    (fun u => hpoint h a b qx qy x u)
  simpa only [g] using hraw.trans_eq (by ring)

/-- Compatibility form of the explicit inner derivative-mass bound. -/
theorem exists_integral_norm_iteratedDeriv_dfiEquation27_sourceSlice_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ) (x : ℝ),
      (∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
        2 * U *
          ((1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
  refine ⟨dfiEquation27SourceDerivativeConstant Cf Cφ j,
    dfiEquation27SourceDerivativeConstant_pos hfC hφC j, ?_⟩
  exact integral_norm_iteratedDeriv_dfiEquation27_sourceSlice_le
    hf hfC hbox hφ hφC hscale j

/-- Outer integrability of the inner derivative mass for the literal
equation-(27) source family. -/
theorem integrable_integral_norm_iteratedDeriv_dfiEquation27_source
    {P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy j : ℕ) :
    Integrable (fun x : ℝ => ∫ u : ℝ, ‖iteratedDeriv j
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x) u‖) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) :=
    contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) :=
    hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hpartialSmooth : ContDiff ℝ ∞
      (dfiPartialY j (Function.uncurry g)) :=
    contDiff_dfiPartialY j hgSmooth
  have hpartialCompact : HasCompactSupport
      (dfiPartialY j (Function.uncurry g)) :=
    hasCompactSupport_dfiPartialY j hgCompact
  have hpartialIntegrable : Integrable
      (dfiPartialY j (Function.uncurry g)) :=
    hpartialSmooth.continuous.integrable_of_hasCompactSupport hpartialCompact
  have hprod := hpartialIntegrable.integral_norm_prod_left
  convert hprod using 1
  funext x
  apply integral_congr_ae
  filter_upwards [] with u
  rw [dfiPartialY_apply j hgSmooth x u]
  rfl

/-- The complete two-variable derivative mass used in the second term of
DFI equation (18).  Both support lengths are now explicit. -/
theorem exists_integral_integral_norm_iteratedDeriv_dfiEquation27_source_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ),
      (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
        2 * X * U *
          ((1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
  obtain ⟨C, hC, hinner⟩ :=
    exists_integral_norm_iteratedDeriv_dfiEquation27_sourceSlice_le
      hf hfC hbox hφ hφC hscale j
  refine ⟨C, hC, ?_⟩
  intro h a b qx qy
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  let H : ℝ → ℝ := fun x => ∫ u : ℝ, ‖iteratedDeriv j (g x) u‖
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) :=
    contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) :=
    hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hpartialSmooth : ContDiff ℝ ∞
      (dfiPartialY j (Function.uncurry g)) :=
    contDiff_dfiPartialY j hgSmooth
  have hpartialCompact : HasCompactSupport
      (dfiPartialY j (Function.uncurry g)) :=
    hasCompactSupport_dfiPartialY j hgCompact
  have hpartialIntegrable : Integrable
      (dfiPartialY j (Function.uncurry g)) :=
    hpartialSmooth.continuous.integrable_of_hasCompactSupport hpartialCompact
  have hHint : Integrable H := by
    have hprod := hpartialIntegrable.integral_norm_prod_left
    convert hprod using 1
    funext x
    apply integral_congr_ae
    filter_upwards [] with u
    rw [dfiPartialY_apply j hgSmooth x u]
    rfl
  have hHsupport : Function.support H ⊆ Set.Icc X (2 * X) := by
    intro x hx
    by_contra hxmem
    have hsliceZero : g x = 0 := by
      funext u
      by_contra hne
      have hp : (x, u) ∈ Function.support (Function.uncurry g) := hne
      exact hxmem
        (support_uncurry_dfiEquation27_sourceSliceFamily_subset
          (h := h) hbox a b qx qy hp).1
    have hderivZero : iteratedDeriv j (g x) = 0 := by
      rw [hsliceZero]
      funext u
      exact iteratedDeriv_const_zero
    exact hx (by simp [H, hderivZero])
  have hHbound : ∀ x : ℝ, H x ≤
      2 * U *
        ((1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
    intro x
    exact hinner h a b qx qy x
  have hraw := integral_le_interval_length_mul H
    (by nlinarith [hf.one_le_X]) hHint hHsupport hHbound
  simpa only [H, g] using hraw.trans_eq (by ring)

/-- A nonzero derivative of the affine equation-(27) slice retains all
three pieces of source support geometry: the first physical coordinate is
in its dyadic interval, the second physical coordinate is in its dyadic
interval, and the displacement is in the redundant-cutoff interval.  The
last two facts together give the second, `Y`-length, projection needed for
the symmetric `min X Y` form of DFI's equation-(27) error. -/
theorem dfiEquation27_sourceSlice_iteratedDeriv_support_geometry
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy j : ℕ) (h x u : ℝ)
    (hne : iteratedDeriv j
      (dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x) u ≠ 0) :
    x ∈ Set.Icc X (2 * X) ∧
      x - h + u ∈ Set.Icc Y (2 * Y) ∧
      u ∈ Set.Icc (-U) U := by
  let G : ℝ × ℝ → ℂ := Function.uncurry
    (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h))
  let y : ℝ := x - h + u
  have hGsmooth : ContDiff ℝ ∞ G := by
    exact contDiff_uncurry_dfiEquation27C_source
      (h := h) hf hbox hφ a b qx qy
  have hshift :
      iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u =
        iteratedDeriv j
          (fun y' => dfiEquation27C a b qx qy
            (dfiLocalizedWeight f φ h) x y') y := by
    have ht := congrFun (iteratedDeriv_comp_const_add j
      (fun y' => dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) x y') (x - h)) u
    simpa only [dfiEquation27SourceSliceFamily, dfiEquation27Slice, y] using ht
  have hpartial : dfiPartialY j G (x, y) ≠ 0 := by
    rw [dfiPartialY_apply j hGsmooth x y]
    rw [hshift] at hne
    simpa only [G, Function.uncurry_apply_pair] using hne
  have hpDeriv : (x, y) ∈ tsupport (dfiPartialY j G) :=
    subset_tsupport _ hpartial
  have hpG : (x, y) ∈ tsupport G :=
    tsupport_dfiPartialY_subset j G hpDeriv
  have hsupport : Function.support G ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
      intro hzero
      apply hp
      change dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) p.1 p.2 = 0
      rw [dfiEquation27C, hzero, mul_zero]
    exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
  have htsupport : tsupport G ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    closure_minimal hsupport (isClosed_Icc.prod isClosed_Icc)
  have hxy := htsupport hpG
  have hu := support_iteratedDeriv_dfiEquation27_sourceSlice_subset
    hφ a b qx qy j h x hne
  exact ⟨hxy.1, hxy.2, hu⟩

/-- Symmetric two-variable derivative mass for equation (27).  Besides the
literal `x`-projection of length `X`, the affine relation
`y = x - h + u`, with `y ∈ [Y,2Y]` and `|u| ≤ U`, supplies a second
projection of length `Y + 2U`.  Since `U ≤ min X Y`, the outer mass is
bounded by `6 * min X Y * U`, uniformly without ordering `X` and `Y`. -/
theorem integral_integral_norm_iteratedDeriv_dfiEquation27_source_le_min
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b qx qy : ℕ),
      (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
        6 * min X Y * U *
          ((1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            dfiEquation27SourceDerivativeConstant Cf Cφ j *
              dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
  let C : ℝ := dfiEquation27SourceDerivativeConstant Cf Cφ j
  have hC : 0 < C := by
    simpa only [C] using dfiEquation27SourceDerivativeConstant_pos hfC hφC j
  have hinner := integral_norm_iteratedDeriv_dfiEquation27_sourceSlice_le
    hf hfC hbox hφ hφC hscale j
  intro h a b qx qy
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  let H : ℝ → ℝ := fun x => ∫ u : ℝ, ‖iteratedDeriv j (g x) u‖
  let B : ℝ :=
    (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
      C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j
  have hgSmooth : ContDiff ℝ ∞ (Function.uncurry g) :=
    contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hf hbox hφ a b qx qy
  have hgCompact : HasCompactSupport (Function.uncurry g) :=
    hasCompactSupport_uncurry_dfiEquation27_sourceSliceFamily
      (h := h) hbox a b qx qy
  have hpartialSmooth : ContDiff ℝ ∞
      (dfiPartialY j (Function.uncurry g)) :=
    contDiff_dfiPartialY j hgSmooth
  have hpartialCompact : HasCompactSupport
      (dfiPartialY j (Function.uncurry g)) :=
    hasCompactSupport_dfiPartialY j hgCompact
  have hpartialIntegrable : Integrable
      (dfiPartialY j (Function.uncurry g)) :=
    hpartialSmooth.continuous.integrable_of_hasCompactSupport hpartialCompact
  have hHint : Integrable H := by
    have hprod := hpartialIntegrable.integral_norm_prod_left
    convert hprod using 1
    funext x
    apply integral_congr_ae
    filter_upwards [] with u
    rw [dfiPartialY_apply j hgSmooth x u]
    rfl
  have hHsupportX : Function.support H ⊆ Set.Icc X (2 * X) := by
    intro x hx
    by_contra hxmem
    have hzero : ∀ u : ℝ, iteratedDeriv j (g x) u = 0 := by
      intro u
      by_contra hne
      have hgeom := dfiEquation27_sourceSlice_iteratedDeriv_support_geometry
        hf hbox hφ a b qx qy j h x u (by simpa only [g] using hne)
      exact hxmem hgeom.1
    apply hx
    simp only [H, hzero, norm_zero, integral_zero]
  have hHsupportY : Function.support H ⊆
      Set.Icc (Y + h - U) (2 * Y + h + U) := by
    intro x hx
    by_contra hxmem
    have hzero : ∀ u : ℝ, iteratedDeriv j (g x) u = 0 := by
      intro u
      by_contra hne
      have hgeom := dfiEquation27_sourceSlice_iteratedDeriv_support_geometry
        hf hbox hφ a b qx qy j h x u (by simpa only [g] using hne)
      exact hxmem ⟨by linarith [hgeom.2.1.1, hgeom.2.2.2],
        by linarith [hgeom.2.1.2, hgeom.2.2.1]⟩
    apply hx
    simp only [H, hzero, norm_zero, integral_zero]
  have hHbound : ∀ x : ℝ, H x ≤ 2 * U * B := by
    intro x
    simpa only [H, g, B, mul_assoc] using hinner h a b qx qy x
  have hrawX := integral_le_interval_length_mul H
    (by nlinarith [hf.one_le_X]) hHint hHsupportX hHbound
  have hrawY := integral_le_interval_length_mul H
    (by nlinarith [hf.one_le_Y, hφ.U_pos]) hHint hHsupportY hHbound
  have hPinv : P⁻¹ ≤ 1 :=
    (inv_le_one₀ (zero_lt_one.trans_le hf.one_le_P)).2 hf.one_le_P
  have hUleMin : U ≤ min X Y := by
    calc
      U ≤ P⁻¹ * min X Y := hscale
      _ ≤ 1 * min X Y := by
        gcongr
        exact le_min (zero_le_one.trans hf.one_le_X)
          (zero_le_one.trans hf.one_le_Y)
      _ = min X Y := one_mul _
  have hUleY : U ≤ Y := hUleMin.trans (min_le_right X Y)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    have hLX : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| := by
      positivity
    have hLY : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| := by
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hLX hLY) hC.le)
          (dfiEquation27LogLeibnizConstant_pos j).le)
      (pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _)
  have hTwoUB0 : 0 ≤ 2 * U * B :=
    mul_nonneg (mul_nonneg (by norm_num) hφ.U_pos.le) hB0
  have hXbound : (∫ x : ℝ, H x) ≤ 2 * X * U * B := by
    calc
      _ ≤ (2 * X - X) * (2 * U * B) := hrawX
      _ = 2 * X * U * B := by ring
  have hYbound : (∫ x : ℝ, H x) ≤ 6 * Y * U * B := by
    calc
      _ ≤ ((2 * Y + h + U) - (Y + h - U)) * (2 * U * B) := hrawY
      _ = (Y + 2 * U) * (2 * U * B) := by ring
      _ ≤ (3 * Y) * (2 * U * B) := by
        gcongr
        linarith
      _ = 6 * Y * U * B := by ring
  by_cases hXY : X ≤ Y
  · have hmin : min X Y = X := min_eq_left hXY
    rw [hmin]
    change (∫ x : ℝ, H x) ≤ 6 * X * U * B
    exact hXbound.trans (by
      have hUB0 : 0 ≤ U * B := mul_nonneg hφ.U_pos.le hB0
      have hcoeff : 2 * X ≤ 6 * X := by nlinarith [hf.one_le_X]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hUB0)
  · have hYX : Y ≤ X := le_of_not_ge hXY
    rw [min_eq_right hYX]
    change (∫ x : ℝ, H x) ≤ 6 * Y * U * B
    exact hYbound

/-- Compatibility form of the explicit symmetric derivative-mass bound. -/
theorem exists_integral_integral_norm_iteratedDeriv_dfiEquation27_source_le_min
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy : ℕ),
      (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
        6 * min X Y * U *
          ((1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
            C * dfiEquation27LogLeibnizConstant j * U⁻¹ ^ j) := by
  refine ⟨dfiEquation27SourceDerivativeConstant Cf Cφ j,
    dfiEquation27SourceDerivativeConstant_pos hfC hφC j, ?_⟩
  exact integral_integral_norm_iteratedDeriv_dfiEquation27_source_le_min
    hf hfC hbox hφ hφC hscale j

/-- The scale-independent profile constant for the source-integrated
equation-(18) majorant. -/
noncomputable def dfiEquation27SourceMajorantConstant
    (Cf : ℕ → ℕ → ℝ) (Cφ : ℕ → ℝ) (j : ℕ) : ℝ :=
  dfiEquation27SourceDerivativeConstant Cf Cφ 0 *
      dfiEquation27LogLeibnizConstant 0 +
    dfiEquation27SourceDerivativeConstant Cf Cφ j *
      dfiEquation27LogLeibnizConstant j

theorem dfiEquation27SourceMajorantConstant_pos
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hfC : DFIEquation2Profile f P X Y Cf)
    {hφ : DFIRedundantCutoff φ U}
    (hφC : DFIRedundantCutoffProfile hφ Cφ) (j : ℕ) :
    0 < dfiEquation27SourceMajorantConstant Cf Cφ j := by
  unfold dfiEquation27SourceMajorantConstant
  exact add_pos
    (mul_pos (dfiEquation27SourceDerivativeConstant_pos hfC hφC 0)
      (dfiEquation27LogLeibnizConstant_pos 0))
    (mul_pos (dfiEquation27SourceDerivativeConstant_pos hfC hφC j)
      (dfiEquation27LogLeibnizConstant_pos j))

/-- The abstract equation-(18) majorant integrated in the outer variable,
now expressed entirely through the source scales and reduced-modulus
logarithms.  This is the quantitative analytic input to the small-modulus
part of DFI equation (27). -/
theorem integral_dfiEquation18ComplexMajorant_source_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b qx qy q : ℕ),
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b qx qy
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                  dfiEquation27SourceMajorantConstant Cf Cφ j)) +
          ((q : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                dfiEquation27SourceMajorantConstant Cf Cφ j * U⁻¹ ^ j)) := by
  let C0 : ℝ := dfiEquation27SourceDerivativeConstant Cf Cφ 0
  let Cj : ℝ := dfiEquation27SourceDerivativeConstant Cf Cφ j
  let C : ℝ := dfiEquation27SourceMajorantConstant Cf Cφ j
  have hC0 : 0 < C0 := by
    simpa only [C0] using dfiEquation27SourceDerivativeConstant_pos hfC hφC 0
  have hCj : 0 < Cj := by
    simpa only [Cj] using dfiEquation27SourceDerivativeConstant_pos hfC hφC j
  have hC : 0 < C := by
    simpa only [C] using dfiEquation27SourceMajorantConstant_pos hfC hφC j
  have hmass0 :=
    integral_integral_norm_iteratedDeriv_dfiEquation27_source_le_min
      hf hfC hbox hφ hφC hscale 0
  have hmassj :=
    integral_integral_norm_iteratedDeriv_dfiEquation27_source_le_min
      hf hfC hbox hφ hφC hscale j
  intro h a b qx qy q
  let L : ℝ :=
    (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|)
  have hLX : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx| := by
    have hlog : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy| := by
    have hlog : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hL : 0 ≤ L := mul_nonneg hLX hLY
  have hbase : 0 ≤ 6 * min X Y * U * L := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (le_min (zero_le_one.trans hf.one_le_X)
            (zero_le_one.trans hf.one_le_Y))) hφ.U_pos.le) hL
  have hC0le : C0 * dfiEquation27LogLeibnizConstant 0 ≤ C := by
    dsimp [C, C0, Cj, dfiEquation27SourceMajorantConstant]
    linarith [mul_pos hCj (dfiEquation27LogLeibnizConstant_pos j)]
  have hCjle : Cj * dfiEquation27LogLeibnizConstant j ≤ C := by
    dsimp [C, C0, Cj, dfiEquation27SourceMajorantConstant]
    linarith [mul_pos hC0 (dfiEquation27LogLeibnizConstant_pos 0)]
  have hmass0' :
      (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv 0
        (dfiEquation27SourceSliceFamily a b qx qy
          (dfiLocalizedWeight f φ h) h x) u‖) ≤
        6 * min X Y * U * (L * C) := by
    have hraw := hmass0 h a b qx qy
    have hraw' :
        (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv 0
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
          6 * min X Y * U * (L *
            (C0 * dfiEquation27LogLeibnizConstant 0)) := by
      simpa only [L, pow_zero, mul_one, mul_assoc] using hraw
    exact hraw'.trans (by
      have := mul_le_mul_of_nonneg_left hC0le hbase
      simpa only [mul_assoc] using this)
  have hmassj' :
      (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv j
        (dfiEquation27SourceSliceFamily a b qx qy
          (dfiLocalizedWeight f φ h) h x) u‖) ≤
        6 * min X Y * U * (L * C * U⁻¹ ^ j) := by
    have hraw := hmassj h a b qx qy
    have hraw' :
        (∫ x : ℝ, ∫ u : ℝ, ‖iteratedDeriv j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) u‖) ≤
          6 * min X Y * U *
            (L * (Cj * dfiEquation27LogLeibnizConstant j) * U⁻¹ ^ j) := by
      simpa only [L, mul_assoc] using hraw
    exact hraw'.trans (by
      have hpow : 0 ≤ U⁻¹ ^ j :=
        pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _
      have hmid := mul_le_mul_of_nonneg_right hCjle hpow
      have hscaled := mul_le_mul_of_nonneg_left hmid hbase
      simpa only [mul_assoc] using hscaled)
  have hint0 := integrable_integral_norm_iteratedDeriv_dfiEquation27_source
    hf hbox hφ a b qx qy 0 (h := h)
  have hintj := integrable_integral_norm_iteratedDeriv_dfiEquation27_source
    hf hbox hφ a b qx qy j (h := h)
  have hintbase : Integrable (fun x : ℝ => ∫ u : ℝ,
      ‖dfiEquation27SourceSliceFamily a b qx qy
        (dfiLocalizedWeight f φ h) h x u‖) := by
    simpa using hint0
  have hmassbase :
      (∫ x : ℝ, ∫ u : ℝ,
        ‖dfiEquation27SourceSliceFamily a b qx qy
          (dfiLocalizedWeight f φ h) h x u‖) ≤
        6 * min X Y * U * (L * C) := by
    simpa using hmass0'
  unfold dfiEquation18ComplexMajorant
  rw [integral_add (hintbase.const_mul
      ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹))
    (hintj.const_mul ((q : ℝ) ^ j * Q ^ (j - 1))),
    integral_const_mul, integral_const_mul]
  have hcoef0 : 0 ≤ (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ := by
    positivity
  have hcoefj : 0 ≤ (q : ℝ) ^ j * Q ^ (j - 1) := by
    positivity
  dsimp [L] at hmass0' hmassj' ⊢
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmassbase hcoef0)
    (mul_le_mul_of_nonneg_left hmassj' hcoefj)

/-- Compatibility form of the explicit source-majorant estimate. -/
theorem exists_integral_dfiEquation18ComplexMajorant_source_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b qx qy q : ℕ),
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b qx qy
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) * C)) +
          ((q : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                C * U⁻¹ ^ j)) := by
  refine ⟨dfiEquation27SourceMajorantConstant Cf Cφ j,
    dfiEquation27SourceMajorantConstant_pos hfC hφC j, ?_⟩
  exact integral_dfiEquation18ComplexMajorant_source_le
    hQ hf hfC hbox hφ hφC hscale j

/-- Equation (18) with the two reduced Voronoi denominators substituted.
The denominator logarithms are bounded uniformly by the original modulus,
so no reduced-modulus parameter remains in the quantitative estimate. -/
theorem integral_dfiEquation18ComplexMajorant_reduced_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b q : ℕ), 0 < q →
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q)
          (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                  dfiEquation27SourceMajorantConstant Cf Cφ j)) +
          ((q : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                  dfiEquation27SourceMajorantConstant Cf Cφ j * U⁻¹ ^ j)) := by
  have hsource := integral_dfiEquation18ComplexMajorant_source_le
    hQ hf hfC hbox hφ hφC hscale j
  intro h a b q hq
  have hqa := abs_log_dfiReducedDenominator_le a q hq
  have hqb := abs_log_dfiReducedDenominator_le b q hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hq)
  have hLX : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator b q : ℝ)| := by
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hLXq : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log q := by
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLYq : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log q := by
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hbase : 0 ≤ 6 * min X Y * U := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (le_min (zero_le_one.trans hf.one_le_X)
          (zero_le_one.trans hf.one_le_Y))) hφ.U_pos.le
  refine (hsource h a b
    (dfiReducedDenominator a q)
    (dfiReducedDenominator b q) q).trans ?_
  have hcoef0 : 0 ≤ (q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ := by positivity
  have hcoefj : 0 ≤ (q : ℝ) ^ j * Q ^ (j - 1) := by positivity
  have hpow : 0 ≤ U⁻¹ ^ j :=
    pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _
  have hC : 0 ≤ dfiEquation27SourceMajorantConstant Cf Cφ j :=
    (dfiEquation27SourceMajorantConstant_pos hfC hφC j).le
  gcongr

/-- Compatibility form of the explicit reduced-modulus majorant. -/
theorem exists_integral_dfiEquation18ComplexMajorant_reduced_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b q : ℕ), 0 < q →
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) * C)) +
          ((q : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
                C * U⁻¹ ^ j)) := by
  refine ⟨dfiEquation27SourceMajorantConstant Cf Cφ j,
    dfiEquation27SourceMajorantConstant_pos hfC hφC j, ?_⟩
  exact integral_dfiEquation18ComplexMajorant_reduced_le
    hQ hf hfC hbox hφ hφC hscale j

/-- Uniform finite-modulus form of the reduced equation-(18) estimate.  For
`1 ≤ q ≤ K`, every occurrence of `q` on the right is enlarged to `K`; this
is the form that can be pulled through the equation-(27) modulus sum. -/
theorem integral_dfiEquation18ComplexMajorant_reduced_Icc_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
      ∀ (h : ℝ) (a b K q : ℕ), q ∈ Finset.Icc 1 K →
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((K : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                  dfiEquation27SourceMajorantConstant Cf Cφ j)) +
          ((K : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                dfiEquation27SourceMajorantConstant Cf Cφ j * U⁻¹ ^ j)) := by
  have hsource := integral_dfiEquation18ComplexMajorant_reduced_le
    hQ hf hfC hbox hφ hφC hscale j
  intro h a b K q hqmem
  have hqNat := (Finset.mem_Icc.mp hqmem).1
  have hqKnat := (Finset.mem_Icc.mp hqmem).2
  have hq : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hqNat
  have hqK : (q : ℝ) ≤ K := by exact_mod_cast hqKnat
  have hlogqK : Real.log (q : ℝ) ≤ Real.log (K : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq) hqK
  have hlogK : 0 ≤ Real.log (K : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hqNat.trans hqKnat)
  have hLXq : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log q := by
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqNat)
    positivity
  have hLYq : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log q := by
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqNat)
    positivity
  have hLXK : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLYK : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  refine (hsource h a b q hq).trans ?_
  have hbase : 0 ≤ 6 * min X Y * U := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (le_min (zero_le_one.trans hf.one_le_X)
          (zero_le_one.trans hf.one_le_Y))) hφ.U_pos.le
  have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ := by positivity
  have hQpow : 0 ≤ Q ^ (j - 1) := by positivity
  have hUpow : 0 ≤ U⁻¹ ^ j :=
    pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _
  have hC : 0 ≤ dfiEquation27SourceMajorantConstant Cf Cφ j :=
    (dfiEquation27SourceMajorantConstant_pos hfC hφC j).le
  gcongr

/-- Compatibility form of the explicit finite-modulus majorant. -/
theorem exists_integral_dfiEquation18ComplexMajorant_reduced_Icc_le
    {Q P X Y U : ℝ} (hQ : 0 < Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b K q : ℕ), q ∈ Finset.Icc 1 K →
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x)) ≤
        ((K : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) * C)) +
          ((K : ℝ) ^ j * Q ^ (j - 1)) *
            (6 * min X Y * U *
              ((1 + Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                (1 + Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
                C * U⁻¹ ^ j)) := by
  refine ⟨dfiEquation27SourceMajorantConstant Cf Cφ j,
    dfiEquation27SourceMajorantConstant_pos hfC hφC j, ?_⟩
  exact integral_dfiEquation18ComplexMajorant_reduced_Icc_le
    hQ hf hfC hbox hφ hφC hscale j

/-- The common analytic envelope pulled out of the small-modulus sum in
DFI equation (27). -/
noncomputable def dfiEquation27IntegratedErrorEnvelope
    (Q X Y U : ℝ) (a b K j : ℕ) : ℝ :=
  ((K : ℝ) ^ j * (Q ^ (j + 1))⁻¹) *
      (6 * min X Y * U *
        ((1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log K))) +
    ((K : ℝ) ^ j * Q ^ (j - 1)) *
      (6 * min X Y * U *
        ((1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
          U⁻¹ ^ j))

theorem dfiEquation27IntegratedErrorEnvelope_nonneg
    {Q X Y U : ℝ} (hQ : 0 < Q) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hU : 0 < U) (a b K j : ℕ) (hK : 1 ≤ K) :
    0 ≤ dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  have hlogK : 0 ≤ Real.log (K : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hK)
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith)
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith)
  have hLXK : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
    positivity
  have hLYK : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
    positivity
  have hKpow : 0 ≤ (K : ℝ) ^ j := by positivity
  have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ := by positivity
  have hQpow : 0 ≤ Q ^ (j - 1) := by positivity
  have hbase : 0 ≤ 6 * min X Y * U := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (le_min (zero_le_one.trans hX) (zero_le_one.trans hY))) hU.le
  have hlogs : 0 ≤
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) :=
    mul_nonneg hLXK hLYK
  have hUpow : 0 ≤ U⁻¹ ^ j := by positivity
  unfold dfiEquation27IntegratedErrorEnvelope
  exact add_nonneg
    (mul_nonneg (mul_nonneg hKpow hQinv) (mul_nonneg hbase hlogs))
    (mul_nonneg (mul_nonneg hKpow hQpow)
      (mul_nonneg hbase (mul_nonneg hlogs hUpow)))

/-- The topological support of the source slice lies in the integer interval
required by equation (18). -/
theorem tsupport_dfiEquation27_sourceSlice_subset_natCeil
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) :
    tsupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
        Set.Icc (-((⌈U⌉₊ : ℕ) : ℝ)) (((⌈U⌉₊ : ℕ) : ℝ)) := by
  have hsupp : tsupport (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) ⊆
      Set.Icc (-U) U := by
    change closure (Function.support (dfiEquation27Slice
      (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x)) ⊆
        Set.Icc (-U) U
    exact (closure_minimal
      (support_dfiEquation27_sourceSlice_subset hφ a b qx qy h x)
      isClosed_Icc)
  intro u hu
  have hUceil : U ≤ ((⌈U⌉₊ : ℕ) : ℝ) := Nat.le_ceil U
  have hu' : u ∈ Set.Icc (-U) U := hsupp hu
  constructor <;> linarith [hu'.1, hu'.2]

/-- Source-facing pointwise form of the approximation used in DFI equation
(27).  Smoothness, compact support, and the support radius are all derived
from equations (2) and (21); none remains as an external premise. -/
theorem dfiEquation27_source_slice_approximation
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h x : ℝ) (q j : ℕ)
    (hq : 0 < q) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ‖dfiEquation12LeftComplex w q
          (dfiEquation27Slice
            (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) -
        dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
          x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ,
              ‖dfiEquation27Slice
                (dfiEquation27C a b qx qy
                  (dfiLocalizedWeight f φ h)) h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j
                (dfiEquation27Slice
                  (dfiEquation27C a b qx qy
                    (dfiLocalizedWeight f φ h)) h x) u‖) := by
  exact dfiEquation27_slice_approximation w q hq
    (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x
    ⌈U⌉₊ j
    (contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x)
    (hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x)
    (tsupport_dfiEquation27_sourceSlice_subset_natCeil
      hφ a b qx qy h x) hj

/-- Uniform source-facing form of the equation-(27) slice estimate.  The
The constant is chosen before the outer variable `x`, which is essential for the
subsequent integration in DFI section 6. -/
theorem dfiEquation27_source_slice_approximation_uniform
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b qx qy : ℕ) (h : ℝ) (q j : ℕ)
    (hq : 0 < q) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      ‖dfiEquation12LeftComplex w q
          (dfiEquation27Slice
            (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) -
        dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
          x (x - h)‖ ≤
        K * ((q : ℝ) ^ j * (Q ^ (j + 1))⁻¹ *
            (∫ u : ℝ,
              ‖dfiEquation27Slice
                (dfiEquation27C a b qx qy
                  (dfiLocalizedWeight f φ h)) h x u‖) +
          (q : ℝ) ^ j * Q ^ (j - 1) *
            ∫ u : ℝ,
              ‖iteratedDeriv j
                (dfiEquation27Slice
                  (dfiEquation27C a b qx qy
                    (dfiLocalizedWeight f φ h)) h x) u‖) := by
  obtain ⟨K, hK, hbound⟩ :=
    dfiEquation18_complex w ⌈U⌉₊ j hj
  refine ⟨K, hK, ?_⟩
  intro x
  simpa [dfiEquation27Slice] using hbound q hq _
      (contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x)
      (hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x)
      (tsupport_dfiEquation27_sourceSlice_subset_natCeil
        hφ a b qx qy h x)

/-- For the source-localized weight, the positive-quadrant physical main
integral is exactly the whole-line affine-slice integral to which equation
(18) applies.  Positivity is derived from the dyadic support, not assumed as
an integration convention. -/
theorem dfiEquation27_physicalMainIntegral_eq_sliceIntegral
    {Q P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (a b qx qy q : ℕ) (h : ℝ) :
    dfiEquation27PhysicalMainIntegral w q a b qx qy
        (dfiLocalizedWeight f φ h) h =
      ∫ x : ℝ, dfiEquation12LeftComplex w q
        (dfiEquation27Slice
          (dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)) h x) := by
  let C : ℝ → ℝ → ℂ :=
    dfiEquation27C a b qx qy (dfiLocalizedWeight f φ h)
  have hinner (x : ℝ) :
      (∫ y in Set.Ioi (0 : ℝ),
          C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)) =
        ∫ y : ℝ, C x y *
          (dfiDeltaKernel w q (x - y - h) : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyNonpos : y ≤ 0 := not_lt.mp hy
    have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
      by_contra hne
      have hp : (x, y) ∈ Function.support
          (Function.uncurry (dfiLocalizedWeight f φ h)) := by
        exact hne
      have hymem := (support_uncurry_dfiLocalizedWeight_subset hbox hp).2
      linarith [hf.one_le_Y, hymem.1]
    simp [C, dfiEquation27C, hlocal]
  have houterZero : ∀ x ∉ Set.Ioi (0 : ℝ),
      (∫ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ)) = 0 := by
    intro x hx
    have hxNonpos : x ≤ 0 := not_lt.mp hx
    have hpoint : ∀ y : ℝ, C x y *
        (dfiDeltaKernel w q (x - y - h) : ℂ) = 0 := by
      intro y
      have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
        by_contra hne
        have hp : (x, y) ∈ Function.support
            (Function.uncurry (dfiLocalizedWeight f φ h)) := by
          exact hne
        have hxmem := (support_uncurry_dfiLocalizedWeight_subset hbox hp).1
        linarith [hf.one_le_X, hxmem.1]
      simp [C, dfiEquation27C, hlocal]
    simp_rw [hpoint]
    simp
  unfold dfiEquation27PhysicalMainIntegral
  change (∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
      C x y * (dfiDeltaKernel w q (x - y - h) : ℂ)) = _
  simp_rw [hinner]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero houterZero]
  exact dfiEquation27_double_change_variables w q C h

/-- Source-facing integrated equation (27).  All smoothness, compact-support,
support-radius, Fubini, and majorant-integrability hypotheses of equation
(18) are discharged from equations (2) and (21). -/
theorem dfiEquation27_source_integrated_approximation
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b qx qy q : ℕ) (h : ℝ), 0 < q →
      ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
          (dfiLocalizedWeight f φ h) h -
        ∫ x : ℝ, dfiEquation27C a b qx qy
          (dfiLocalizedWeight f φ h) x (x - h)‖ ≤
        C * ∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) := by
  obtain ⟨C, hC, hbound⟩ := dfiEquation18_complex_family_integral
    w ⌈U⌉₊ j hj
  refine ⟨C, hC, ?_⟩
  intro a b qx qy q h hq
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hsmooth : ∀ x, ContDiff ℝ ∞ (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x
  have hcompact : ∀ x, HasCompactSupport (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x
  have hsupp : ∀ x, tsupport (g x) ⊆
      Set.Icc (-((⌈U⌉₊ : ℕ) : ℝ)) (((⌈U⌉₊ : ℕ) : ℝ)) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      tsupport_dfiEquation27_sourceSlice_subset_natCeil
        hφ a b qx qy h x
  have hleft : Integrable (fun x => dfiEquation12LeftComplex w q (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_left
      w hf hbox hφ a b qx qy q hq
  have hcenter : Integrable (fun x => g x 0) := by
    simpa only [g] using integrable_dfiEquation27_source_center
      hf hbox hφ a b qx qy
  have hmajor : Integrable (fun x =>
      dfiEquation18ComplexMajorant (Q := Q) q j (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_majorant
      hf hbox hφ a b qx qy q j
  rw [dfiEquation27_physicalMainIntegral_eq_sliceIntegral
    w hf hbox a b qx qy q h]
  simpa [g, dfiEquation27SourceSliceFamily, dfiEquation27Slice] using
    hbound q hq g hsmooth hcompact hsupp hleft hcenter hmajor

/-- Source-facing integrated equation (27) with the equation-(18) constant
selected from scale-uniform cutoff profiles. -/
theorem dfiEquation27_source_integrated_approximation_of_profiles
    {Q P X Y U : ℝ} {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc)
    (a b qx qy q : ℕ) (h : ℝ) (hq : 0 < q) :
    ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
        (dfiLocalizedWeight f φ h) h -
      ∫ x : ℝ, dfiEquation27C a b qx qy
        (dfiLocalizedWeight f φ h) x (x - h)‖ ≤
      (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
        ∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
          (dfiEquation27SourceSliceFamily a b qx qy
            (dfiLocalizedWeight f φ h) h x) := by
  let g : ℝ → ℝ → ℂ := dfiEquation27SourceSliceFamily a b qx qy
    (dfiLocalizedWeight f φ h) h
  have hsmooth : ∀ x, ContDiff ℝ ∞ (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      contDiff_dfiEquation27_sourceSlice hf hbox hφ a b qx qy h x
  have hcompact : ∀ x, HasCompactSupport (g x) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      hasCompactSupport_dfiEquation27_sourceSlice hφ a b qx qy h x
  have hsupp : ∀ x, tsupport (g x) ⊆
      Set.Icc (-((⌈U⌉₊ : ℕ) : ℝ)) (((⌈U⌉₊ : ℕ) : ℝ)) := by
    intro x
    simpa [g, dfiEquation27SourceSliceFamily] using
      tsupport_dfiEquation27_sourceSlice_subset_natCeil
        hφ a b qx qy h x
  have hleft : Integrable (fun x => dfiEquation12LeftComplex w q (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_left
      w hf hbox hφ a b qx qy q hq
  have hcenter : Integrable (fun x => g x 0) := by
    simpa only [g] using integrable_dfiEquation27_source_center
      hf hbox hφ a b qx qy
  have hmajor : Integrable (fun x =>
      dfiEquation18ComplexMajorant (Q := Q) q j (g x)) := by
    simpa only [g] using integrable_dfiEquation27_source_majorant
      hf hbox hφ a b qx qy q j
  have hbound := dfiEquation18_complex_family_integral_of_profiles
    hD hEprofile ⌈U⌉₊ j hj hCpsi hpsi hCpsiSucc hpsiSucc
      q hq g hsmooth hcompact hsupp hleft hcenter hmajor
  rw [dfiEquation27_physicalMainIntegral_eq_sliceIntegral
    w hf hbox a b qx qy q h]
  simpa [g, dfiEquation27SourceSliceFamily, dfiEquation27Slice] using hbound

/-- Compatibility between the integer-frequency Ramanujan sum used by the
delta symbol and the natural-frequency Kloosterman specialization used in
DFI equations (24)--(27). -/
theorem ramanujanSumInt_ofNat_eq_ramanujanSum
    (q h : ℕ) [NeZero q] :
    ramanujanSumInt q h = ramanujanSum q h := by
  have hq : 0 < q := NeZero.pos q
  unfold ramanujanSumInt ramanujanSum kloostermanSum
  simp only [hq.ne', dite_false]
  simpa using sum_range_coprime_eq_sum_zmod_units q
    (fun z => ZMod.stdAddChar ((h : ZMod q) * z))

/-- The arithmetic coefficient of the main integral in DFI equation (27).
The zero modulus is defined to contribute zero, so the complete series can
be indexed by all natural numbers. -/
noncomputable def dfiEquation27ArithmeticCoefficient
    (a b h q : ℕ) : ℂ :=
  if q = 0 then 0 else
    ((Nat.gcd (a * b) q : ℂ) / (q : ℂ) ^ 2) * ramanujanSumInt q h

theorem dfiEquation27ArithmeticCoefficient_zero
    (a b h : ℕ) :
    dfiEquation27ArithmeticCoefficient a b h 0 = 0 := by
  simp [dfiEquation27ArithmeticCoefficient]

theorem dfiEquation27ArithmeticCoefficient_eq
    (a b h q : ℕ) [NeZero q] :
    dfiEquation27ArithmeticCoefficient a b h q =
      ((Nat.gcd (a * b) q : ℂ) / (q : ℂ) ^ 2) * ramanujanSum q h := by
  have hq : 0 < q := NeZero.pos q
  simp only [dfiEquation27ArithmeticCoefficient, hq.ne', if_false]
  rw [ramanujanSumInt_ofNat_eq_ramanujanSum q h]

/-- Equation (26) gives the exact arithmetic majorant needed for the tail
of the main series in equation (27). -/
theorem norm_dfiEquation27ArithmeticCoefficient_le
    (a b h q : ℕ) [NeZero q] :
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
        ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := by
  rw [dfiEquation27ArithmeticCoefficient_eq]
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_natCast]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hram := norm_ramanujanSum_le_gcd_mul_divisors q h
  calc
    ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
        ‖ramanujanSum q h‖ ≤
      ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
        ((Nat.gcd h q : ℝ) *
          ((Nat.gcd h q).divisors.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hram (by positivity)
    _ = (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
        ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := by
      field_simp

/-- For a nonzero shift, the equation-(26) arithmetic coefficient has the
uniform inverse-square majorant used to sum the large-modulus part of DFI
equation (27).  The constant is deliberately elementary: both gcd factors
and the divisor count are bounded by their fixed source arguments. -/
theorem norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) [NeZero q] :
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      ((a * b * h ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
  have hbase := norm_dfiEquation27ArithmeticCoefficient_le a b h q
  have hab : Nat.gcd (a * b) q ≤ a * b :=
    Nat.gcd_le_left _ (Nat.mul_pos ha hb)
  have hhgcd : Nat.gcd h q ≤ h := Nat.gcd_le_left _ hh
  have hcard : (Nat.gcd h q).divisors.card ≤ Nat.gcd h q :=
    Nat.card_divisors_le_self _
  have hqnonneg : 0 ≤ ((q : ℝ) ^ 2)⁻¹ := by positivity
  calc
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
        (Nat.gcd (a * b) q : ℝ) * (Nat.gcd h q : ℝ) *
          ((Nat.gcd h q).divisors.card : ℝ) / (q : ℝ) ^ 2 := hbase
    _ ≤ ((a * b : ℕ) : ℝ) * (h : ℝ) * (h : ℝ) / (q : ℝ) ^ 2 := by
      have habR : (Nat.gcd (a * b) q : ℝ) ≤ (a * b : ℕ) := by exact_mod_cast hab
      have hhR : (Nat.gcd h q : ℝ) ≤ h := by exact_mod_cast hhgcd
      have hcR : ((Nat.gcd h q).divisors.card : ℝ) ≤ Nat.gcd h q := by
        exact_mod_cast hcard
      have hch : ((Nat.gcd h q).divisors.card : ℝ) ≤ h := hcR.trans hhR
      gcongr
    _ = ((a * b * h ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
      push_cast
      rw [div_eq_mul_inv]
      ring

/-- The full equation-(27) arithmetic coefficient series is absolutely
summable for every nonzero shift. -/
theorem summable_norm_dfiEquation27ArithmeticCoefficient
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    Summable (fun q : ℕ => ‖dfiEquation27ArithmeticCoefficient a b h q‖) := by
  have hsquare : Summable (fun q : ℕ => ((q : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have hmajor := hsquare.mul_left (((a * b * h ^ 2 : ℕ) : ℝ))
  apply Summable.of_norm_bounded hmajor
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hq : q = 0
  · subst q
    simp [dfiEquation27ArithmeticCoefficient]
  · letI : NeZero q := ⟨hq⟩
    exact norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b h q ha hb hh

/-- Quantitative finite-tail form of the preceding summability theorem.
This is the exact estimate used when equation (30) supplies a uniform bound
for the modulus-dependent main integral in the range discarded from (27). -/
theorem norm_sum_Ioo_dfiEquation27ArithmeticCoefficient_mul_le
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (I : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hI : ∀ q ∈ Finset.Ioo K L, ‖I q‖ ≤ B) :
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
      ((a * b * h ^ 2 : ℕ) : ℝ) * B * (2 / (K + 1 : ℝ)) := by
  let C : ℝ := ((a * b * h ^ 2 : ℕ) : ℝ)
  have hC : 0 ≤ C := by positivity
  calc
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
        ∑ q ∈ Finset.Ioo K L,
          ‖dfiEquation27ArithmeticCoefficient a b h q * I q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioo K L, (C * ((q : ℝ) ^ 2)⁻¹) * B := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      have hq0 : q ≠ 0 := by
        intro hzero
        subst q
        simp at hq
      letI : NeZero q := ⟨hq0⟩
      exact mul_le_mul
        (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b h q ha hb hh)
        (hI q hq) (norm_nonneg _) (mul_nonneg hC (by positivity))
    _ = C * B * (∑ q ∈ Finset.Ioo K L, ((q : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ C * B * (2 / (K + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_inv_sq_le K L) (mul_nonneg hC hB)
    _ = ((a * b * h ^ 2 : ℕ) : ℝ) * B * (2 / (K + 1 : ℝ)) := rfl

/-- Source-strength equation-(27) arithmetic tail.  Unlike the elementary
`h²` majorant above, this proof expands the Ramanujan sum by equation (26)
and sums each divisor only over the moduli divisible by it.  The resulting
loss is `d(h)` times one harmonic factor, exactly the loss absorbed by
DFI's epsilon convention. -/
theorem sum_Ioo_norm_dfiEquation27ArithmeticCoefficient_le
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    (∑ q ∈ Finset.Ioo K L,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      ((a * b : ℕ) : ℝ) * (h.divisors.card : ℝ) *
        ((1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ)) := by
  let A : ℝ := ((a * b : ℕ) : ℝ)
  have hA : 0 ≤ A := by positivity
  calc
    ∑ q ∈ Finset.Ioo K L,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
        ∑ q ∈ Finset.Ioo K L,
          A * (∑ d ∈ h.divisors,
            if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqIoo := Finset.mem_Ioo.mp hq
      have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [dfiEquation27ArithmeticCoefficient_eq]
      rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
        Complex.norm_natCast]
      have hram := norm_ramanujanSum_le_sum_divisors_filter_dvd
        q h hh.ne'
      have hgcd : (Nat.gcd (a * b) q : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast Nat.gcd_le_left q (Nat.mul_pos ha hb)
      have hqSq : 0 < (q : ℝ) ^ 2 := by positivity
      calc
        ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
            ‖ramanujanSum q h‖ ≤
            (A / (q : ℝ) ^ 2) *
              (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0) := by
          exact mul_le_mul
            (div_le_div_of_nonneg_right hgcd hqSq.le) hram
            (norm_nonneg _) (div_nonneg hA hqSq.le)
        _ = A * (∑ d ∈ h.divisors,
            if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdq : d ∣ q
          · simp only [hdq, ↓reduceIte]
            field_simp
          · simp [hdq]
    _ = A * (∑ d ∈ h.divisors,
        ∑ q ∈ Finset.Ioo K L,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ A * (∑ d ∈ h.divisors,
        ((1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ))) := by
      gcongr with d hd
      exact sum_Ioo_dvd_weighted_inv_sq_le K L d
        (Nat.pos_of_mem_divisors hd)
    _ = ((a * b : ℕ) : ℝ) * (h.divisors.card : ℝ) *
        ((1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ)) := by
      simp [A, mul_assoc]

/-- Epsilon-power form of the equation-(27) arithmetic tail.  Its constant
is explicit and depends only on `ε`; there is no polynomial dependence on
the shift `h`. -/
theorem sum_Ioo_norm_dfiEquation27ArithmeticCoefficient_le_epsilon
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ q ∈ Finset.Ioo K L,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
        ((1 / (K + 1 : ℝ)) *
          ((1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε))) := by
  have hTail := sum_Ioo_norm_dfiEquation27ArithmeticCoefficient_le
    a b h K L ha hb hh
  have hDiv := card_divisors_le_const_mul_rpow hε hh.ne'
  have hHarm := harmonic_le_epsilon_rpow hε L
  have hHnonneg : 0 ≤ ((harmonic L : ℚ) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  have hCpos := divisorEpsilonConstant_pos ε
  calc
    (∑ q ∈ Finset.Ioo K L,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
        ((a * b : ℕ) : ℝ) * (h.divisors.card : ℝ) *
          ((1 / (K + 1 : ℝ)) * ((harmonic L : ℚ) : ℝ)) := hTail
    _ ≤ ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
        ((1 / (K + 1 : ℝ)) *
          ((1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε))) := by
      gcongr

/-- The source-strength arithmetic tail remains valid after multiplication
by a uniformly bounded family of physical main integrals. -/
theorem norm_sum_Ioo_dfiEquation27ArithmeticCoefficient_mul_le_epsilon
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε : 0 < ε) (I : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hI : ∀ q ∈ Finset.Ioo K L, ‖I q‖ ≤ B) :
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
      ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
        ((1 / (K + 1 : ℝ)) *
          ((1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε))) * B := by
  calc
    ‖∑ q ∈ Finset.Ioo K L,
        dfiEquation27ArithmeticCoefficient a b h q * I q‖ ≤
        ∑ q ∈ Finset.Ioo K L,
          ‖dfiEquation27ArithmeticCoefficient a b h q * I q‖ :=
      norm_sum_le _ _
    _ ≤ (∑ q ∈ Finset.Ioo K L,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) * B := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hI q hq) (norm_nonneg _)
    _ ≤ (((a * b : ℕ) : ℝ) *
          (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
          ((1 / (K + 1 : ℝ)) *
            ((1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε)))) * B := by
      exact mul_le_mul_of_nonneg_right
        (sum_Ioo_norm_dfiEquation27ArithmeticCoefficient_le_epsilon
          a b h K L ha hb hh hε) hB
    _ = ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
        ((1 / (K + 1 : ℝ)) *
          ((1 + ε⁻¹) * max 1 ((L : ℝ) ^ ε))) * B := rfl

/-- The small-modulus part of source equation (27), summed with one constant
uniform in every active modulus.  This is the finite summation step that
would be invalid if the equation-(18) constant were selected after `q`.
The remaining right-hand side is exactly the integrated derivative
majorant that equation (2) must make rapidly decreasing. -/
theorem norm_sum_Icc_dfiEquation27_source_main_error_le_of_profiles
    {Q P X Y U : ℝ} {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc) :
      ∀ (a b h K : ℕ) (qx qy : ℕ → ℕ),
      ‖∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
          ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
              (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
  have happrox := dfiEquation27_source_integrated_approximation_of_profiles
    hD hEprofile hf hbox hφ j hj hCpsi hpsi hCpsiSucc hpsiSucc
  intro a b h K qx qy
  calc
    ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q *
          (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
            dfiEquation27CentralIntegral a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ((2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
            ∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
            (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [dfiEquation27CentralIntegral] using
        happrox a b (qx q) (qy q) q (h : ℝ) hqpos
    _ = (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
        ∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
            (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Compatibility form using the intrinsic compact-support constants of an
arbitrary fixed delta weight.  Uniform family arguments should use the
profile-controlled theorem above. -/
theorem norm_sum_Icc_dfiEquation27_source_main_error_le
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h K : ℕ) (qx qy : ℕ → ℕ),
      ‖∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        C * ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
              (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
  obtain ⟨C, hC, happrox⟩ :=
    dfiEquation27_source_integrated_approximation w hf hbox hφ j hj
  refine ⟨C, hC, ?_⟩
  intro a b h K qx qy
  calc
    ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q *
          (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
            dfiEquation27CentralIntegral a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b (qx q) (qy q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          (C * ∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
            (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [dfiEquation27CentralIntegral] using
        happrox a b (qx q) (qy q) q (h : ℝ) hqpos
    _ = C * ∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
            (dfiEquation27SourceSliceFamily a b (qx q) (qy q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- The fully source-specialized small-modulus error in equation (27).
Both reduced denominators are the actual denominators of `a/q` and `b/q`,
and the analytic envelope has been pulled outside the finite arithmetic
sum.  The remaining coefficient sum is treated arithmetically by equation
(26). -/
theorem norm_sum_Icc_dfiEquation27_reduced_main_error_le_of_profiles
    {Q P X Y U : ℝ} (hQ : 0 < Q) {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc) :
    ∀ (a b h K : ℕ), 1 ≤ K →
      ‖∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        ((2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
          dfiEquation27SourceMajorantConstant Cf Cφ j) *
          (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  let Cδ : ℝ := 2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc
  let Cs : ℝ := dfiEquation27SourceMajorantConstant Cf Cφ j
  have hCδ : 0 < Cδ := by
    dsimp [Cδ]
    exact mul_pos two_pos (dfiEquation18ProfileConstant_pos
      hD.positive hEprofile.positive j hCpsi hCpsiSucc)
  have hCs : 0 < Cs := by
    simpa only [Cs] using dfiEquation27SourceMajorantConstant_pos hfC hφC j
  have hδ := norm_sum_Icc_dfiEquation27_source_main_error_le_of_profiles
    hD hEprofile hf hbox hφ j hj hCpsi hpsi hCpsiSucc hpsiSucc
  have hs := integral_dfiEquation18ComplexMajorant_reduced_Icc_le
    hQ hf hfC hbox hφ hφC hscale j
  intro a b h K hK
  have hraw := hδ a b h K
    (fun q => dfiReducedDenominator a q)
    (fun q => dfiReducedDenominator b q)
  have henvNonneg :
      0 ≤ dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
    have hlogK : 0 ≤ Real.log (K : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hK)
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    have hX : 0 ≤ X := zero_le_one.trans hf.one_le_X
    have hU : 0 ≤ U := hφ.U_pos.le
    have hLXK : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
      positivity
    have hLYK : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
      positivity
    have hX : 0 ≤ X := zero_le_one.trans hf.one_le_X
    have hU : 0 ≤ U := hφ.U_pos.le
    have hKpow : 0 ≤ (K : ℝ) ^ j := by positivity
    have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ := by positivity
    have hQpow : 0 ≤ Q ^ (j - 1) := by positivity
    have hbase : 0 ≤ 6 * min X Y * U := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (le_min (zero_le_one.trans hf.one_le_X)
            (zero_le_one.trans hf.one_le_Y))) hφ.U_pos.le
    have hlogs : 0 ≤
        (1 + Real.log (2 * X) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
        (1 + Real.log (2 * Y) + |Real.log b| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) :=
      mul_nonneg hLXK hLYK
    have hUpow : 0 ≤ U⁻¹ ^ j := by
      exact pow_nonneg (inv_nonneg.mpr hU) _
    unfold dfiEquation27IntegratedErrorEnvelope
    exact add_nonneg
      (mul_nonneg (mul_nonneg hKpow hQinv) (mul_nonneg hbase hlogs))
      (mul_nonneg (mul_nonneg hKpow hQpow)
        (mul_nonneg hbase (mul_nonneg hlogs hUpow)))
  have hpoint : ∀ q ∈ Finset.Icc 1 K,
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) ≤
        Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
    intro q hq
    have hqbound := hs (h : ℝ) a b K q hq
    unfold dfiEquation27IntegratedErrorEnvelope
    exact hqbound.trans_eq (by ring)
  calc
    ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q *
          (dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
            dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        Cδ * ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
              (dfiEquation27SourceSliceFamily a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := hraw
    _ ≤ Cδ * ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
      apply mul_le_mul_of_nonneg_left _ hCδ.le
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hpoint q hq) (norm_nonneg _)
    _ = ((2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
          dfiEquation27SourceMajorantConstant Cf Cφ j) *
        (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
      have hsum :
          (∑ q ∈ Finset.Icc 1 K,
              ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
                (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j)) =
            (∑ q ∈ Finset.Icc 1 K,
              ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
                (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
        rw [Finset.sum_mul]
      rw [hsum]
      simp only [Cδ, Cs]
      ring

/-- Compatibility form for a fixed delta weight.  The profile-controlled
variant above is the form used to obtain constants uniform in `Q`. -/
theorem norm_sum_Icc_dfiEquation27_reduced_main_error_le
    {Q P X Y U : ℝ} (hQ : 0 < Q) (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b h K : ℕ), 1 ≤ K →
      ‖∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        C * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  obtain ⟨Cδ, hCδ, hδ⟩ :=
    norm_sum_Icc_dfiEquation27_source_main_error_le w hf hbox hφ j hj
  obtain ⟨Cs, hCs, hs⟩ :=
    exists_integral_dfiEquation18ComplexMajorant_reduced_Icc_le
      hQ hf hfC hbox hφ hφC hscale j
  refine ⟨Cδ * Cs, mul_pos hCδ hCs, ?_⟩
  intro a b h K hK
  have hraw := hδ a b h K
    (fun q => dfiReducedDenominator a q)
    (fun q => dfiReducedDenominator b q)
  have henvNonneg :
      0 ≤ dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
    have hlogK : 0 ≤ Real.log (K : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hK)
    have hlogX : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    have hlogY : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    have hLXK : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
      positivity
    have hLYK : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log K := by
      positivity
    have hU : 0 ≤ U := hφ.U_pos.le
    have hKpow : 0 ≤ (K : ℝ) ^ j := by positivity
    have hQinv : 0 ≤ (Q ^ (j + 1))⁻¹ := by positivity
    have hQpow : 0 ≤ Q ^ (j - 1) := by positivity
    have hbase : 0 ≤ 6 * min X Y * U := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (le_min (zero_le_one.trans hf.one_le_X)
            (zero_le_one.trans hf.one_le_Y))) hφ.U_pos.le
    have hlogs : 0 ≤
        (1 + Real.log (2 * X) + |Real.log a| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) *
        (1 + Real.log (2 * Y) + |Real.log b| +
          2 * |Real.eulerMascheroniConstant| + 2 * Real.log K) :=
      mul_nonneg hLXK hLYK
    have hUpow : 0 ≤ U⁻¹ ^ j :=
      pow_nonneg (inv_nonneg.mpr hU) _
    unfold dfiEquation27IntegratedErrorEnvelope
    exact add_nonneg
      (mul_nonneg (mul_nonneg hKpow hQinv) (mul_nonneg hbase hlogs))
      (mul_nonneg (mul_nonneg hKpow hQpow)
        (mul_nonneg hbase (mul_nonneg hlogs hUpow)))
  have hpoint : ∀ q ∈ Finset.Icc 1 K,
      (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
        (dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) ≤
        Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
    intro q hq
    have hqbound := hs (h : ℝ) a b K q hq
    unfold dfiEquation27IntegratedErrorEnvelope
    exact hqbound.trans_eq (by ring)
  calc
    ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q *
          (dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
            dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        Cδ * ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (∫ x : ℝ, dfiEquation18ComplexMajorant (Q := Q) q j
              (dfiEquation27SourceSliceFamily a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) x)) := hraw
    _ ≤ Cδ * ∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
      apply mul_le_mul_of_nonneg_left _ hCδ.le
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hpoint q hq) (norm_nonneg _)
    _ = (Cδ * Cs) * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
      have hsum :
          (∑ q ∈ Finset.Icc 1 K,
              ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
                (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j)) =
            (∑ q ∈ Finset.Icc 1 K,
              ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
                (Cs * dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
        rw [Finset.sum_mul]
      rw [hsum]
      ring

/-- Equation-(26) bound for the complete initial modulus interval.  This is
the `K = 0`, `L = K+1` specialization of the divisor-by-divisor harmonic
summation, rewritten from `Ioo 0 (K+1)` to `Icc 1 K`. -/
theorem sum_Icc_norm_dfiEquation27ArithmeticCoefficient_le_epsilon
    (a b h K : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
        ((1 + ε⁻¹) * max 1 (((K + 1 : ℕ) : ℝ) ^ ε)) := by
  have hraw :=
    sum_Ioo_norm_dfiEquation27ArithmeticCoefficient_le_epsilon
      a b h 0 (K + 1) ha hb hh hε
  have hinterval : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by
    ext q
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [hinterval] at hraw
  simpa using hraw

/-- Source-strength small-modulus equation-(27) error after both the analytic
and arithmetic finite sums have been discharged. -/
theorem norm_sum_Icc_dfiEquation27_reduced_main_error_le_epsilon
    {Q P X Y U : ℝ} (hQ : 0 < Q) (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (j : ℕ) (hj : 2 ≤ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h K : ℕ), 0 < a → 0 < b → 0 < h → 1 ≤ K →
      ‖∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q *
            (dfiEquation27PhysicalMainIntegral w q a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        C * (((a * b : ℕ) : ℝ) *
          (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
          ((1 + ε⁻¹) * max 1 (((K + 1 : ℕ) : ℝ) ^ ε))) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  obtain ⟨C, hC, hmain⟩ :=
    norm_sum_Icc_dfiEquation27_reduced_main_error_le
      hQ w hf hfC hbox hφ hφC hscale j hj
  refine ⟨C, hC, ?_⟩
  intro a b h K ha hb hh hK
  have harith :=
    sum_Icc_norm_dfiEquation27ArithmeticCoefficient_le_epsilon
      a b h K ha hb hh hε
  have henv := dfiEquation27IntegratedErrorEnvelope_nonneg
    hQ hf.one_le_X hf.one_le_Y hφ.U_pos a b K j hK
  exact (hmain a b h K hK).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left harith hC.le) henv)

end RiemannZeta.GuthMaynard
