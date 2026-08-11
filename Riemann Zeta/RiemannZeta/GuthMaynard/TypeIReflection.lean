import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MellinInversion
import RiemannZeta.GuthMaynard.LargeValuesReflection
import RiemannZeta.GuthMaynard.MediumReflection
import RiemannZeta.GuthMaynard.TypeISmoothing

open Complex Filter MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

namespace RiemannZeta.GuthMaynard

/-!
# Exact smooth Type-I Poisson reflection

This file is the literal analytic bridge from the smooth source block to its
Poisson modes.  Negative Fourier frequency `-m` has phase
`m*x - t/(2π)*log x`; its stationary point is therefore `t/(2πm)`, and the
stationary frequencies have scale `t/(2^r Y)`.
-/

/-! ## Mellin transform of the actual Type-I cutoff

The exact Mellin route is the formal replacement for appealing to an
unavailable black-box stationary-phase theorem.  It keeps the fixed cutoff
as a Schwartz transform and leaves one common logarithmic reflection
integral, which is controlled by the weighted B-process estimate in
`LargeValuesReflection.lean`.
-/

private noncomputable def typeIDyadicCutoffComplex (x : ℝ) : ℂ :=
  (typeIDyadicCutoff x : ℂ)

private theorem contDiff_typeIDyadicCutoffComplex :
    ContDiff ℝ ∞ typeIDyadicCutoffComplex := by
  exact Complex.ofRealCLM.contDiff.comp contDiff_typeIDyadicCutoff

private theorem hasCompactSupport_typeIDyadicCutoffComplex :
    HasCompactSupport typeIDyadicCutoffComplex := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 2 : ℝ) 2))
  intro x hx
  by_cases hhalf : x ≤ 1 / 2
  · simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_le_half hhalf]
  · have htwo : 2 ≤ x := by
      by_contra hnot
      exact hx ⟨le_of_not_ge hhalf, le_of_not_ge hnot⟩
    simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_two_le htwo]

theorem mellinConvergent_typeIDyadicCutoff_one :
    MellinConvergent typeIDyadicCutoffComplex (1 : ℂ) := by
  rw [MellinConvergent]
  have hInt : Integrable typeIDyadicCutoffComplex volume :=
    contDiff_typeIDyadicCutoffComplex.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_typeIDyadicCutoffComplex
  simpa using hInt.integrableOn

/-- Logarithmic-coordinate Schwartz kernel for the literal cutoff used in
the #15 smooth partition. -/
noncomputable def typeIDyadicMellinKernel (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * typeIDyadicCutoffComplex (Real.exp (-u))

theorem contDiff_typeIDyadicMellinKernel :
    ContDiff ℝ ∞ typeIDyadicMellinKernel := by
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_neg
  exact (Complex.ofRealCLM.contDiff.comp hExp).mul
    (contDiff_typeIDyadicCutoffComplex.comp hExp)

theorem hasCompactSupport_typeIDyadicMellinKernel :
    HasCompactSupport typeIDyadicMellinKernel := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (-Real.log 2) (Real.log 2)))
  intro u hu
  have hcut : typeIDyadicCutoff (Real.exp (-u)) = 0 := by
    by_cases hleft : u < -Real.log 2
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      have hlog : Real.log 2 < -u := by linarith
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact (Real.exp_lt_exp).mpr hlog |>.le
    · have hright : Real.log 2 < u := by
        by_contra hnot
        exact hu ⟨le_of_not_gt hleft, le_of_not_gt hnot⟩
      apply typeIDyadicCutoff_eq_zero_of_le_half
      have hneg : -u < -Real.log 2 := by linarith
      rw [Real.exp_neg]
      have hinv : (Real.exp u)⁻¹ ≤ (2 : ℝ)⁻¹ := by
        apply (inv_le_inv₀ (Real.exp_pos u) (by norm_num : (0 : ℝ) < 2)).2
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact (Real.exp_lt_exp).mpr hright |>.le
      simpa only [inv_eq_one_div] using hinv
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex, hcut]

/-- Schwartz realization of the logarithmic cutoff. -/
noncomputable def typeIDyadicMellinSchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_typeIDyadicMellinKernel.toSchwartzMap
    contDiff_typeIDyadicMellinKernel

@[simp]
theorem typeIDyadicMellinSchwartz_apply (u : ℝ) :
    typeIDyadicMellinSchwartz u = typeIDyadicMellinKernel u := rfl

/-- Mellin transform of the fixed Type-I cutoff on `Re s = 1`. -/
noncomputable def typeIDyadicCutoffMellin (r : ℝ) : ℂ :=
  mellin typeIDyadicCutoffComplex ((1 : ℂ) + (r : ℂ) * I)

theorem typeIDyadicCutoffMellin_eq_fourier (r : ℝ) :
    typeIDyadicCutoffMellin r =
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
  unfold typeIDyadicCutoffMellin
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (r / (2 * Real.pi)))
  funext u
  rw [typeIDyadicMellinSchwartz_apply]
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex,
    Complex.ofReal_exp]

theorem continuous_typeIDyadicCutoffMellin :
    Continuous typeIDyadicCutoffMellin := by
  have hEq : typeIDyadicCutoffMellin = fun r : ℝ =>
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
    funext r
    exact typeIDyadicCutoffMellin_eq_fourier r
  rw [hEq]
  exact (𝓕 typeIDyadicMellinSchwartz).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

theorem verticalIntegrable_typeIDyadicCutoffMellin :
    VerticalIntegrable (mellin typeIDyadicCutoffComplex) 1 := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 typeIDyadicMellinSchwartz
  have hFourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hScaled : Integrable
      (fun u : ℝ => 𝓕 typeIDyadicMellinSchwartz
        (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right'
        (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  exact (typeIDyadicCutoffMellin_eq_fourier u).symm

/-- Exact pointwise Mellin inversion for the actual #15 dyadic cutoff. -/
theorem typeIDyadicCutoff_mellinInversion {x : ℝ} (hx : 0 < x) :
    mellinInv 1 (mellin typeIDyadicCutoffComplex) x =
      (typeIDyadicCutoff x : ℂ) := by
  exact mellinInv_mellin_eq 1 typeIDyadicCutoffComplex hx
    mellinConvergent_typeIDyadicCutoff_one
    verticalIntegrable_typeIDyadicCutoffMellin
    contDiff_typeIDyadicCutoffComplex.continuous.continuousAt

/-- Vertical-line form used inside the exact Type-I reflection formula. -/
theorem typeIDyadicCutoff_eq_verticalMellinIntegral
    {x : ℝ} (hx : 0 < x) :
    (typeIDyadicCutoff x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + (r : ℂ) * I)) *
            typeIDyadicCutoffMellin r := by
  rw [← typeIDyadicCutoff_mellinInversion hx]
  unfold mellinInv typeIDyadicCutoffMellin
  simp only [smul_eq_mul]
  norm_num

/-- Raw two-variable integrand obtained by inserting exact Mellin inversion
after the change of variables `v = m*x`. -/
noncomputable def typeIMellinReflectionIntegrand
    (sigma t q v r : ℝ) : ℂ :=
  (v / q : ℂ)⁻¹ *
    Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I)) *
      typeIDyadicCutoffMellin r *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))

/-- Pointwise insertion of the literal cutoff's Mellin inversion into the
rescaled logarithmic phase. -/
theorem typeIDyadicCutoffPhase_eq_mellinIntegral
    (sigma t q : ℝ) {v : ℝ} (hv : 0 < v) (hq : 0 < q) :
    (typeIDyadicCutoff (v / q) : ℂ) *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
  have hratio : 0 < v / q := div_pos hv hq
  rw [typeIDyadicCutoff_eq_verticalMellinIntegral hratio]
  rw [smul_mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  funext r
  unfold typeIMellinReflectionIntegrand typeIDyadicCutoffMellin
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have hExpLog :
      Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  have hsplit :
      (Real.log (v / q) : ℂ) * -((1 : ℂ) + (r : ℂ) * I) =
        -(Real.log (v / q) : ℂ) +
          -(((r * Real.log (v / q) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, hExpLog]
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hRatioInvC : ((v : ℂ) / (q : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  rw [hRatioInv]
  rw [hRatioInvC]

/-- Algebraic factorization of the raw Mellin integrand.  All dependence on
the cutoff dilation `q` is outside the common weighted logarithmic kernel. -/
theorem typeIMellinReflectionIntegrand_eq_factored
    (sigma t : ℝ) {q v : ℝ} (r : ℝ) (hq : 0 < q) (hv : 0 < v) :
    typeIMellinReflectionIntegrand sigma t q v r =
      (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
        typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            star ((v : ℂ)⁻¹ * Complex.exp
              (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
  unfold typeIMellinReflectionIntegrand
  have hlog : Real.log (v / q) = Real.log v - Real.log q :=
    Real.log_div hv.ne' hq.ne'
  rw [hlog]
  have hRatioInv : ((v : ℂ) / (q : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  rw [hRatioInv]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
  rw [← Complex.ofReal_log hq.le]
  have hstar :
      star ((v : ℂ)⁻¹ * Complex.exp
        (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        (v : ℂ)⁻¹ * Complex.exp
          (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    rw [Complex.star_def, map_mul, map_inv₀, conj_ofReal,
      ← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring_nf
  rw [hstar]
  have hExpEq :
      Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          Complex.exp
            (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (q : ℂ) * (v : ℂ)⁻¹ *
          Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
        (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      ring
    _ = (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
            Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      rw [hExpEq]
    _ = (q : ℂ) * Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            ((v : ℂ)⁻¹ * Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) := by
      ring

/-- Absolute integrability needed to exchange the finite physical interval
with the complete Mellin line.  Compactness of the physical interval and
Schwartz decay of the literal cutoff are both used explicitly. -/
theorem integrable_typeIMellinReflectionIntegrand
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (Function.uncurry
      (typeIMellinReflectionIntegrand sigma t q))
      ((volume.restrict (Set.uIoc A B)).prod volume) := by
  have hH : Integrable typeIDyadicCutoffMellin := by
    simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_typeIDyadicCutoffMellin
  let C : ℝ := (q / A) * A ^ (-sigma)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hConst : Integrable (fun _v : ℝ => C)
      (volume.restrict (Set.uIoc A B)) := by
    exact MeasureTheory.integrableOn_const (hs := by simp)
  have hDom := hConst.mul_prod hH.norm
  apply hDom.mono'
  · have hElementary : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (z.1 / q : ℂ)⁻¹ *
            Complex.exp (-(((z.2 * Real.log (z.1 / q) : ℝ) : ℂ) * I)) *
              (gmReflectionPowerWeight sigma z.1 *
                Complex.exp
                  (-((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))))
        ((volume.restrict (Set.uIoc A B)).prod volume) := by
      apply StronglyMeasurable.aestronglyMeasurable
      unfold gmReflectionPowerWeight
      measurability
    exact (hElementary.mul (hH.aestronglyMeasurable.comp_snd)).congr
      (Filter.Eventually.of_forall fun z => by
        simp [typeIMellinReflectionIntegrand, Function.uncurry_def]
        ring)
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ =>
            typeIDyadicCutoffMellin z.2 :=
          continuous_typeIDyadicCutoffMellin.measurable.comp measurable_snd
        unfold typeIMellinReflectionIntegrand Function.uncurry
        unfold gmReflectionPowerWeight
        measurability
      · exact ((continuous_typeIDyadicCutoffMellin.norm.comp continuous_snd
          |>.const_mul C)).measurable)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with v hv
    filter_upwards with r
    have hvIoc : v ∈ Set.Ioc A B := by
      simpa only [Set.uIoc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans hvIoc.1
    have hqv : q / v ≤ q / A := by
      exact div_le_div_of_nonneg_left hq.le hA hvIoc.1.le
    have hpow : v ^ (-sigma) ≤ A ^ (-sigma) := by
      exact Real.rpow_le_rpow_of_nonpos hA hvIoc.1.le (by linarith)
    have hNormRatio : ‖(v : ℂ) / (q : ℂ)‖⁻¹ = q / v := by
      rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hvPos,
        abs_of_pos hq, inv_div]
    have hNormMellinPhase :
        ‖Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hNormReflectionPhase :
        ‖Complex.exp
          (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [show ‖Function.uncurry
        (typeIMellinReflectionIntegrand sigma t q) (v, r)‖ =
        (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) by
      unfold typeIMellinReflectionIntegrand Function.uncurry
      simp only [norm_mul, norm_inv]
      rw [hNormRatio, hNormMellinPhase, hNormReflectionPhase,
        norm_gmReflectionPowerWeight hvPos]
      ring]
    change (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
      C * ‖typeIDyadicCutoffMellin r‖
    dsimp only [C]
    calc
      (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
          (q / A) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) := by
        gcongr
      _ ≤ (q / A) * ‖typeIDyadicCutoffMellin r‖ * A ^ (-sigma) := by
        gcongr
      _ = q / A * A ^ (-sigma) * ‖typeIDyadicCutoffMellin r‖ := by
        ring

/-- Common conjugated power-weighted reflection integral produced by the
exact Mellin transform. -/
noncomputable def typeIPowerReflectionIntegral
    (sigma tau A B : ℝ) : ℂ :=
  ∫ v in A..B,
    gmReflectionPowerWeight sigma v *
      star ((v : ℂ)⁻¹ * Complex.exp
        (((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- Uniform weighted B-process bound for the common integral in the exact
Mellin reflection formula. -/
theorem norm_typeIPowerReflectionIntegral_le
    {sigma tau A B : ℝ} (htau : 1 ≤ tau)
    (hA : 0 < A) (hAB : A ≤ B) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  simpa only [typeIPowerReflectionIntegral] using
    norm_conj_powerWeighted_gmReflectionIntegral_le htau hA hAB

/-- Exact Mellin form of the rescaled medium Type-I integral.  The right
side has one common weighted logarithmic reflection integral; the mode scale
`q` appears only in explicit unitary/Mellin factors. -/
theorem typeIDyadicRescaledIntegral_eq_mellinReflection
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
  calc
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      ∫ v in A..B,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hvIcc : v ∈ Set.Icc A B := by
          simpa only [Set.uIcc_of_le hAB] using hv
        exact typeIDyadicCutoffPhase_eq_mellinIntegral sigma t q
          (hA.trans_le hvIcc.1) hq
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ v in A..B,
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [intervalIntegral.integral_smul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [MeasureTheory.intervalIntegral_integral_swap
          (integrable_typeIMellinReflectionIntegrand hsigma hq hA hAB)]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold typeIPowerReflectionIntegral
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        have hvIcc : v ∈ Set.Icc A B := by
          simpa only [Set.uIcc_of_le hAB] using hv
        exact typeIMellinReflectionIntegrand_eq_factored sigma t r hq
          (hA.trans_le hvIcc.1)

/-- Explicit Jacobian and logarithmic scale factor in `v = m*x`. -/
noncomputable def typeIReflectionScaleFactor
    (sigma t m : ℝ) : ℂ :=
  ((m : ℂ)⁻¹ *
    Complex.exp (((sigma * Real.log m : ℝ) : ℂ))) *
      Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))

/-- Physical cutoff integrand at Fourier frequency `m`. -/
noncomputable def typeIDyadicPhysicalIntegrand
    (sigma t m Q x : ℝ) : ℂ :=
  (typeIDyadicCutoff (x / Q) : ℂ) *
    (gmReflectionPowerWeight sigma x *
      Complex.exp
        (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))))

/-- Exact physical-to-reflected rescaling before Mellin inversion. -/
theorem typeIDyadicPhysicalIntegral_rescale
    {sigma t m Q A B : ℝ} (hm : 0 < m) (hQ : 0 < Q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
  let g : ℝ → ℂ := typeIDyadicPhysicalIntegrand sigma t 1 (m * Q)
  have hPointwise : ∀ x ∈ Set.uIcc A B,
      typeIDyadicPhysicalIntegrand sigma t m Q x =
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
    have hlog : Real.log (m * x) = Real.log m + Real.log x :=
      Real.log_mul hm.ne' hxPos.ne'
    have hcut : m * x / (m * Q) = x / Q := by
      field_simp [hm.ne', hQ.ne']
    dsimp only [g]
    unfold typeIDyadicPhysicalIntegrand gmReflectionPowerWeight
    rw [hcut]
    rw [hlog]
    have hSigmaEq :
        Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
            Complex.exp (((-sigma * (Real.log m + Real.log x) : ℝ) : ℂ)) =
          Complex.exp (((-sigma * Real.log x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hPhaseEq :
        Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I)) *
            Complex.exp
              (-((((t * (Real.log m + Real.log x) -
                2 * Real.pi * 1 * (m * x) : ℝ) : ℂ) * I))) =
          Complex.exp
            (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hSigmaEq, ← hPhaseEq]
    ring
  have hChange := intervalIntegral.integral_comp_mul_left g hm.ne'
    (a := A) (b := B)
  calc
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∫ x in A..B,
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
        apply intervalIntegral.integral_congr
        exact hPointwise
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ∫ x in A..B, g (m * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ((m : ℝ)⁻¹ • ∫ v in m * A..m * B, g v) := by
      rw [hChange]
    _ = typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
      unfold typeIReflectionScaleFactor
      simp only [Complex.real_smul]
      dsimp only [g]
      push_cast
      ring

/-- Exact Mellin-reflected formula for a physical dyadic Fourier mode. -/
theorem typeIDyadicPhysicalIntegral_eq_mellinReflection
    {sigma t m Q A B : ℝ} (hsigma : 0 ≤ sigma)
    (hm : 0 < m) (hQ : 0 < Q) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            ((m * Q : ℝ) : ℂ) *
              ((m * Q : ℝ) : ℂ) ^ ((r : ℂ) * I) *
                typeIDyadicCutoffMellin r *
                  typeIPowerReflectionIntegral sigma (t + r)
                    (m * A) (m * B)) := by
  rw [typeIDyadicPhysicalIntegral_rescale hm hQ hA hAB]
  congr 1
  have hFun : typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) =
      fun v : ℝ =>
        (typeIDyadicCutoff (v / (m * Q)) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
    funext v
    unfold typeIDyadicPhysicalIntegrand
    congr 3
    ring_nf
  rw [hFun]
  exact typeIDyadicRescaledIntegral_eq_mellinReflection hsigma
    (mul_pos hm hQ) (mul_pos hm hA)
    (mul_le_mul_of_nonneg_left hAB hm.le)

/-- A rescaled dyadic integrand is supported strictly between `q/2` and
`2*q`.  Consequently any larger positive interval may be used for its
integral.  This is the support statement that lets all critical Poisson modes
share one reflection interval. -/
theorem integral_typeIDyadicPhysicalIntegrand_eq_interval
    {sigma t q L U : ℝ} (hq : 0 < q)
    (hL : L ≤ q / 2) (hU : 2 * q ≤ U) :
    (∫ v : ℝ, typeIDyadicPhysicalIntegrand sigma t 1 q v) =
      ∫ v in L..U, typeIDyadicPhysicalIntegrand sigma t 1 q v := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro v hv
  have hcut : typeIDyadicCutoff (v / q) ≠ 0 := by
    intro hzero
    apply hv
    simp [typeIDyadicPhysicalIntegrand, hzero]
  have hlower : 1 / 2 < v / q := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_le_half (le_of_not_gt hnot))
  have hupper : v / q < 2 := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_two_le (le_of_not_gt hnot))
  rw [Set.mem_Ioc]
  constructor
  · have hqhalf : q / 2 < v := by
      have hscaled := (lt_div_iff₀ hq).mp hlower
      nlinarith
    exact hL.trans_lt hqhalf
  · exact ((div_lt_iff₀ hq).mp hupper).le.trans hU

/-- Exact medium Type-I reflection with a mode-independent integration
interval.  For every `1 ≤ m ≤ M`, the change of variables `v = m*x` puts the
support inside `[Q/2, 2*M*Q]`; Mellin inversion then leaves the mode only in
explicit algebraic factors. -/
theorem typeIDyadicPhysicalIntegral_eq_common_mellinReflection
    {sigma t Q : ℝ} {m M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            (((m : ℝ) * Q : ℝ) : ℂ) *
              (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I) *
                typeIDyadicCutoffMellin r *
                  typeIPowerReflectionIntegral sigma (t + r)
                    (Q / 2) (2 * M * Q)) := by
  have hmPosNat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hmPosNat
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMPos : (0 : ℝ) < M := by exact_mod_cast hmPosNat.trans_le hmM
  rw [typeIDyadicPhysicalIntegral_rescale hmPos hQ (by positivity)
    (by linarith)]
  congr 1
  have hNatural :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in (m : ℝ) * (Q / 2)..(m : ℝ) * (2 * Q),
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · exact le_of_eq (by ring)
    · exact le_of_eq (by ring)
  have hmMReal : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hCommon :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in Q / 2..2 * M * Q,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · have hscale := mul_le_mul_of_nonneg_right hmOne hQ.le
      nlinarith
    · nlinarith
  rw [← hNatural, hCommon]
  have hFun : typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) =
      fun v : ℝ =>
        (typeIDyadicCutoff (v / ((m : ℝ) * Q)) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
    funext v
    unfold typeIDyadicPhysicalIntegrand
    congr 3
    ring_nf
  rw [hFun]
  exact typeIDyadicRescaledIntegral_eq_mellinReflection hsigma
    (mul_pos hmPos hQ) (by positivity) (by
      have hMOne : (1 : ℝ) ≤ M := hmOne.trans hmMReal
      have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
      nlinarith)

/-- One mode of the exact common Mellin-reflection integrand. -/
noncomputable def typeICommonMellinMode
    (sigma t q A B r : ℝ) : ℂ :=
  (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
    typeIDyadicCutoffMellin r *
      typeIPowerReflectionIntegral sigma (t + r) A B

theorem intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    {sigma t q A B : ℝ} (r : ℝ) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) =
      typeICommonMellinMode sigma t q A B r := by
  unfold typeICommonMellinMode typeIPowerReflectionIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc A B := by
    simpa only [Set.uIcc_of_le hAB] using hv
  exact typeIMellinReflectionIntegrand_eq_factored sigma t r hq
    (hA.trans_le hvIcc.1)

theorem integrable_typeICommonMellinMode
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (typeICommonMellinMode sigma t q A B) := by
  have hJoint := integrable_typeIMellinReflectionIntegrand
    (sigma := sigma) (t := t) (q := q) (A := A) (B := B)
    hsigma hq hA hAB
  have hInner : Integrable (fun r : ℝ =>
      ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) := by
    have h := hJoint.integral_prod_right
    simpa only [intervalIntegral.integral_of_le hAB,
      Set.uIoc_of_le hAB, Function.uncurry_apply_pair] using h
  apply hInner.congr
  filter_upwards with r
  exact intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    r hq hA hAB

/-- The finite coefficient polynomial produced by exact medium reflection.
The coefficients are independent of the original ordinate except for the
standard unit-modulus Dirichlet phase. -/
noncomputable def typeIReflectedMellinPolynomial
    (sigma t Q : ℝ) (M : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    typeIReflectionScaleFactor sigma t m *
      (((m : ℝ) * Q : ℝ) : ℂ) *
        (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I)

/-- Exact finite B-process assembly.  A whole block of critical modes is one
Mellin integral of a fixed finite Dirichlet polynomial against the common
oscillatory kernel.  No pointwise stationary-phase approximation or hidden
error term remains. -/
theorem sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
  let S := Finset.Icc 1 M
  let A : ℝ := Q / 2
  let B : ℝ := 2 * M * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hMOne : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
    nlinarith
  have hModeInt : ∀ m ∈ S,
      Integrable (fun r : ℝ =>
        typeIReflectionScaleFactor sigma t m *
          typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hmS
    have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hmS
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmRange.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∑ m ∈ S,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        apply Finset.sum_congr rfl
        intro m hmS
        have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hmS
        rw [typeIDyadicPhysicalIntegral_eq_common_mellinReflection
          hsigma hQ hmRange.1 hmRange.2]
        unfold typeICommonMellinMode A B
        simp only [Complex.real_smul]
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ m ∈ S,
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        rw [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∑ m ∈ S,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        congr 1
        exact (MeasureTheory.integral_finsetSum S hModeInt).symm
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        dsimp only [S, A, B]
        unfold typeIReflectedMellinPolynomial typeICommonMellinMode
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- Continuous compactly supported interpolation of a smooth Type-I block. -/
noncomputable def typeIReflectionKernel
    (Y A r : ℕ) (σ t x : ℝ) : ℂ :=
  (typeISourceSmoothWeight Y A r x : ℂ) *
    Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
    Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))

theorem contDiff_typeIReflectionKernel
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    ContDiff ℝ ∞ (typeIReflectionKernel Y A r σ t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
    have hEventually : typeIReflectionKernel Y A r σ t =ᶠ[𝓝 0] 0 := by
      filter_upwards [Iio_mem_nhds hYreal] with y hy
      have hy' : y < (Y : ℝ) := hy
      have hleft : Real.smoothTransition (y - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [typeIReflectionKernel, typeISourceSmoothWeight,
        typeITailBoundary, hleft]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hweight : ContDiffAt ℝ ∞
        (fun y : ℝ => (typeISourceSmoothWeight Y A r y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiff_typeISourceSmoothWeight Y A r).contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hsigma : ContDiffAt ℝ ∞
        (fun y : ℝ => (((-σ * Real.log y : ℝ) : ℂ))) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)
    have ht : ContDiffAt ℝ ∞
        (fun y : ℝ => (((-t * Real.log y : ℝ) : ℂ) * I)) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).mul contDiffAt_const
    exact (hweight.mul hsigma.cexp).mul ht.cexp

theorem hasCompactSupport_typeIReflectionKernel
    (Y A r : ℕ) (σ t : ℝ) :
    HasCompactSupport (typeIReflectionKernel Y A r σ t) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (A + 1)))
  intro x hx
  have hboundary : typeITailBoundary Y A x = 0 := by
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have hleft : Real.smoothTransition (x - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by
          have hYnonneg : (0 : ℝ) ≤ Y := by positivity
          linarith)
      rw [typeITailBoundary, hleft, zero_mul]
    · have hx' : (((A + 1 : ℕ) : ℝ)) ≤ x := by
        push_cast
        exact le_of_not_ge hx
      have hright : Real.smoothTransition
          (((A + 1 : ℕ) : ℝ) - x) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [typeITailBoundary, hright, mul_zero]
  simp [typeIReflectionKernel, typeISourceSmoothWeight, hboundary]

/-- Schwartz realization of the smooth Type-I kernel. -/
noncomputable def typeIReflectionSchwartz
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeIReflectionKernel Y A r σ t).toSchwartzMap
    (contDiff_typeIReflectionKernel Y A r σ t hY)

@[simp]
theorem typeIReflectionSchwartz_apply
    (Y A r : ℕ) (σ t x : ℝ) (hY : 0 < Y) :
    typeIReflectionSchwartz Y A r σ t hY x =
      typeIReflectionKernel Y A r σ t x := rfl

/-- Fourier mode of the smooth Type-I block. -/
noncomputable def typeIReflectionFourier
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) (ξ : ℝ) : ℂ :=
  𝓕 (typeIReflectionSchwartz Y A r σ t hY) ξ

/-- Literal Poisson expansion of the smooth block. -/
theorem typeIReflection_poisson
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    ∑' n : ℤ, typeIReflectionKernel Y A r σ t n =
      ∑' m : ℤ, typeIReflectionFourier Y A r σ t hY m := by
  simpa [typeIReflectionFourier] using
    (SchwartzMap.tsum_eq_tsum_fourier
      (typeIReflectionSchwartz Y A r σ t hY) 0)

/-- Every fixed source block has arbitrary-order Fourier decay.  This is the
non-uniform Schwartz bound underlying the complete Poisson tail; the missing
medium Type-I theorem is precisely the parameter-uniform specialization at
the source cutoff `T^ε T/Q`. -/
theorem typeIReflectionFourier_fixed_decay
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      |ξ| ^ j * ‖typeIReflectionFourier Y A r σ t hY ξ‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (typeIReflectionSchwartz Y A r σ t hY)
  obtain ⟨C, hC, hbound⟩ := F.decay j 0
  refine ⟨C, hC, ?_⟩
  intro ξ
  simpa [F, typeIReflectionFourier, Real.norm_eq_abs] using hbound ξ

/-- Absolute summability of the complete integer Poisson series for a fixed
source block.  This justifies an exact finite critical-window/remainder
decomposition without postulating any tail estimate. -/
theorem typeIReflectionFourier_summable
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    Summable (fun m : ℤ =>
      typeIReflectionFourier Y A r σ t hY m) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (typeIReflectionSchwartz Y A r σ t hY)
  have hBigO := F.isBigO_cocompact_rpow (-2)
  have hSummable : Summable (fun m : ℤ => F (m : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hBigO.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [F, typeIReflectionFourier,
    SchwartzMap.fourierTransformCLM_apply] using hSummable

/-- At positive integers the continuous kernel is exactly the source block
summand. -/
theorem typeIReflectionKernel_natCast
    (Y A r n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    typeIReflectionKernel Y A r σ t n =
      typeISourceSmoothWeight Y A r n *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  rw [hbase]
  unfold typeIReflectionKernel
  rw [Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    ← Complex.ofReal_log hnReal.le]
  simp only [ofReal_neg, ofReal_mul]
  ring_nf

/-- The negative frequency `-m` is the source logarithmic stationary phase,
with every nonoscillatory factor kept outside the exponential. -/
theorem typeIReflectionFourier_neg_eq_stationaryIntegral
    (Y A r : ℕ) (σ t m : ℝ) (hY : 0 < Y) :
    typeIReflectionFourier Y A r σ t hY (-m) =
      ∫ x : ℝ,
        (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp (2 * Real.pi * I *
            ((reflectionPhase t m x : ℝ) : ℂ)) := by
  rw [typeIReflectionFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [typeIReflectionSchwartz_apply]
  by_cases hweight : typeISourceSmoothWeight Y A r x = 0
  · simp [typeIReflectionKernel, hweight]
  · have hxPos : 0 < x := by
      by_contra hx
      have hxle : x ≤ 0 := le_of_not_gt hx
      have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
      have hleft : Real.smoothTransition (x - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      apply hweight
      simp [typeISourceSmoothWeight, typeITailBoundary, hleft]
    unfold typeIReflectionKernel reflectionPhase
    simp only [Real.inner_apply, smul_eq_mul]
    calc
      Complex.exp (((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) *
          ((typeISourceSmoothWeight Y A r x : ℂ) *
            Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
            Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))) =
        (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          (Complex.exp (((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) *
            Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))) := by ring
      _ = (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp
            ((((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) +
              (((-t * Real.log x : ℝ) : ℂ) * I)) := by
            rw [Complex.exp_add]
      _ = (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp (2 * Real.pi * I *
            (((m * x - t / (2 * Real.pi) * Real.log x : ℝ)) : ℂ)) := by
            congr 2
            push_cast
            field_simp [Real.pi_ne_zero]
            ring

/-- The exact stationary-frequency window of the `r`-th source block.  Its
endpoints are constant multiples of `t/(2^r Y)`, the dual scale required by
the medium Type-I B-process. -/
theorem typeIReflection_stationary_window
    {Y r : ℕ} {t m : ℝ} (hY : 0 < Y) (hm : 0 < m) :
    reflectionStationaryPoint t m ∈
        Set.Icc (((2 ^ r * Y : ℕ) : ℝ) / 2)
          (2 * ((2 ^ r * Y : ℕ) : ℝ)) ↔
      t / (4 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) ≤ m ∧
        m ≤ t / (Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by
  have hscale : (0 : ℝ) < (2 ^ r * Y : ℕ) := by positivity
  rw [reflectionStationaryPoint_mem_Icc_iff hm (by positivity)
    (by linarith : ((2 ^ r * Y : ℕ) : ℝ) / 2 ≤
      2 * ((2 ^ r * Y : ℕ) : ℝ))]
  have hlow : t / (2 * Real.pi *
      (2 * ((2 ^ r * Y : ℕ) : ℝ))) =
      t / (4 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by ring
  have hupp : t / (2 * Real.pi *
      (((2 ^ r * Y : ℕ) : ℝ) / 2)) =
      t / (Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by
    field_simp [Real.pi_ne_zero, hscale.ne']
  rw [hlow, hupp]

end RiemannZeta.GuthMaynard
