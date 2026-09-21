import TaoTrudgianYang2025.PointMeanLemmaThreeContour
import TaoTrudgianYang2025.PointMeanLemmaThreeDouble
import TaoTrudgianYang2025.PointMeanMellinHorizontal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Adapted from the adjacent Gafni--Tao development, with local contour proofs
and the target's literal critical-line zeta norm and local second integral.

# Quantitative edges in Heath--Brown's Lemma 3

This file estimates the four literal sides of the finite residue rectangle.
The long-side estimates retain the strong Gamma reserve and therefore lose
only one factor `delta⁻¹` after the nested equation-(40) convolution.
-/

open Complex Set MeasureTheory Filter
open scoped Interval

namespace TaoTrudgianYang2025

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_log_sq_le_rpow {q : ℝ} (hq : 0 < q) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ 2 ≤ X ^ q := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with X hBound hX
  have hLogNonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hXNonneg : 0 ≤ X := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hLogNonneg 2),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hXNonneg q)] at hBound
  simpa [Real.rpow_two] using hBound


theorem eventually_const_mul_rpow_le_rpow
    {D a b : Real} (hab : a < b) :
    ∀ᶠ U : Real in atTop, D * U ^ a <= U ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hTend : Tendsto (fun U : Real => U ^ (b - a)) atTop atTop :=
    tendsto_rpow_atTop hgap
  have hEventually : ∀ᶠ U : Real in atTop, D <= U ^ (b - a) :=
    (tendsto_atTop.1 hTend) D
  filter_upwards [hEventually, eventually_gt_atTop (0 : Real)] with U hU hUpos
  calc
    D * U ^ a <= U ^ (b - a) * U ^ a :=
      mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hUpos.le _)
    _ = U ^ b := by
      rw [<- Real.rpow_add hUpos]
      congr 1
      ring



theorem integral_exp_neg_abs_heathBrown :
    (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-x))]
  rw [integral_exp_neg_Ioi_zero]
  norm_num

theorem integrable_exp_neg_abs_heathBrown :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-|x|)
  have hpos : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).congr_fun
      (fun x hx => by
        dsimp only [f]
        rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, f, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hall := hneg.union hpos
  rw [Iic_union_Ioi] at hall
  simpa only [IntegrableOn, Measure.restrict_univ] using hall

theorem heathBrownStrongSingularKernel_le_exp
    {delta x : ℝ} (hdelta : 0 < delta) :
    heathBrownStrongSingularKernel delta x ≤
      delta⁻¹ * Real.exp (-|x|) := by
  have hden : 0 < delta + |x| := by positivity
  have hExp : Real.exp (-(4 / 3 : ℝ) * |x|) ≤ Real.exp (-|x|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg x]
  unfold heathBrownStrongSingularKernel
  calc
    Real.exp (-(4 / 3 : ℝ) * |x|) / (delta + |x|) ≤
        Real.exp (-|x|) / (delta + |x|) := by gcongr
    _ ≤ Real.exp (-|x|) / delta := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdelta
        (by linarith [abs_nonneg x])
    _ = delta⁻¹ * Real.exp (-|x|) := by field_simp

theorem integrable_heathBrownStrongSingularKernel
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (heathBrownStrongSingularKernel delta) := by
  apply ((integrable_exp_neg_abs_heathBrown.const_mul delta⁻¹)).mono'
  · have hcont : Continuous (heathBrownStrongSingularKernel delta) := by
      unfold heathBrownStrongSingularKernel
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact (by positivity : 0 < delta + |x|).ne' hx
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold heathBrownStrongSingularKernel
      positivity)]
    exact heathBrownStrongSingularKernel_le_exp hdelta

theorem integral_heathBrownStrongSingularKernel_le
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x : ℝ, heathBrownStrongSingularKernel delta x) ≤ 2 / delta := by
  calc
    (∫ x : ℝ, heathBrownStrongSingularKernel delta x) ≤
        ∫ x : ℝ, delta⁻¹ * Real.exp (-|x|) := by
      exact integral_mono
        (integrable_heathBrownStrongSingularKernel hdelta)
        (integrable_exp_neg_abs_heathBrown.const_mul delta⁻¹)
        (fun x => heathBrownStrongSingularKernel_le_exp hdelta)
    _ = delta⁻¹ * 2 := by
      rw [integral_const_mul, integral_exp_neg_abs_heathBrown]
    _ = 2 / delta := by field_simp

theorem intervalIntegral_heathBrownStrongSingularKernel_le
    {delta H : ℝ} (hdelta : 0 < delta) (hH : 0 ≤ H) :
    (∫ x in -H..H, heathBrownStrongSingularKernel delta x) ≤ 2 / delta := by
  calc
    (∫ x in -H..H, heathBrownStrongSingularKernel delta x) ≤
        ∫ x : ℝ, heathBrownStrongSingularKernel delta x := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral
        (integrable_heathBrownStrongSingularKernel hdelta)
        (Filter.Eventually.of_forall fun x => by
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ 2 / delta := integral_heathBrownStrongSingularKernel_le hdelta

theorem norm_VIntegral'_le_intervalIntegral_norm
    (f : ℂ → ℂ) {x a b : ℝ} (hab : a ≤ b) :
    ‖VIntegral' f x a b‖ ≤
      ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖ := by
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  unfold VIntegral' VIntegral
  rw [norm_smul, norm_smul]
  simp only [norm_I, one_mul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ ≤
      1 * ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ := by gcongr
    _ ≤ ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖ :=
      (by simpa only [one_mul] using
        (intervalIntegral.norm_integral_le_integral_norm hab :
          ‖∫ y in a..b, f ((x : ℂ) + (y : ℂ) * I)‖ ≤
            ∫ y in a..b, ‖f ((x : ℂ) + (y : ℂ) * I)‖))

theorem exists_norm_heathBrownLemmaThree_plusEdge_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * (heathBrownStrongSingularKernel delta w *
          (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  obtain ⟨G, hG, hGamma⟩ :=
    exists_heathBrown_Gamma_shift_kernel_strong_bound
  obtain ⟨P, hP, hPlus⟩ :=
    exists_heathBrown_offCritical_plus_strong_le
  refine ⟨G * P, mul_pos hG hP, ?_⟩
  intro delta t w hdelta hdeltaUpper htw
  have hden : 0 < delta + |w| := by positivity
  have hGamma' :
      ‖Complex.Gamma (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using (hGamma delta w hdelta hdeltaUpper).1
  have hzeta := hPlus delta (t + w) hdelta hdeltaUpper htw
  have harg :
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((delta : ℝ) : ℂ) + (w : ℂ) * I) =
        (((1 / 2 + delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  calc
    ‖Complex.Gamma (((delta : ℝ) : ℂ) + (w : ℂ) * I)‖ *
        ‖riemannZeta
          (((1 / 2 + delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I)‖ ^
            (2 : ℕ) ≤
      (G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|)) *
        (P * (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      gcongr
    _ = (G * P) * (heathBrownStrongSingularKernel delta w *
          (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      unfold heathBrownStrongSingularKernel
      ring_nf

theorem integrable_heathBrownStrongLongEdgeMajorant
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    Integrable (fun w : ℝ => heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  convert (integrable_heathBrownStrongSingularKernel hdelta).add
    (integrable_strongKernel_mul_strongMoment hdelta t) using 1
  funext w
  simp only [Pi.add_apply]
  ring

theorem integral_heathBrownStrongLongEdgeMajorant_le
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) ≤
        ((2 + Real.pi) / delta) * (1 + heathBrownFullCriticalMoment t) := by
  have hfull := heathBrownFullCriticalMoment_nonneg t
  have hmass := integral_heathBrownStrongSingularKernel_le hdelta
  have hdouble := integral_strongKernel_mul_strongMoment_le hdelta t
  rw [show (∫ w : ℝ, heathBrownStrongSingularKernel delta w *
      (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) =
        (∫ w : ℝ, heathBrownStrongSingularKernel delta w) +
          ∫ w : ℝ, heathBrownStrongSingularKernel delta w *
            heathBrownStrongMellinCriticalMoment delta (t + w) by
      rw [← integral_add
        (integrable_heathBrownStrongSingularKernel hdelta)
        (integrable_strongKernel_mul_strongMoment hdelta t)]
      apply integral_congr_ae
      filter_upwards with w
      ring]
  have hdeltaNonneg : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  calc
    (∫ w : ℝ, heathBrownStrongSingularKernel delta w) +
        ∫ w : ℝ, heathBrownStrongSingularKernel delta w *
          heathBrownStrongMellinCriticalMoment delta (t + w) ≤
      2 / delta + (Real.pi / delta) * heathBrownFullCriticalMoment t :=
        add_le_add hmass hdouble
    _ ≤ ((2 + Real.pi) / delta) * (1 + heathBrownFullCriticalMoment t) := by
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      field_simp [hdelta.ne']
      nlinarith

theorem exists_norm_heathBrownLemmaThree_plusEdge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t H : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) delta (-H) H‖ ≤
        (C / delta) * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_plusEdge_integrand_le
  let C : ℝ := B * (2 + Real.pi)
  have hC : 0 < C := mul_pos hB (by positivity)
  refine ⟨C, hC, ?_⟩
  intro delta t H hdelta hdeltaUpper hH ht
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun w => heathBrownStrongSingularKernel delta w *
    (1 + heathBrownStrongMellinCriticalMoment delta (t + w))
  have hg : Integrable g := by
    simpa only [g] using integrable_heathBrownStrongLongEdgeMajorant hdelta t
  have hNorm := norm_VIntegral'_le_intervalIntegral_norm F
    (x := delta) (a := -H) (b := H) (by linarith)
  calc
    ‖VIntegral' F delta (-H) H‖ ≤
        ∫ w in -H..H, ‖F ((delta : ℂ) + (w : ℂ) * I)‖ := hNorm
    _ ≤ ∫ w in -H..H, B * g w := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have hcont := continuous_heathBrownZetaSquareMellinIntegrand_vertical
          (s := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (a := delta) (by linarith) hdelta.ne'
          (by simp; linarith)
        have hcontNorm : Continuous (fun w : ℝ =>
            ‖F ((delta : ℂ) + (w : ℂ) * I)‖) := by
          simpa only [F] using hcont.norm
        exact hcontNorm.intervalIntegrable _ _
      · exact (hg.const_mul B).intervalIntegrable
      · intro w hw'
        simpa only [F, g] using hPoint delta t w hdelta hdeltaUpper
          (by linarith [hw'.1])
    _ = B * ∫ w in -H..H, g w := intervalIntegral.integral_const_mul _ _
    _ ≤ B * ∫ w : ℝ, g w := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall fun w => by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ B * (((2 + Real.pi) / delta) *
          (1 + heathBrownFullCriticalMoment t)) := by
      gcongr
      simpa only [g] using integral_heathBrownStrongLongEdgeMajorant_le hdelta t
    _ = (C / delta) * (1 + heathBrownFullCriticalMoment t) := by
      dsimp only [C]
      ring

theorem exists_norm_heathBrownLemmaThree_minusEdge_integrand_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t w : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t + w →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        C * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (heathBrownStrongSingularKernel delta w *
              (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
  obtain ⟨G, hG, hGamma⟩ :=
    exists_heathBrown_Gamma_shift_kernel_strong_bound
  obtain ⟨P, D, hP, hD, hMinus⟩ :=
    exists_heathBrown_offCritical_minus_strong_le
  refine ⟨G * P, D, mul_pos hG hP, hD, ?_⟩
  intro delta t w hdelta hdeltaUpper htw
  have hden : 0 < delta + |w| := by positivity
  have hGamma' :
      ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
        G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using (hGamma delta w hdelta hdeltaUpper).2
  have hzeta := hMinus delta (t + w) hdelta hdeltaUpper htw
  have harg :
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((-delta : ℝ) : ℂ) + (w : ℂ) * I) =
        (((1 / 2 - delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow, harg]
  calc
    ‖Complex.Gamma (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ *
        ‖riemannZeta
          (((1 / 2 - delta : ℝ) : ℂ) + ((t + w : ℝ) : ℂ) * I)‖ ^
            (2 : ℕ) ≤
      (G * Real.exp (-(4 / 3 : ℝ) * |w|) / (delta + |w|)) *
        (P * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      gcongr
    _ = (G * P) * Real.exp
          (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) *
            (heathBrownStrongSingularKernel delta w *
              (1 + heathBrownStrongMellinCriticalMoment delta (t + w))) := by
      unfold heathBrownStrongSingularKernel
      ring_nf

theorem exists_norm_heathBrownLemmaThree_minusEdge_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (delta t H Q : ℝ),
      0 < delta → delta ≤ 1 / 4 → 0 ≤ H → 10 + H ≤ t → 0 ≤ Q →
      (∀ w ∈ Set.Icc (-H) H,
        Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) ≤ Q) →
      ‖VIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) (-H) H‖ ≤
        ((C * Q) / delta) * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨B, D, hB, hD, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_minusEdge_integrand_le
  let C : ℝ := B * (2 + Real.pi)
  have hC : 0 < C := mul_pos hB (by positivity)
  refine ⟨C, D, hC, hD, ?_⟩
  intro delta t H Q hdelta hdeltaUpper hH ht hQ hUniform
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := fun w => heathBrownStrongSingularKernel delta w *
    (1 + heathBrownStrongMellinCriticalMoment delta (t + w))
  have hg : Integrable g := by
    simpa only [g] using integrable_heathBrownStrongLongEdgeMajorant hdelta t
  have hNorm := norm_VIntegral'_le_intervalIntegral_norm F
    (x := -delta) (a := -H) (b := H) (by linarith)
  calc
    ‖VIntegral' F (-delta) (-H) H‖ ≤
        ∫ w in -H..H, ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ := hNorm
    _ ≤ ∫ w in -H..H, (B * Q) * g w := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have hcont := continuous_heathBrownZetaSquareMellinIntegrand_vertical
          (s := (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (a := -delta) (by linarith) (neg_ne_zero.mpr hdelta.ne')
          (by simp; linarith)
        have hcontNorm : Continuous (fun w : ℝ =>
            ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖) := by
          simpa only [F] using hcont.norm
        exact hcontNorm.intervalIntegrable _ _
      · exact (hg.const_mul (B * Q)).intervalIntegrable
      · intro w hw
        have hraw := hPoint delta t w hdelta hdeltaUpper
          (by linarith [hw.1])
        have hfactor := hUniform w hw
        have hgNonneg : 0 ≤ g w := by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity
        calc
          ‖F (((-delta : ℝ) : ℂ) + (w : ℂ) * I)‖ ≤
              B * Real.exp
                (2 * (Real.log ((t + w) / 2 + 2) + D) * delta) * g w := by
            simpa only [F, g] using hraw
          _ ≤ B * Q * g w := by gcongr
          _ = (B * Q) * g w := by ring
    _ = (B * Q) * ∫ w in -H..H, g w :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (B * Q) * ∫ w : ℝ, g w := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact MeasureTheory.setIntegral_le_integral hg
        (Filter.Eventually.of_forall fun w => by
          dsimp only [g]
          have hm := heathBrownStrongMellinCriticalMoment_nonneg
            (delta := delta) (t := t + w) hdelta
          unfold heathBrownStrongSingularKernel
          positivity)
    _ ≤ (B * Q) * (((2 + Real.pi) / delta) *
          (1 + heathBrownFullCriticalMoment t)) := by
      gcongr
      simpa only [g] using integral_heathBrownStrongLongEdgeMajorant_le hdelta t
    _ = ((C * Q) / delta) * (1 + heathBrownFullCriticalMoment t) := by
      dsimp only [C]
      ring

theorem eventually_heathBrownLemmaThreeRadius_le_half_identity :
    ∀ᶠ t : ℝ in Filter.atTop,
      heathBrownLemmaThreeRadius t ≤ t / 2 := by
  have hlog := eventually_log_sq_le_rpow (q := (1 / 2 : ℝ)) (by norm_num)
  have hpow := eventually_const_mul_rpow_le_rpow
    (D := (2 : ℝ)) (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  filter_upwards [hlog, hpow, Filter.eventually_gt_atTop (0 : ℝ)] with
      t hlog hpow ht
  unfold heathBrownLemmaThreeRadius
  rw [Real.rpow_one] at hpow
  linarith

theorem heathBrownLemmaThree_minus_factor_le_exp_four
    {D t w : ℝ} (ht : 8 ≤ t)
    (hRadius : heathBrownLemmaThreeRadius t ≤ t / 2)
    (hDlog : D ≤ Real.log t)
    (hw : w ∈ Set.Icc (-heathBrownLemmaThreeRadius t)
      (heathBrownLemmaThreeRadius t)) :
    Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
      heathBrownLemmaThreeDelta t) ≤ Real.exp 4 := by
  have htPos : 0 < t := by linarith
  have htwLower : -(t / 2) ≤ w := by linarith [hw.1]
  have hargPos : 0 < (t + w) / 2 + 2 := by linarith
  have hargUpper : (t + w) / 2 + 2 ≤ t := by linarith [hw.2]
  have hlogUpper : Real.log ((t + w) / 2 + 2) ≤ Real.log t :=
    Real.log_le_log hargPos hargUpper
  have hlogPos : 0 < Real.log t := Real.log_pos (by linarith)
  apply Real.exp_le_exp.mpr
  unfold heathBrownLemmaThreeDelta
  calc
    2 * (Real.log ((t + w) / 2 + 2) + D) * (1 / Real.log t) =
        (2 * (Real.log ((t + w) / 2 + 2) + D)) / Real.log t := by ring
    _ ≤ 4 := (div_le_iff₀ hlogPos).2 (by nlinarith)

theorem eventually_heathBrownLemmaThree_minus_factor
    (D : ℝ) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ w ∈
      Set.Icc (-heathBrownLemmaThreeRadius t) (heathBrownLemmaThreeRadius t),
      Real.exp (2 * (Real.log ((t + w) / 2 + 2) + D) *
        heathBrownLemmaThreeDelta t) ≤ Real.exp 4 := by
  have hD := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop D)
  filter_upwards [eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hD, Filter.eventually_ge_atTop (8 : ℝ)] with t hRadius hDlog ht
  intro w hw
  exact heathBrownLemmaThree_minus_factor_le_exp_four ht hRadius hDlog hw

theorem exists_norm_Gamma_heathBrown_small_horizontal_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta → 1 ≤ |R| →
      ‖Complex.Gamma ((x : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) := by
  obtain ⟨B, hB, hStrip⟩ :=
    exists_norm_Gamma_heathBrown_positive_strip_strong_le
  refine ⟨B, hB, ?_⟩
  intro delta x R hdelta hdeltaUpper hx hR
  let z : ℂ := (x : ℂ) + (R : ℂ) * I
  have hz : z ≠ 0 := by
    intro hz0
    have him := congrArg Complex.im hz0
    dsimp only [z] at him
    simp at him
    rw [him, abs_zero] at hR
    norm_num at hR
  have hrec := Complex.Gamma_add_one z hz
  have harg : z + 1 = ((1 + x : ℝ) : ℂ) + (R : ℂ) * I := by
    apply Complex.ext
    · simp [z]
      ring
    · simp [z]
  have hshift := hStrip (1 + x) R (by linarith [hx.1])
    (by linarith [hx.2])
  have hnormLower : 1 ≤ ‖z‖ := by
    calc
      1 ≤ |R| := hR
      _ ≤ ‖z‖ := by
        have himz : z.im = R := by simp [z]
        rw [← himz]
        exact Complex.abs_im_le_norm z
  calc
    ‖Complex.Gamma z‖ = 1 * ‖Complex.Gamma z‖ := by ring
    _ ≤ ‖z‖ * ‖Complex.Gamma z‖ := by gcongr
    _ = ‖Complex.Gamma (((1 + x : ℝ) : ℂ) + (R : ℂ) * I)‖ := by
      rw [← harg, hrec, norm_mul]
    _ ≤ B * Real.exp (-(4 / 3 : ℝ) * |R|) := hshift

theorem exists_norm_heathBrownLemmaThree_horizontal_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t x R : ℝ),
      0 < delta → delta ≤ 1 / 4 → x ∈ Set.Icc (-delta) delta →
      1 ≤ |t + R| → 1 ≤ |R| →
      ‖heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
          (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by
  obtain ⟨B, hB, hGamma⟩ :=
    exists_norm_Gamma_heathBrown_small_horizontal_strong_le
  refine ⟨B, hB, ?_⟩
  intro delta t x R hdelta hdeltaUpper hx hheight hR
  have hzetaRe : (1 / 4 : ℝ) ≤
      ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
        (((x : ℝ) : ℂ) + (R : ℂ) * I)).re := by
    simp
    linarith [hx.1]
  have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe (by simpa using hheight)
  have hnorm :
      ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
        (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤ 1 + |t| + |R| := by
    calc
      ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
          (((x : ℝ) : ℂ) + (R : ℂ) * I)‖ ≤
        |1 / 2 + x| + |t + R| := by
          have h := Complex.norm_le_abs_re_add_abs_im
            ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
              (((x : ℝ) : ℂ) + (R : ℂ) * I))
          simpa using h
      _ ≤ (1 / 2 + |x|) + (|t| + |R|) := by
        gcongr
        · calc
            |1 / 2 + x| ≤ |(1 / 2 : ℝ)| + |x| := abs_add_le _ _
            _ = 1 / 2 + |x| := by norm_num
        · exact abs_add_le _ _
      _ ≤ 1 + |t| + |R| := by
        have hxAbs : |x| ≤ delta := abs_le.mpr hx
        linarith
  rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
  exact mul_le_mul
    (hGamma delta x R hdelta hdeltaUpper hx hR)
    (pow_le_pow_left₀ (norm_nonneg _) (hzeta.trans
      (mul_le_mul_of_nonneg_left hnorm (by norm_num))) 2)
    (by positivity) (by positivity)

theorem exists_norm_heathBrownLemmaThree_horizontalEdge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t R : ℝ),
      0 < delta → delta ≤ 1 / 4 → 1 ≤ |t + R| → 1 ≤ |R| →
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (-delta) delta R‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by
  obtain ⟨B, hB, hPoint⟩ :=
    exists_norm_heathBrownLemmaThree_horizontal_integrand_le
  let C : ℝ := B
  refine ⟨C, hB, ?_⟩
  intro delta t R hdelta hdeltaUpper hheight hR
  let F : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let M : ℝ := B * Real.exp (-(4 / 3 : ℝ) * |R|) *
    (5 * (1 + |t| + |R|)) ^ (2 : ℕ)
  have hbase : ‖HIntegral F (-delta) delta R‖ ≤ M * |delta - (-delta)| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-delta) delta := by
      rw [← Set.uIcc_of_le (by linarith : -delta ≤ delta)]
      exact Set.uIoc_subset_uIcc hx
    simpa only [F, M] using hPoint delta t x R hdelta hdeltaUpper hx' hheight hR
  have hwidth : |delta - (-delta)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖HIntegral F (-delta) delta R‖ ≤
        1 * (M * |delta - (-delta)|) :=
      mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ ≤ M := by nlinarith [mul_le_mul_of_nonneg_left hwidth hM]
    _ = C * Real.exp (-(4 / 3 : ℝ) * |R|) *
          (5 * (1 + |t| + |R|)) ^ (2 : ℕ) := by rfl

theorem heathBrown_logSquare_exponential_absorption
    {D t : ℝ} (ht : 0 < t) (hDt : D ≤ t)
    (hlog : 9 / 4 ≤ Real.log t) :
    D * t ^ (2 : ℕ) *
      Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) ≤ 1 := by
  let L : ℝ := Real.log t
  have hlog' : 9 / 4 ≤ L := by simpa only [L] using hlog
  have htEq : t = Real.exp L := by
    dsimp only [L]
    exact (Real.exp_log ht).symm
  have hpow : D * t ^ (2 : ℕ) ≤ t * t ^ (2 : ℕ) := by gcongr
  calc
    D * t ^ (2 : ℕ) *
        Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) ≤
      (t * t ^ (2 : ℕ)) *
        Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by gcongr
    _ = Real.exp (3 * L - (4 / 3 : ℝ) * L ^ (2 : ℕ)) := by
      change (t * t ^ (2 : ℕ)) *
        Real.exp (-(4 / 3 : ℝ) * L ^ (2 : ℕ)) = _
      rw [htEq, pow_two]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (L - 9 / 8)]
    _ = 1 := Real.exp_zero

theorem eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one :
    ∀ᶠ t : ℝ in Filter.atTop,
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (-heathBrownLemmaThreeRadius t)‖ ≤ 1 ∧
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (heathBrownLemmaThreeRadius t)‖ ≤ 1 := by
  obtain ⟨B, hB, hHorizontal⟩ :=
    exists_norm_heathBrownLemmaThree_horizontalEdge_le
  have hLog := Real.tendsto_log_atTop.eventually
    (Filter.eventually_ge_atTop (4 : ℝ))
  filter_upwards [eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hLog, Filter.eventually_ge_atTop (max 2 (100 * B))] with
      t hRadius hlog htLarge
  have htTwo : 2 ≤ t := (le_max_left _ _).trans htLarge
  have hBt : 100 * B ≤ t := (le_max_right _ _).trans htLarge
  have ht : 0 < t := by linarith
  have hdelta : 0 < heathBrownLemmaThreeDelta t := by
    unfold heathBrownLemmaThreeDelta
    have : 0 < Real.log t := by linarith
    positivity
  have hdeltaUpper : heathBrownLemmaThreeDelta t ≤ 1 / 4 := by
    unfold heathBrownLemmaThreeDelta
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hH : 1 ≤ heathBrownLemmaThreeRadius t := by
    unfold heathBrownLemmaThreeRadius
    nlinarith
  have hHNonneg : 0 ≤ heathBrownLemmaThreeRadius t := by linarith
  have hminusHeight : 1 ≤ |t - heathBrownLemmaThreeRadius t| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hplusHeight : 1 ≤ |t + heathBrownLemmaThreeRadius t| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hSize :
      5 * (1 + |t| + |heathBrownLemmaThreeRadius t|) ≤ 10 * t := by
    rw [abs_of_pos ht, abs_of_nonneg hHNonneg]
    nlinarith
  have hAbsorb := heathBrown_logSquare_exponential_absorption
    (D := 100 * B) ht hBt (by linarith)
  constructor
  · have hraw := hHorizontal (heathBrownLemmaThreeDelta t) t
      (-heathBrownLemmaThreeRadius t) hdelta hdeltaUpper
      (by simpa only [sub_eq_add_neg] using hminusHeight)
      (by simpa only [abs_neg, abs_of_nonneg hHNonneg] using hH)
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (-heathBrownLemmaThreeRadius t)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |(-heathBrownLemmaThreeRadius t)|) *
          (5 * (1 + |t| + |(-heathBrownLemmaThreeRadius t)|)) ^
            (2 : ℕ) := hraw
      _ ≤ B * Real.exp (-(4 / 3 : ℝ) * heathBrownLemmaThreeRadius t) *
          (10 * t) ^ (2 : ℕ) := by
        rw [abs_neg, abs_of_nonneg hHNonneg]
        have hSize' :
            5 * (1 + |t| + heathBrownLemmaThreeRadius t) ≤ 10 * t := by
          simpa only [abs_of_nonneg hHNonneg] using hSize
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hSize' 2) (by positivity)
      _ = (100 * B) * t ^ (2 : ℕ) *
          Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by
        unfold heathBrownLemmaThreeRadius
        ring
      _ ≤ 1 := hAbsorb
  · have hraw := hHorizontal (heathBrownLemmaThreeDelta t) t
      (heathBrownLemmaThreeRadius t) hdelta hdeltaUpper hplusHeight
      (by simpa only [abs_of_nonneg hHNonneg] using hH)
    calc
      ‖HIntegral' (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
          (-heathBrownLemmaThreeDelta t) (heathBrownLemmaThreeDelta t)
          (heathBrownLemmaThreeRadius t)‖ ≤
        B * Real.exp (-(4 / 3 : ℝ) * |heathBrownLemmaThreeRadius t|) *
          (5 * (1 + |t| + |heathBrownLemmaThreeRadius t|)) ^
            (2 : ℕ) := hraw
      _ ≤ B * Real.exp (-(4 / 3 : ℝ) * heathBrownLemmaThreeRadius t) *
          (10 * t) ^ (2 : ℕ) := by
        rw [abs_of_nonneg hHNonneg]
        have hSize' :
            5 * (1 + |t| + heathBrownLemmaThreeRadius t) ≤ 10 * t := by
          simpa only [abs_of_nonneg hHNonneg] using hSize
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hSize' 2) (by positivity)
      _ = (100 * B) * t ^ (2 : ℕ) *
          Real.exp (-(4 / 3 : ℝ) * (Real.log t ^ (2 : ℕ))) := by
        unfold heathBrownLemmaThreeRadius
        ring
      _ ≤ 1 := hAbsorb

theorem exists_eventually_heathBrownLemmaThree_fullMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in Filter.atTop,
      zetaMomentCriticalNorm t ^ (2 : ℕ) ≤
        C * Real.log t * (1 + heathBrownFullCriticalMoment t) := by
  obtain ⟨P, hP, hPlus⟩ :=
    exists_norm_heathBrownLemmaThree_plusEdge_le
  obtain ⟨M, D, hM, hD, hMinus⟩ :=
    exists_norm_heathBrownLemmaThree_minusEdge_le
  let C : ℝ := 2 + P + M * Real.exp 4
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hMinusFactor := eventually_heathBrownLemmaThree_minus_factor D
  filter_upwards [eventually_norm_heathBrownLemmaThree_horizontalEdges_le_one,
    eventually_heathBrownLemmaThreeRadius_le_half_identity,
    hMinusFactor, Real.tendsto_log_atTop.eventually
      (Filter.eventually_ge_atTop (4 : ℝ)),
    Filter.eventually_ge_atTop (20 : ℝ)] with
      t hHorizontal hRadius hFactor hlog ht
  let delta : ℝ := heathBrownLemmaThreeDelta t
  let H : ℝ := heathBrownLemmaThreeRadius t
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let f : ℂ → ℂ := heathBrownZetaSquareMellinIntegrand s
  let bottom : ℂ := HIntegral' f (-delta) delta (-H)
  let top : ℂ := HIntegral' f (-delta) delta H
  let plus : ℂ := VIntegral' f delta (-H) H
  let minus : ℂ := VIntegral' f (-delta) (-H) H
  let Z : ℝ := heathBrownFullCriticalMoment t
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact heathBrownLemmaThreeDelta_pos (by linarith)
  have hdeltaUpper : delta ≤ 1 / 4 := by
    dsimp only [delta, heathBrownLemmaThreeDelta]
    exact one_div_le_one_div_of_le (by norm_num) hlog
  have hH : 0 ≤ H := by
    dsimp only [H, heathBrownLemmaThreeRadius]
    positivity
  have htH : 10 + H ≤ t := by
    dsimp only [H]
    linarith
  have hBottom : ‖bottom‖ ≤ 1 := by
    simpa only [bottom, f, s, delta, H] using hHorizontal.1
  have hTop : ‖top‖ ≤ 1 := by
    simpa only [top, f, s, delta, H] using hHorizontal.2
  have hPlus : ‖plus‖ ≤ (P / delta) * (1 + Z) := by
    simpa only [plus, f, s, Z] using
      hPlus delta t H hdelta hdeltaUpper hH htH
  have hMinus : ‖minus‖ ≤ ((M * Real.exp 4) / delta) * (1 + Z) := by
    apply hMinus delta t H (Real.exp 4) hdelta hdeltaUpper hH htH
      (Real.exp_pos _).le
    simpa only [H] using hFactor
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact heathBrownFullCriticalMoment_nonneg t
  have hRect := heathBrownLemmaThree_finiteRectangle t (by linarith)
  have hEdges := heathBrownLemmaThree_rectangle_eq_edges t
  have hIdentity : riemannZeta s ^ 2 = bottom - top + plus - minus := by
    rw [← hRect, hEdges]
  have hNorm : ‖riemannZeta s ^ 2‖ ≤
      ‖bottom‖ + ‖top‖ + ‖plus‖ + ‖minus‖ := by
    rw [hIdentity]
    have hOuter := norm_sub_le (bottom - top + plus) minus
    have hMiddle := norm_add_le (bottom - top) plus
    have hInner := norm_sub_le bottom top
    linarith
  have hdeltaInv : 1 / delta = Real.log t := by
    dsimp only [delta, heathBrownLemmaThreeDelta]
    field_simp [(by linarith : Real.log t ≠ 0)]
  calc
    zetaMomentCriticalNorm t ^ (2 : ℕ) = ‖riemannZeta s ^ 2‖ := by
      dsimp only [zetaMomentCriticalNorm, s]
      rw [norm_pow]
    _ ≤ ‖bottom‖ + ‖top‖ + ‖plus‖ + ‖minus‖ := hNorm
    _ ≤ 2 + (P / delta) * (1 + Z) +
          ((M * Real.exp 4) / delta) * (1 + Z) := by linarith
    _ ≤ C * (1 / delta) * (1 + Z) := by
      have hInv : 1 ≤ 1 / delta := by
        rw [hdeltaInv]
        linarith
      have hOneZ : 1 ≤ 1 + Z := by linarith
      have hProd : 1 ≤ (1 / delta) * (1 + Z) := by
        calc
          1 ≤ 1 / delta := hInv
          _ = (1 / delta) * 1 := by ring
          _ ≤ (1 / delta) * (1 + Z) :=
            mul_le_mul_of_nonneg_left hOneZ (by positivity)
      dsimp only [C]
      calc
        2 + (P / delta) * (1 + Z) +
            ((M * Real.exp 4) / delta) * (1 + Z) ≤
          2 * ((1 / delta) * (1 + Z)) + (P / delta) * (1 + Z) +
            ((M * Real.exp 4) / delta) * (1 + Z) := by
              nlinarith [hProd]
        _ = (2 + P + M * Real.exp 4) * (1 / delta) * (1 + Z) := by ring
    _ = C * Real.log t * (1 + heathBrownFullCriticalMoment t) := by
      rw [hdeltaInv]


end

end TaoTrudgianYang2025
