import TaoTrudgianYang2025.SargosKernelBasic

/-!
# Real-frequency tent integral

The symmetry calculation follows the pinned Ford tent proof, but its
frequency is an arbitrary real number. It reuses the proved real-frequency
cosine integral and exact additive character identity. The zero frequency
is retained explicitly.
-/

noncomputable section

open MeasureTheory Set GafniTao

namespace TaoTrudgianYang2025

theorem sargosSincKernel_eq_sin {w ξ : ℝ} (hw : w ≠ 0) (hξ : ξ ≠ 0) :
    sargosSincKernel w ξ =
      Real.sin (Real.pi*ξ*w)^2/(Real.pi^2*w*ξ^2) := by
  unfold sargosSincKernel
  rw [show Real.pi*w*ξ = Real.pi*ξ*w by ring,
    Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero Real.pi_ne_zero hξ) hw)]
  field_simp

theorem sargos_integral_symmetric_tent_character
    {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    (∫ x in -w..w,
        ((1 - |x| / w : ℝ) : ℂ) *
          fordAdditiveCharacter (-(ξ * x))) =
      ((2 * ∫ x in (0 : ℝ)..w,
          (1 - x / w) * Real.cos (2 * Real.pi * ξ * x) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    ((1 - |x| / w : ℝ) : ℂ) * fordAdditiveCharacter (-(ξ * x))
  have hchar : Continuous fordAdditiveCharacter := by
    unfold fordAdditiveCharacter
    fun_prop
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hf : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    exact hfcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf (-w) 0) (hf 0 w)]
  have hneg :
      (∫ x in (0 : ℝ)..w, f (-x)) = ∫ x in -w..0, f x := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  have hfneg : IntervalIntegrable (fun x : ℝ => f (-x))
      MeasureTheory.volume 0 w := by
    simpa only [Function.comp_apply] using
      (hfcont.comp continuous_neg).intervalIntegrable (0 : ℝ) w
  rw [← hneg, ← intervalIntegral.integral_add
    hfneg (hf 0 w)]
  calc
    (∫ x in (0 : ℝ)..w, f (-x) + f x) =
        ∫ x in (0 : ℝ)..w,
          ((2 * ((1 - x / w) * Real.cos (2 * Real.pi * ξ * x)) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by
        rcases Set.mem_uIcc.mp hx with h | h
        · exact h.1
        · linarith
      simp only [f, abs_neg, abs_of_nonneg hx0]
      rw [show -(ξ * -x) = ξ * x by ring]
      rw [← mul_add]
      rw [fordAdditiveCharacter_pair_eq_cos]
      push_cast
      ring_nf
    _ = ((∫ x in (0 : ℝ)..w,
          2 * ((1 - x / w) * Real.cos (2 * Real.pi * ξ * x)) : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    _ = ((2 * ∫ x in (0 : ℝ)..w,
          (1 - x / w) * Real.cos (2 * Real.pi * ξ * x) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul]


theorem sargos_integral_symmetric_tent_character_eq_kernel
    {w : ℝ} (hw : 0 < w) (ξ : ℝ) :
    (∫ x in -w..w,
        ((1-|x|/w : ℝ) : ℂ)*fordAdditiveCharacter (-(ξ*x))) =
      (sargosSincKernel w ξ : ℂ) := by
  rw [sargos_integral_symmetric_tent_character hw ξ]
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [zero_mul,Real.cos_zero,mul_one,sargosSincKernel,mul_zero,
      Real.sinc_zero,one_pow]
    have hlinear : (∫ x in (0 : ℝ)..w, (1-x/w)) = w/2 := by
      have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 w :=
        continuous_const.intervalIntegrable 0 w
      have hquot : IntervalIntegrable (fun x : ℝ => x/w) volume 0 w :=
        (by fun_prop : Continuous fun x : ℝ => x/w).intervalIntegrable 0 w
      rw [intervalIntegral.integral_sub hone hquot]
      simp only [intervalIntegral.integral_const,intervalIntegral.integral_div,
        integral_id,sub_zero,smul_eq_mul,pow_succ]
      field_simp [hw.ne']
      ring
    rw [hlinear]
    norm_cast
    ring
  · have ha : 2*Real.pi*ξ ≠ 0 := by positivity
    rw [ford_integral_linear_tent_cos hw.ne' ha,sargosSincKernel_eq_sin hw.ne' hξ]
    norm_cast
    rw [show (2*Real.pi*ξ)*w = 2*(Real.pi*ξ*w) by ring]
    have htrig : 1-Real.cos (2*(Real.pi*ξ*w)) = 2*Real.sin (Real.pi*ξ*w)^2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi*ξ*w)]
    rw [htrig]
    field_simp [Real.pi_ne_zero,hw.ne',hξ]

end TaoTrudgianYang2025
