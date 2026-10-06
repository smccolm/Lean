import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Symmetric vertical averaging and nonzero Fourier frequencies -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The source's symmetric interval mean. At height zero its totalized value is zero. -/
def symmetricAverage (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  (2 * T)⁻¹ • ∫ t in -T..T, f t

theorem symmetricAverage_zero (T : ℝ) : symmetricAverage (fun _ => 0) T = 0 := by
  simp [symmetricAverage]

theorem symmetricAverage_const (c : ℂ) {T : ℝ} (hT : T ≠ 0) :
    symmetricAverage (fun _ => c) T = c := by
  simp only [symmetricAverage, intervalIntegral.integral_const, sub_neg_eq_add,
    ← two_mul, smul_smul]
  rw [inv_mul_cancel₀ (mul_ne_zero two_ne_zero hT), one_smul]

theorem symmetricAverage_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    symmetricAverage (fun t => f t + g t) T = symmetricAverage f T + symmetricAverage g T := by
  rw [symmetricAverage, intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), smul_add]
  rfl

theorem symmetricAverage_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    symmetricAverage (fun t => f t - g t) T = symmetricAverage f T - symmetricAverage g T := by
  rw [symmetricAverage, intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), smul_sub]
  rfl

theorem symmetricAverage_smul (c : ℂ) (f : ℝ → ℂ) (T : ℝ) :
    symmetricAverage (fun t => c • f t) T = c • symmetricAverage f T := by
  rw [symmetricAverage, intervalIntegral.integral_smul, smul_comm]
  rfl

theorem norm_symmetricAverage_le {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C) (T : ℝ) : ‖symmetricAverage f T‖ ≤ C := by
  by_cases hT : T = 0
  · simpa [symmetricAverage, hT] using hC
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (fun t _ => hf t)
  rw [symmetricAverage, norm_smul, Real.norm_eq_abs]
  calc
    |(2 * T)⁻¹| * ‖∫ t in -T..T, f t‖ ≤ |(2 * T)⁻¹| * (C * |T - -T|) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = C := by
      rw [sub_neg_eq_add, ← two_mul, abs_inv]
      field_simp

theorem norm_exp_negative_frequency (ω t : ℝ) :
    ‖Complex.exp ((-Complex.I * (ω : ℂ)) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_symmetricAverage_exp_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖symmetricAverage (fun t => Complex.exp ((-Complex.I * (ω : ℂ)) * (t : ℂ))) T‖ ≤
      |(2 * T)⁻¹| * (2 / |ω|) := by
  have hc : -Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hω)
  rw [symmetricAverage, norm_smul, Real.norm_eq_abs, integral_exp_mul_complex hc, norm_div]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hn : ‖-Complex.I * (ω : ℂ)‖ = |ω| := by simp
  rw [hn]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ ‖Complex.exp ((-Complex.I * (ω : ℂ)) * (T : ℂ))‖ +
      ‖Complex.exp ((-Complex.I * (ω : ℂ)) * ((-T : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_exp_negative_frequency, norm_exp_negative_frequency]; norm_num

theorem tendsto_symmetricAverage_exp_zero {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (symmetricAverage (fun t => Complex.exp ((-Complex.I * (ω : ℂ)) * (t : ℂ))))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_symmetricAverage_exp_le hω)
  have hi : Tendsto (fun T : ℝ => (2 * T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (by norm_num))
  simpa using hi.abs.mul_const (2 / |ω|)

end

end Dubon2026
