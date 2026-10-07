import Dubon2026.CuspPeriodFourierEnergy
import Mathlib.NumberTheory.ModularForms.Bounds

/-! # Actual Fourier energy bounds at arbitrary positive cusp periods -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- The genuine Petersson bound controls a cusp form on every arithmetic subgroup at every upper-half-plane point. -/
theorem exists_arithmetic_cusp_norm_sq_bound {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, ‖f τ‖ ^ 2 ≤ C / τ.im ^ k := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f
  refine ⟨|C| + 1, by positivity, fun τ => ?_⟩
  apply (le_div_iff₀ (zpow_pos τ.im_pos k)).mpr
  have hh := hC τ
  have he : ‖petersson k f f τ‖ = ‖f τ‖ ^ 2 * τ.im ^ k := by
    simp [petersson, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos τ.im_pos, pow_two]
  rw [he] at hh
  exact hh.trans (by linarith [le_abs_self C])

/-- The actual normalized width-h horizontal integral has the same Petersson bound. -/
theorem cusp_period_horizontal_energy_le {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) {C : ℝ}
    (hC : ∀ τ : ℍ, ‖f τ‖ ^ 2 ≤ C / τ.im ^ k) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, ‖f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) ≤
      C / y ^ k := by
  have hc : Continuous (fun x : ℝ => f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩) :=
    (ModularFormClass.continuous f).comp
      (((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).add continuous_const).upperHalfPlaneMk
        (fun _ => by simpa using hy))
  have hi := (hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hb (x : ℝ) : ‖f ⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2 ≤ C / y ^ k := by
    simpa only [UpperHalfPlane.im, UpperHalfPlane.coe_mk, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using
      hC (⟨((h * x : ℝ) : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)
  calc
    _ ≤ ∫ _x in (0 : ℝ)..1, C / y ^ k :=
      intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const (fun x _ => hb x)
    _ = _ := by simp

/-- The true q-expansion at any positive cusp period has the exact weight-k square-sum bound, derived from Parseval and Petersson boundedness. -/
theorem exists_cusp_period_coefficient_energy_upper {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ‖(qExpansion h f).coeff n‖ ^ 2) ≤ C * (N : ℝ) ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_arithmetic_cusp_norm_sq_bound f
  refine ⟨Real.exp (4 * Real.pi / h) * C, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hN0
  have hlow : Real.exp (-4 * Real.pi / h) *
      (∑ n ∈ Finset.Icc 1 N, ‖(qExpansion h f).coeff n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, ‖(qExpansion h f).coeff n‖ ^ 2 *
        Real.exp (-4 * Real.pi * n * (N : ℝ)⁻¹ / h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hh).mpr
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn' : (n : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]
      exact hnN
    nlinarith [Real.pi_pos]
  have hd := sum_le_hasSum (Finset.Icc 1 N) (fun _ _ => by positivity)
    (hasSum_cusp_period_horizontal_energy f hh hΓ hy)
  have hb := hlow.trans (hd.trans (cusp_period_horizontal_energy_le f h hC hy))
  have he : Real.exp (4 * Real.pi / h) * Real.exp (-4 * Real.pi / h) = 1 := by
    rw [← Real.exp_add]
    rw [show 4 * Real.pi / h + -4 * Real.pi / h = 0 by ring, Real.exp_zero]
  have ht := mul_le_mul_of_nonneg_left hb (Real.exp_pos (4 * Real.pi / h)).le
  rw [← mul_assoc, he, one_mul, inv_zpow, div_inv_eq_mul] at ht
  simpa only [mul_assoc] using ht

end
end Dubon2026
