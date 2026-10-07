import Dubon2026.CuspFourierEnergy
import Mathlib.NumberTheory.ModularForms.Bounds

/-! # Unconditional upper bounds for the actual cusp-form Fourier energy -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- Continuity of the actual cusp form along a horizontal line in the upper half-plane. -/
theorem continuous_cusp_horizontal {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩) := by
  exact (ModularFormClass.continuous f).comp
    ((Complex.continuous_ofReal.add continuous_const).upperHalfPlaneMk
      (fun _ => by simpa using hy))

/-- The genuine Petersson bound gives one constant valid at every upper-half-plane point. -/
theorem exists_cusp_norm_sq_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, ‖f τ‖ ^ 2 ≤ C / τ.im ^ k := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) f f
  refine ⟨|C| + 1, by positivity, fun τ => ?_⟩
  apply (le_div_iff₀ (zpow_pos τ.im_pos k)).mpr
  have hh := hC τ
  have he : ‖petersson k f f τ‖ = ‖f τ‖ ^ 2 * τ.im ^ k := by
    simp [petersson, norm_zpow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos τ.im_pos, pow_two]
  rw [he] at hh
  exact hh.trans (by linarith [le_abs_self C])

/-- The actual horizontal integral is bounded by the same global Petersson constant. -/
theorem cusp_horizontal_energy_le {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) {C : ℝ}
    (hC : ∀ τ : ℍ, ‖f τ‖ ^ 2 ≤ C / τ.im ^ k) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, ‖f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) ≤
      C / y ^ k := by
  have hi := ((continuous_cusp_horizontal f hy).norm.pow 2).intervalIntegrable
    (μ := volume) 0 1
  have hb (x : ℝ) : ‖f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2 ≤ C / y ^ k := by
    have ht := hC (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)
    simpa only [UpperHalfPlane.im, UpperHalfPlane.coe_mk,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using ht
  calc
    _ ≤ ∫ _x in (0 : ℝ)..1, C / y ^ k :=
      intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const
        (fun x _ => hb x)
    _ = _ := by simp

/-- Every finite damped Fourier energy is bounded by the literal horizontal integral. -/
theorem cusp_damped_energy_le {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) (S : Finset ℕ) :
    (∑ n ∈ S, ‖cuspCoefficients f n‖ ^ 2 * Real.exp (-4 * Real.pi * n * y)) ≤
      (∫ x in (0 : ℝ)..1, ‖f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩‖ ^ 2) :=
  sum_le_hasSum S (fun _ _ => by positivity) (hasSum_cusp_horizontal_energy f hy)

/-- An unconditional square-sum upper bound from the actual q-expansion and Petersson estimate.
This supplies an analytic growth bound, not the Rankin--Selberg main term or remainder. -/
theorem exists_cusp_coefficient_energy_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2) ≤ C * (N : ℝ) ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_cusp_norm_sq_bound f
  refine ⟨Real.exp (4 * Real.pi) * C, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hN0
  have hlow : Real.exp (-4 * Real.pi) *
      (∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, ‖cuspCoefficients f n‖ ^ 2 *
        Real.exp (-4 * Real.pi * n * (N : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn' : (n : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]
      exact hnN
    nlinarith [Real.pi_pos]
  have hb := hlow.trans ((cusp_damped_energy_le f hy _).trans (cusp_horizontal_energy_le f hC hy))
  have he : Real.exp (4 * Real.pi) * Real.exp (-4 * Real.pi) = 1 := by
    rw [← Real.exp_add]
    simp
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (4 * Real.pi)).le
  rw [← mul_assoc, he, one_mul, inv_zpow, div_inv_eq_mul] at hh
  simpa only [mul_assoc] using hh

end
end Dubon2026
