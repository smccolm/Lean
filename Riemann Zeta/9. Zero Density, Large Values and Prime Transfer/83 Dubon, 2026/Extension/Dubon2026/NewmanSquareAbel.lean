import Dubon2026.NewmanSquareLaplace

/-! # Exact finite Abel identity for the actual logarithmic square-mean error -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The logarithmic cutoff maps to the exact finite positive-index Mellin interval. -/
theorem newman_exp_image_Ioc_log {X : ℝ} (hX : 1 ≤ X) :
    Real.exp '' Ioc 0 (Real.log X) = Ioc 1 X := by
  have hX0 : 0 < X := by linarith
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.one_lt_exp_iff.mpr ht.1, (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log hX0)⟩
  · intro hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact ⟨Real.log x, ⟨Real.log_pos hx.1, Real.log_le_log hx0 hx.2⟩, Real.exp_log hx0⟩

/-- The real exponential Jacobian converts the actual normalized summatory remainder into the centered mean. -/
theorem newman_square_error_jacobian (a : ℕ → ℂ) (c t : ℝ) :
    |Real.exp t| • (((squareSummatory a (Real.exp t) - c * Real.exp t) *
      (Real.exp t) ^ (-2 : ℝ) : ℝ) : ℂ) = newmanSquareError a c t := by
  rw [abs_of_pos (Real.exp_pos t), Real.rpow_neg (Real.exp_pos t).le, Real.rpow_two]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_inv, Complex.ofReal_pow, newmanSquareError, newmanSquareMean]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)]

/-- A genuine finite change of variables identifies the Tauberian integral with the exact Abel remainder. -/
theorem newman_square_error_integral (a : ℕ → ℂ) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in (0 : ℝ)..Real.log N, newmanSquareError a c t) =
      ((∫ x in Ioc (1 : ℝ) N, (squareSummatory a x - c * x) * x ^ (-2 : ℝ) : ℝ) : ℂ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (0 : ℝ) (Real.log N)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun x : ℝ => (((squareSummatory a x - c * x) * x ^ (-2 : ℝ) : ℝ) : ℂ))
  rw [newman_exp_image_Ioc_log hNr] at hi
  simp_rw [newman_square_error_jacobian] at hi
  rw [integral_complex_ofReal] at hi
  rw [intervalIntegral.integral_of_le (Real.log_nonneg hNr)]
  exact hi.symm

/-- The actual central weighted energy is exactly the square mean plus its Tauberian integral. -/
theorem coefficientEnergy_center_tauberian_identity (a : ℕ → ℂ) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    coefficientEnergy a N (1 / 2) - c * Real.log N = squareSummatory a N / N +
      (∫ t in (0 : ℝ)..Real.log N, newmanSquareError a c t).re := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have ha := coefficientEnergy_sub_main a hN (1 / 2) c
  norm_num only at ha
  rw [weightedEnergyMain_center hN c, Real.rpow_neg_one] at ha
  rw [newman_square_error_integral a c hN, Complex.ofReal_re]
  have he : (squareSummatory a N - c * N) * (N : ℝ)⁻¹ = squareSummatory a N / N - c := by
    field_simp
  rw [he] at ha
  linarith

end
end Dubon2026
