import Dubon2026.FiniteSpectralLog

/-! # Three-four-one positivity for genuine finite Euler factors -/

namespace Dubon2026

noncomputable section

/-- Unit rotation preserves the norm of every actual spectral coordinate. -/
theorem norm_spectral_unit_rotation {w a z : ℂ} (hz : ‖z‖ = 1) :
    ‖w * (a * z)‖ = ‖w * a‖ := by
  rw [← mul_assoc, norm_mul, hz, mul_one]

/-- Nonnegative real spectral power traces make the exact finite logarithmic three-four-one combination nonnegative. -/
theorem finiteSpectralLog_three_four_one {d : ℕ} (w : Fin d → ℂ) {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, ‖w i * (a : ℂ)‖ < 1)
    (htrace : ∀ r : ℕ, (∑ i : Fin d, w i ^ r).im = 0 ∧ 0 ≤ (∑ i : Fin d, w i ^ r).re)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (finiteSpectralLog w a).re + 4 * (finiteSpectralLog w ((a : ℂ) * z)).re +
      (finiteSpectralLog w ((a : ℂ) * z ^ 2)).re := by
  let c : ℕ → ℝ := fun r => (∑ i : Fin d, w i ^ r).re * a ^ r / r
  have hc : ∀ r, 0 ≤ c r := fun r =>
    div_nonneg (mul_nonneg (htrace r).2 (pow_nonneg ha r)) (Nat.cast_nonneg r)
  have hsum : ∀ u : ℂ, ‖u‖ = 1 →
      HasSum (fun r : ℕ => (c r : ℂ) * u ^ r) (finiteSpectralLog w ((a : ℂ) * u)) := by
    intro u hu
    have hh := finiteSpectralLog_hasSum w (fun i => by
      rw [norm_spectral_unit_rotation hu]
      exact hw i)
    convert hh using 1
    funext r
    have hr : (∑ i : Fin d, w i ^ r) = ((∑ i : Fin d, w i ^ r).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using (htrace r).1)
    rw [hr, mul_pow]
    dsimp only [c]
    push_cast
    ring
  have h0 := hsum 1 (norm_one (α := ℂ))
  simp only [mul_one, one_pow] at h0
  have h1 := hsum z hz
  have h2 := hsum (z ^ 2) (by rw [norm_pow, hz, one_pow])
  have ht := (((Complex.hasSum_re h0).mul_left 3).add
    ((Complex.hasSum_re h1).mul_left 4)).add (Complex.hasSum_re h2)
  rw [← ht.tsum_eq]
  apply tsum_nonneg
  intro r
  have hp : (z ^ 2) ^ r = (z ^ r) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 r]
  simpa only [Complex.ofReal_re, hp] using
    real_weighted_three_four_one (hc r) (z := z ^ r) (by rw [norm_pow, hz, one_pow])

/-- The actual product of reciprocal finite Euler factors satisfies the three-four-one norm inequality whenever its power traces are real and nonnegative. -/
theorem finiteSpectralEuler_three_four_one {d : ℕ} (w : Fin d → ℂ) {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ i, ‖w i * (a : ℂ)‖ < 1)
    (htrace : ∀ r : ℕ, (∑ i : Fin d, w i ^ r).im = 0 ∧ 0 ≤ (∑ i : Fin d, w i ^ r).re)
    {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖((∏ i : Fin d, (1 - w i * (a : ℂ)))⁻¹) ^ 3 *
      ((∏ i : Fin d, (1 - w i * ((a : ℂ) * z)))⁻¹) ^ 4 *
        ((∏ i : Fin d, (1 - w i * ((a : ℂ) * z ^ 2)))⁻¹)‖ := by
  have hn : ∀ u : ℂ, ‖u‖ = 1 → ∀ i : Fin d, 1 - w i * ((a : ℂ) * u) ≠ 0 := by
    intro u hu i he
    have hl : ‖w i * ((a : ℂ) * u)‖ < 1 := by rw [norm_spectral_unit_rotation hu]; exact hw i
    rw [← sub_eq_zero.mp he, norm_one] at hl
    exact lt_irrefl _ hl
  have h0 : ∀ i, 1 - w i * (a : ℂ) ≠ 0 := by simpa only [mul_one] using hn 1 (norm_one (α := ℂ))
  rw [← exp_finiteSpectralLog w h0, ← exp_finiteSpectralLog w (hn z hz),
    ← exp_finiteSpectralLog w (hn (z ^ 2) (by rw [norm_pow, hz, one_pow]))]
  simp only [← Complex.exp_nat_mul, Nat.cast_ofNat, ← Complex.exp_add, Complex.norm_exp,
    Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    Real.one_le_exp_iff]
  exact finiteSpectralLog_three_four_one w ha hw htrace hz

end
end Dubon2026
