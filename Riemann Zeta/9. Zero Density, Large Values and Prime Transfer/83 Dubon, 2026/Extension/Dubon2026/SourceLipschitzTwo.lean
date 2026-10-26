import Mathlib

/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

theorem summable_one_div_add_int_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w + n) ^ 2 := by
  simpa [one_div] using EisensteinSeries.linear_right_summable w 1 (k := 2) le_rfl

theorem tsum_one_div_add_int_sq_neg (w : ℂ) :
    ∑' n : ℤ, 1 / (-w + n) ^ 2 = ∑' n : ℤ, 1 / (w + n) ^ 2 := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

theorem tsum_one_div_sub_int_sq (w : ℂ) :
    ∑' n : ℤ, 1 / (w - n) ^ 2 = ∑' n : ℤ, 1 / (w + n) ^ 2 := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [sub_eq_add_neg]

theorem lipschitz_two_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨w, hw⟩
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h]
  ring

theorem lipschitz_two_of_im_neg {w : ℂ} (hw : w.im < 0) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m := by
  rw [← tsum_one_div_add_int_sq_neg, lipschitz_two_of_im_pos (w := -w) (by simpa using hw)]
  simp [mul_neg]

theorem summable_nat_mul_cexp_pow {w : ℂ} (hw : 0 < w.im) :
    Summable fun m : ℕ ↦ (m : ℂ) * cexp (2 * π * I * w) ^ m := by
  simpa using summable_pow_mul_cexp 1 1 ⟨w, hw⟩

theorem cexp_two_pi_I_mul_ne_one {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    cexp (2 * π * I * x) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have : x = n := by
    have := congrArg (· / (2 * π * I)) hn
    simpa [mul_div_assoc, div_self h2, mul_comm] using this
  exact hx ⟨n, this.symm⟩

theorem lipschitz_two_closed_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  rw [lipschitz_two_of_im_pos hx, tsum_coe_mul_geometric_of_norm_lt_one]
  simpa using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩

theorem lipschitz_two_closed_of_im_neg {x : ℂ} (hx : x.im < 0) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  have hr : ‖cexp (-(2 * π * I * x))‖ < 1 := by
    simpa [mul_neg] using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-x, by simpa using hx⟩
  have hq0 : cexp (2 * π * I * x) ≠ 0 := Complex.exp_ne_zero _
  have hq1 : 1 - cexp (2 * π * I * x) ≠ 0 := by
    intro h0
    have h1 : ‖cexp (2 * π * I * x)‖ = 1 := by rw [(sub_eq_zero.mp h0).symm, norm_one]
    rw [Complex.norm_exp] at h1
    have : (2 * π * I * x).re = -(2 * π * x.im) := by simp [mul_comm]
    rw [this, Real.exp_eq_one_iff] at h1
    nlinarith [Real.pi_pos]
  have hr1 : 1 - cexp (-(2 * π * I * x)) ≠ 0 := by
    rw [Complex.exp_neg]
    intro h0
    apply hq1
    have := sub_eq_zero.mp h0
    rw [eq_comm, inv_eq_one] at this
    simp [this]
  rw [lipschitz_two_of_im_neg hx, tsum_coe_mul_geometric_of_norm_lt_one hr]
  congr 1
  rw [Complex.exp_neg] at hr1 ⊢
  rw [div_eq_div_iff (pow_ne_zero 2 hr1) (pow_ne_zero 2 hq1)]
  field_simp
  ring


end
end Dubon2026.SourceFricke
