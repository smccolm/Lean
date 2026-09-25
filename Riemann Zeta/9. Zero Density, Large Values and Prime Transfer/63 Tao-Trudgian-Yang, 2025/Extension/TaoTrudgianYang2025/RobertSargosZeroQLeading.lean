import TaoTrudgianYang2025.RobertSargosZeroQPhase

/-! Ordinary third-derivative control of the genuine zero-q leading phase. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_leading_prefix
    (f : ℝ → ℝ) (A : ℝ) (N : ℕ) {r C lam : ℝ}
    (hr : r ≠ 0) (hC : 1 ≤ C) (hlam : 0 < lam) (hscale : 2*|r| *lam ≤ 1)
    (hf : ∀ x ∈ Icc A (A+N), ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc A (A+N), lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc A (A+N), iteratedDeriv 4 f x ≤ C*lam) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (robertSargosZeroQLeading f r (A+n))‖ ≤
      20*C*((N:ℝ)*(2*|r| *lam)^((1:ℝ)/6)+Real.sqrt N*(2*|r| *lam)^(-(1:ℝ)/6)) := by
  have hj (j : ℕ) (hj : j < 3) (x : ℝ) (hx : x ∈ Icc A (A+N)) :=
    hasDerivAt_robertSargos_zero_q_leading_jet (r := r) hj (hf x hx)
  by_cases hrp : 0 < r
  · rw [abs_of_pos hrp] at hscale ⊢
    exact continuous_third_derivative_negative_bound
      (robertSargosZeroQLeading f r) (fun x => -2*r*iteratedDeriv 2 f x)
      (fun x => -2*r*iteratedDeriv 3 f x) (fun x => -2*r*iteratedDeriv 4 f x)
      A N hC (by positivity) hscale
      (fun x hx => hj 0 (by norm_num) x hx)
      (fun x hx => hj 1 (by norm_num) x hx)
      (fun x hx => hj 2 (by norm_num) x hx)
      (fun x hx => by nlinarith [mul_le_mul_of_nonneg_left (hhi x hx) hrp.le])
      (fun x hx => by nlinarith [mul_le_mul_of_nonneg_left (hlo x hx) hrp.le])
  · have hrn : r < 0 := lt_of_le_of_ne (le_of_not_gt hrp) hr
    have hneg : 0 < -r := neg_pos.mpr hrn
    rw [abs_of_neg hrn] at hscale ⊢
    exact continuous_third_derivative_bound
      (robertSargosZeroQLeading f r) (fun x => -2*r*iteratedDeriv 2 f x)
      (fun x => -2*r*iteratedDeriv 3 f x) (fun x => -2*r*iteratedDeriv 4 f x)
      A N hC (by positivity) hscale
      (fun x hx => hj 0 (by norm_num) x hx)
      (fun x hx => hj 1 (by norm_num) x hx)
      (fun x hx => hj 2 (by norm_num) x hx)
      (fun x hx => by nlinarith [mul_le_mul_of_nonneg_left (hlo x hx) (neg_nonneg.mpr hrn.le)])
      (fun x hx => by nlinarith [mul_le_mul_of_nonneg_left (hhi x hx) (neg_nonneg.mpr hrn.le)])

end TaoTrudgianYang2025
