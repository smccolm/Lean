import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Square-root shift sums with their endpoint terms retained. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem inverse_sqrt_succ_le_difference (n : ℕ) :
    1/Real.sqrt (n+1) ≤ 2*(Real.sqrt (n+1)-Real.sqrt n) := by
  have hp : 0 < (n:ℝ)+1 := by positivity
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
    Real.sq_sqrt hp.le,sq_nonneg (Real.sqrt (n+1)-Real.sqrt n)]

theorem sum_inverse_sqrt_Icc (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 H, 1/Real.sqrt (r:ℝ) ≤ 2*Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H+1)]
      have hs := inverse_sqrt_succ_le_difference H
      push_cast
      linarith

theorem sum_shift_inverse_sqrt_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H-1), 1/Real.sqrt (r:ℝ) ≤ 2*Real.sqrt H := by
  exact (sum_inverse_sqrt_Icc (H-1)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by
      exact_mod_cast (show H-1 ≤ H by omega))) (by norm_num))

theorem sum_shift_sqrt_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H-1), Real.sqrt (r:ℝ) ≤ (H:ℝ)*Real.sqrt H := by
  have hc : (Finset.Icc 1 (H-1)).card ≤ H := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 (H-1), Real.sqrt (H:ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Real.sqrt_le_sqrt
      exact_mod_cast (show r ≤ H by have := Finset.mem_Icc.mp hr; omega)
    _ = ((Finset.Icc 1 (H-1)).card:ℝ)*Real.sqrt H := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.sqrt_nonneg _)

end TaoTrudgianYang2025
