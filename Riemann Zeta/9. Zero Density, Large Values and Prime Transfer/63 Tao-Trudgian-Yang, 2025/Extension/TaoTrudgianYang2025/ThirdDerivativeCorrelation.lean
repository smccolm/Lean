import TaoTrudgianYang2025.ContinuousSecondDerivative
import TaoTrudgianYang2025.ThirdDerivativeShift

/-! Actual finite shifted correlation bounded from continuous third derivatives. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem continuous_third_derivative_correlation
    (F F' F'' F''' : ℝ → ℝ) (A : ℝ) (N r : ℕ) {C μ : ℝ}
    (hC : 0 ≤ C) (hμ : 0 < μ) (hr : 0 < r) (hrμ : (r:ℝ)*μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x ∈ Icc A (A+N), HasDerivAt F'' (F''' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), μ ≤ F''' x)
    (hhi : ∀ x ∈ Icc A (A+N), F''' x ≤ C*μ) :
    ‖∑ n ∈ Finset.range (N-r),
      fordAdditiveCharacter (F (A+n+r)-F (A+n))‖ ≤
        12*(C*N*Real.sqrt ((r:ℝ)*μ)+2/Real.sqrt ((r:ℝ)*μ)) := by
  by_cases hnr : r < N
  · let L := N-r-1
    have hlen : N-r = L+1 := by dsimp [L]; omega
    have hlenR : (L:ℝ)+1+(r:ℝ) = N := by
      exact_mod_cast (show L+1+r = N by dsimp [L]; omega)
    have hin (x : ℝ) (hx : x ∈ Icc A (A+L+1)) :
        x ∈ Icc A (A+N) ∧ x+r ∈ Icc A (A+N) := by
      constructor <;> constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r,hx.1,hx.2]
    have hcurv (x : ℝ) (hx : x ∈ Icc A (A+L+1)) :
        (r:ℝ)*μ ≤ F'' (x+r)-F'' x ∧ F'' (x+r)-F'' x ≤ C*((r:ℝ)*μ) := by
      have hb := third_derivative_shift_curvature F'' F'''
        (Nat.cast_nonneg r) (hin x hx).1.1 (hin x hx).2.2 hF'' hlo hhi
      simpa only [mul_left_comm] using hb
    have hb := continuous_second_derivative_bound
      (fun x => F (x+r)-F x) (fun x => F' (x+r)-F' x)
      (fun x => F'' (x+r)-F'' x) A L hC
      (mul_pos (by exact_mod_cast hr) hμ) hrμ
      (fun x hx => hasDerivAt_shift_difference F F' (hF x (hin x hx).1)
        (hF (x+r) (hin x hx).2))
      (fun x hx => hasDerivAt_shift_difference F' F'' (hF' x (hin x hx).1)
        (hF' (x+r) (hin x hx).2))
      (fun x hx => (hcurv x hx).1) (fun x hx => (hcurv x hx).2)
    rw [hlen]
    exact hb.trans (by
      have hLN : (L:ℝ) ≤ N := by exact_mod_cast (show L ≤ N by dsimp [L]; omega)
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLN hC) (Real.sqrt_nonneg ((r:ℝ)*μ))
      linarith)
  · have he : N-r = 0 := by omega
    rw [he,Finset.sum_range_zero,norm_zero]
    positivity

end TaoTrudgianYang2025
