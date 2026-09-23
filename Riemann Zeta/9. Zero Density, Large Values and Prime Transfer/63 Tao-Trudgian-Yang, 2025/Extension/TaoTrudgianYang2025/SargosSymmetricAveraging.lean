import TaoTrudgianYang2025.ExponentPairWeylSum

/-! Actual even-shift averaging before symmetric, nonconjugated differencing. -/

noncomputable section

open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosPaddedSequence (a : ℤ → ℂ) (M : ℕ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico (0:ℤ) M then a n else 0

theorem sargosPaddedSequence_eq (a : ℤ → ℂ) (M : ℕ) {n : ℤ}
    (hn : n ∈ Finset.Ico (0:ℤ) M) :
    sargosPaddedSequence a M n = a n := by
  simp only [sargosPaddedSequence,if_pos hn]

theorem sargosPaddedSequence_zero (a : ℤ → ℂ) (M : ℕ) {n : ℤ}
    (hn : n ∉ Finset.Ico (0:ℤ) M) :
    sargosPaddedSequence a M n = 0 := by
  simp only [sargosPaddedSequence,if_neg hn]

theorem sargos_even_shift_sum (a : ℤ → ℂ) (M H h : ℕ) (hh : h < H) :
    (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M, sargosPaddedSequence a M (n+2*h)) =
      ∑ n ∈ Finset.Ico (0:ℤ) M, a n := by
  have he := sum_paddedShift_eq a M (2*H) (2*h) (by omega)
  simpa only [paddedShift,sargosPaddedSequence,Nat.cast_mul,Nat.cast_ofNat] using he

theorem sargos_even_shift_averaging (a : ℤ → ℂ) (M H : ℕ) :
    (H:ℝ)^2*‖∑ n ∈ Finset.Ico (0:ℤ) M, a n‖^2 ≤
      ((M+2*H:ℕ):ℝ)*
        ∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M,
          ‖∑ h ∈ Finset.range H, sargosPaddedSequence a M (n+2*h)‖^2 := by
  let U : ℤ → ℂ := fun n => ∑ h ∈ Finset.range H, sargosPaddedSequence a M (n+2*h)
  have hs : (∑ n ∈ Finset.Ico (-(2*(H:ℤ))) M, U n) =
      H • (∑ n ∈ Finset.Ico (0:ℤ) M, a n) := by
    dsimp [U]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _h ∈ Finset.range H, ∑ n ∈ Finset.Ico (0:ℤ) M, a n := by
        apply Finset.sum_congr rfl
        intro h hh
        exact sargos_even_shift_sum a M H h (Finset.mem_range.mp hh)
      _ = _ := by simp
  have hc : ((Finset.Ico (-(2*(H:ℤ))) M).card : ℝ) = ((M+2*H:ℕ):ℝ) := by
    simp [Int.card_Ico]
    norm_cast
  have ht := norm_sum_sq_le_card_mul_sum_norm_sq
    (Finset.Ico (-(2*(H:ℤ))) M) U
  rw [hs,hc,RCLike.norm_nsmul ℂ,nsmul_eq_mul] at ht
  simpa only [mul_pow] using ht

end TaoTrudgianYang2025
