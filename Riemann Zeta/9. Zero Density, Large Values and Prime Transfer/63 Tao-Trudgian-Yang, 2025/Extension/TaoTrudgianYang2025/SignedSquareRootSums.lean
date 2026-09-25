import TaoTrudgianYang2025.SignedEvenSum
import TaoTrudgianYang2025.SquareRootShiftSums

/-! Exact positive/signed integer shift bridges for the zero-r square-root sums. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_positive_int_eq_nat_Icc (f : ℤ → ℝ) (Q : ℕ) :
    (∑ q ∈ Finset.Ioo (0:ℤ) Q, f q) =
      ∑ q ∈ Finset.Icc 1 (Q-1), f q := by
  symm
  apply Finset.sum_bij (fun (q : ℕ) _ => (q:ℤ))
  · intro q hq
    have hi := Finset.mem_Icc.mp hq
    exact Finset.mem_Ioo.mpr ⟨by omega,by omega⟩
  · intro q _ r _ he
    exact_mod_cast he
  · intro q hq
    have hi := Finset.mem_Ioo.mp hq
    refine ⟨q.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Int.toNat_of_nonneg (by omega)⟩
  · intro _ _
    rfl

theorem sum_signed_sqrt_le (Q : ℕ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, Real.sqrt |(q:ℝ)|) ≤
      2*(Q:ℝ)*Real.sqrt Q := by
  by_cases hQ : 0 < Q
  · rw [sum_signed_even _ Q hQ (by intro n; simp),
      sum_positive_int_eq_nat_Icc]
    simp only [Int.cast_zero,abs_zero,Real.sqrt_zero,zero_add,Int.cast_natCast,Nat.abs_cast]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (sum_shift_sqrt_le Q) (by norm_num : (0:ℝ) ≤ 2)
  · have he : Q = 0 := by omega
    subst Q
    simp

theorem sum_signed_inverse_sqrt_le (Q : ℕ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, 1/Real.sqrt |(q:ℝ)|) ≤
      4*Real.sqrt Q := by
  by_cases hQ : 0 < Q
  · rw [sum_signed_even _ Q hQ (by intro n; simp),
      sum_positive_int_eq_nat_Icc]
    simp only [Int.cast_zero,abs_zero,Real.sqrt_zero,div_zero,zero_add,Int.cast_natCast,Nat.abs_cast]
    have hs := mul_le_mul_of_nonneg_left (sum_shift_inverse_sqrt_le Q)
      (by norm_num : (0:ℝ) ≤ 2)
    linarith
  · have he : Q = 0 := by omega
    subst Q
    simp

end TaoTrudgianYang2025
