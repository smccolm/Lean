import TaoTrudgianYang2025.DoubleShiftWeights

/-! Exact mass and first-moment control of the signed triangular shift weights. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem signed_shift_abs_le {N : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Ioo (-(N:ℤ)) N) : |(q:ℝ)| ≤ N := by
  have ht := Finset.mem_Ioo.mp hq
  have ha : |q| ≤ (N:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  exact_mod_cast ha

theorem signed_triangular_weight_nonneg {N : ℕ} (hN : 0 < N) {q : ℤ}
    (hq : q ∈ Finset.Ioo (-(N:ℤ)) N) : 0 ≤ 1-|(q:ℝ)|/N := by
  have hp : (0:ℝ) < N := by exact_mod_cast hN
  have ha := signed_shift_abs_le hq
  exact sub_nonneg.mpr ((div_le_one hp).mpr ha)

theorem sum_signed_triangular_weights (N : ℕ) (hN : 0 < N) :
    (∑ q ∈ Finset.Ioo (-(N:ℤ)) N, (1-|(q:ℝ)|/N)) = N := by
  have hp : (N:ℝ) ≠ 0 := by positivity
  have ht := sum_signed_shift_differences N (fun _ => (1:ℝ))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at ht
  calc
    _ = ∑ q ∈ Finset.Ioo (-(N:ℤ)) N, (((N-q.natAbs:ℕ):ℝ)/N) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [signed_shift_weight_real hq]
      field_simp
    _ = (∑ q ∈ Finset.Ioo (-(N:ℤ)) N, ((N-q.natAbs:ℕ):ℝ))/N := by
      rw [Finset.sum_div]
    _ = N := by
      rw [← ht]
      field_simp

theorem signed_triangular_first_moment (N : ℕ) (hN : 0 < N) :
    (∑ q ∈ Finset.Ioo (-(N:ℤ)) N, (1-|(q:ℝ)|/N)*|(q:ℝ)|) ≤ (N:ℝ)^2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioo (-(N:ℤ)) N, (1-|(q:ℝ)|/N)*(N:ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (signed_shift_abs_le hq)
        (signed_triangular_weight_nonneg hN hq)
    _ = (N:ℝ)^2 := by
      rw [← Finset.sum_mul,sum_signed_triangular_weights N hN]
      ring

end TaoTrudgianYang2025
