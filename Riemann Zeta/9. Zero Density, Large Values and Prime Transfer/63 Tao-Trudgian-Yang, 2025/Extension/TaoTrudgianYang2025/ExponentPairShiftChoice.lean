import TaoTrudgianYang2025.ExponentPairDifferencingBound

/-! Actual integer shifts at a prescribed positive optimization scale. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_comparable_source_shift
    {η R N : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) (hRN : R ≤ N)
    (hlarge : 2 ≤ η*R) :
    ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ η*N ∧
      η*R/2 ≤ (H : ℝ) ∧ (H : ℝ) ≤ R := by
  let H := Nat.floor (η*R)
  have hH₁ : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (by linarith)).ne'
  have hfloor : (H : ℝ) ≤ η*R := Nat.floor_le (by linarith)
  have hfloor' : η*R < (H : ℝ)+1 := Nat.lt_floor_add_one _
  have hR : 0 < R := by nlinarith
  refine ⟨H,hH₁,hfloor.trans (mul_le_mul_of_nonneg_left hRN hη.le),?_,?_⟩
  · linarith
  · exact hfloor.trans (by nlinarith)

end TaoTrudgianYang2025
