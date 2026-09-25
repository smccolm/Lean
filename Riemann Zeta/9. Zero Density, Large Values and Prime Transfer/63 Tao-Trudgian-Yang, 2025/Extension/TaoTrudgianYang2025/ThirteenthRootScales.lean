import TaoTrudgianYang2025.RobertSargosPhysicalShift

/-! Exact thirteenth-root powers and positive floor losses at the paper scale. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem thirteenth_root_nat_pow {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    (lam^(-(1:ℝ)/13))^n = lam^(-(n:ℝ)/13) := by
  rw [← Real.rpow_mul_natCast hlam.le]
  congr 1
  ring

theorem thirteenth_root_physical_scale {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192) :
    2 ≤ lam^(-(1:ℝ)/13) ∧ (lam^(-(1:ℝ)/13))^13*lam = 1 := by
  have he : (1/8192:ℝ) = (2:ℝ)^(-(13:ℝ)) := by norm_num
  have hb := Real.rpow_le_rpow_of_nonpos hlam hsmall
    (show -(1:ℝ)/13 ≤ 0 by norm_num)
  rw [he,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hb
  norm_num at hb
  refine ⟨by simpa only [neg_div] using hb,?_⟩
  rw [thirteenth_root_nat_pow hlam]
  norm_num
  rw [Real.rpow_neg_one,inv_mul_cancel₀ hlam.ne']

theorem positive_floor_half_bounds {X : ℝ} (hX : 1 ≤ X) :
    0 < ⌊X⌋₊ ∧ X/2 ≤ (⌊X⌋₊:ℝ) ∧ (⌊X⌋₊:ℝ) ≤ X := by
  have hp : 0 < ⌊X⌋₊ := Nat.floor_pos.mpr hX
  have h1 : (1:ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hp
  have hn := Nat.lt_floor_add_one X
  exact ⟨hp,by linarith,Nat.floor_le (by linarith)⟩

end TaoTrudgianYang2025
