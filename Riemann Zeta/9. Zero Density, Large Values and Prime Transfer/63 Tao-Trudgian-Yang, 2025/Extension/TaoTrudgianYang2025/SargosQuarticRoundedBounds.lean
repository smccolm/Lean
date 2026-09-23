import TaoTrudgianYang2025.SargosQuarticStationaryWidth

/-! Actual quartic endpoint and rounded-integer budgets at the physical scale. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticSlope_scaled_abs_le {N α γ u : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hu : u ∈ Icc (1:ℝ) 2) :
    |sargosQuarticSlope α γ (N*u)| ≤ 6*α*N := by
  have hp := sargosQuarticSlope_normalize hN.ne' hα.ne' γ (N*u)
  rw [mul_div_cancel_left₀ _ hN.ne'] at hp
  rw [← hp,abs_mul,abs_of_pos (mul_pos hα hN)]
  have h := mul_le_mul_of_nonneg_left (sargosQuartic_normalized_slope_bound
    (sargosQuartic_normalized_coefficient_bound hN hα hγ) hu) (mul_pos hα hN).le
  exact h.trans_eq (by ring)

theorem sargos_rounding_natAbs_bound {x B : ℝ} (hx : |x| ≤ B) :
    ((⌊x⌋ : ℤ).natAbs : ℝ) ≤ B+1 ∧ ((⌈x⌉ : ℤ).natAbs : ℝ) ≤ B+1 := by
  have hh := abs_le.mp hx
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have hc := Int.le_ceil x
  have hc' := Int.ceil_lt_add_one x
  simp only [Nat.cast_natAbs,Int.cast_abs]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hh.1,hh.2]

theorem sargosQuarticBand_natAbs_bounds {N α γ l b η : ℝ}
    (hN : 1 ≤ N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    ((sargosQuarticSupportLower N α γ l η).natAbs : ℝ) ≤ 6*(α*N^2)+1 ∧
      ((sargosQuarticSupportUpper N α γ b η).natAbs : ℝ) ≤ 6*(α*N^2)+1 ∧
      ((sargosQuarticPlateauLower N α γ l η).natAbs : ℝ) ≤ 6*(α*N^2)+1 ∧
      ((sargosQuarticPlateauUpper N α γ b η).natAbs : ℝ) ≤ 6*(α*N^2)+1 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNN : N ≤ N^2 := by nlinarith
  have hαNN := mul_le_mul_of_nonneg_left hNN hα.le
  have hj (u : ℝ) (hu : u ∈ Icc (1:ℝ) 2) :
      |sargosQuarticSlope α γ (N*u)| ≤ 6*(α*N^2) :=
    (sargosQuarticSlope_scaled_abs_le hNp hα hγ hu).trans (by nlinarith)
  exact ⟨(sargos_rounding_natAbs_bound (hj (l+η) (by constructor <;> linarith))).1,
    (sargos_rounding_natAbs_bound (hj (b-η) (by constructor <;> linarith))).2,
    (sargos_rounding_natAbs_bound (hj (l+2*η) (by constructor <;> linarith))).2,
    (sargos_rounding_natAbs_bound (hj (b-2*η) (by constructor <;> linarith))).1⟩

end TaoTrudgianYang2025

