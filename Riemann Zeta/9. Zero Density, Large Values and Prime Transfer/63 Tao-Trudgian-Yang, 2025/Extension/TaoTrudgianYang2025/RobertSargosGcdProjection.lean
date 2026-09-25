import TaoTrudgianYang2025.RobertSargosNormalizationCoordinates

/-! The actual common-gcd key lies in the full finite summation rectangle. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosGcdKey (p : RobertSargosPoint) : ℕ × ℕ :=
  (robertSargosCoefficientGcd p,robertSargosFrequencyGcd p)

theorem RobertSargosReducedSystem.gcd_key_mem {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) (hQ : 0 < Q) :
    robertSargosGcdKey p ∈ (Finset.Icc 1 ⌊R⌋₊) ×ˢ (Finset.Icc 1 ⌊2*Q⌋₊) := by
  have hR : 0 ≤ R := (abs_nonneg (p.r:ℝ)).trans h.r_bound
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨h.coefficient_gcd_pos,
      (Nat.le_floor_iff hR).mpr h.coefficient_gcd_le⟩
  · exact Finset.mem_Icc.mpr ⟨h.frequency_gcd_pos,
      (Nat.le_floor_iff (by positivity : 0 ≤ 2*Q)).mpr (h.frequency_gcd_le hQ)⟩

end TaoTrudgianYang2025

