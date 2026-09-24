import TaoTrudgianYang2025.BourgainRegionDichotomy
import TaoTrudgianYang2025.EnergyCardinalityBounds

/-!
# Bourgain's logarithmic dichotomy on the complete source range

Mean square covers short local heights. On the lower sigma strip it
either gives the small branch or permits an explicit auxiliary witness.
The previously proved physical dichotomy handles every remaining case.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem bourgain_auxiliary_witness_of_large_alpha
    {σ τ ρ α χ : ℝ} (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (hα : 0 ≤ α) (hχ : 0 ≤ χ) (hlarge : 2*σ-1 ≤ 2*α) :
    ∃ x : ℝ, 0 ≤ x ∧
      max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
        heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  refine ⟨4*σ+ρ,by linarith,?_⟩
  have hr : 2*ρ+1 ≤ heathBrownDoubleZetaExponent τ ρ :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hx : 2*(4*σ+ρ)+1 ≤ heathBrownDoubleZetaExponent τ (4*σ+ρ) :=
    (le_max_left _ _).trans (le_max_left _ _)
  apply max_le <;> linarith

theorem InCardinalityEnergyRegion.bourgain_log_dichotomy_full
    {σ τ ρ energy χ α : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hα : 0 ≤ α) (hχ : 0 ≤ χ) :
    ρ ≤ bourgainSmallExponent σ τ α χ ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
          heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  have hmean := hregion.mean_square_cardinality
  have hfirst : χ+2-2*σ ≤ bourgainSmallExponent σ τ α χ :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hthird : -2*α+τ+12-16*σ ≤ bourgainSmallExponent σ τ α χ :=
    le_max_right _ _
  by_cases hmargin : 1 < τ-χ
  · by_cases hσ : 3/4 < σ
    · exact hregion.bourgain_log_dichotomy hσ hχ hmargin
    · by_cases hlarge : 2*σ-1 ≤ 2*α
      · obtain ⟨s,hs⟩ := hregion
        exact Or.inr (bourgain_auxiliary_witness_of_large_alpha
          (by linarith [hs.1]) hs.2.2.2.1 hα hχ hlarge)
      · left
        apply hmean.trans
        apply max_le <;> linarith
  · left
    apply hmean.trans
    apply max_le <;> linarith

end TaoTrudgianYang2025
