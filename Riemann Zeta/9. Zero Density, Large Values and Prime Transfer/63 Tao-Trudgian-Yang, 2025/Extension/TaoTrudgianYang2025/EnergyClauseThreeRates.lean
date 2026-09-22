import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (iii)

The first two printed fractions have negative denominators on this
interval. Both signs are reversed explicitly before comparisons.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseThreeFirstRate (σ : ℝ) : ℝ := (270*σ-173)/(16*(125*σ-93))
def energyClauseThreeSecondRate (σ : ℝ) : ℝ := (890*σ-653)/(10*(125*σ-93))
def energyClauseThreeThirdRate (σ : ℝ) : ℝ := (1151-1190*σ)/(20*(15*σ-2))
def energyClauseThreeRate (σ : ℝ) : ℝ :=
  max (energyClauseThreeFirstRate σ)
    (max (energyClauseThreeSecondRate σ) (energyClauseThreeThirdRate σ))

theorem energyClauseThreeRate_eq_printed (σ : ℝ) :
    energyClauseThreeRate σ =
      max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))) := by
  have h₁ : (173-270*σ)/(16*(93-125*σ)) = (270*σ-173)/(16*(125*σ-93)) := by
    rw [show 173-270*σ = -(270*σ-173) by ring,
      show 16*(93-125*σ) = -(16*(125*σ-93)) by ring, neg_div_neg_eq]
  have h₂ : (653-890*σ)/(10*(93-125*σ)) = (890*σ-653)/(10*(125*σ-93)) := by
    rw [show 653-890*σ = -(890*σ-653) by ring,
      show 10*(93-125*σ) = -(10*(125*σ-93)) by ring, neg_div_neg_eq]
  rw [h₁,h₂]
  rfl

theorem energyClauseThreeFirstRate_le (σ : ℝ) :
    energyClauseThreeFirstRate σ ≤ energyClauseThreeRate σ := le_max_left _ _

theorem energyClauseThreeSecondRate_le (σ : ℝ) :
    energyClauseThreeSecondRate σ ≤ energyClauseThreeRate σ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem energyClauseThreeThirdRate_le (σ : ℝ) :
    energyClauseThreeThirdRate σ ≤ energyClauseThreeRate σ :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem energyClauseThreeRate_pos {σ : ℝ}
    (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    0 < energyClauseThreeRate σ := by
  apply lt_of_lt_of_le _ (energyClauseThreeThirdRate_le σ)
  exact div_pos (by linarith : 0 < 1151-1190*σ) (by linarith)

end TaoTrudgianYang2025
