import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (viii)

The full closed interval agrees with blueprint imp-energy-bound7.
Both printed normalizations are kept explicit.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseEightFirstRate (σ : ℝ) : ℝ := (18-19*σ)/(2*(37*σ-27))
def energyClauseEightSecondRate (σ : ℝ) : ℝ := 5*(18-19*σ)/(2*(13*σ-3))
def energyClauseEightRate (σ : ℝ) : ℝ :=
  max (energyClauseEightFirstRate σ) (energyClauseEightSecondRate σ)

theorem energyClauseEightRate_eq_printed (σ : ℝ) :
    energyClauseEightRate σ =
      max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))) := rfl

theorem energyClauseEightFirstRate_le (σ : ℝ) :
    energyClauseEightFirstRate σ ≤ energyClauseEightRate σ := le_max_left _ _

theorem energyClauseEightSecondRate_le (σ : ℝ) :
    energyClauseEightSecondRate σ ≤ energyClauseEightRate σ := le_max_right _ _

theorem energyClauseEight_printed_denominators_pos {σ : ℝ} (hlo : 79/103 ≤ σ) :
    0 < 2*(37*σ-27) ∧ 0 < 2*(13*σ-3) := by
  constructor <;> linarith

theorem energyClauseEightRate_pos {σ : ℝ}
    (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    0 < energyClauseEightRate σ := by
  apply lt_of_lt_of_le _ (energyClauseEightSecondRate_le σ)
  exact div_pos (by linarith : 0 < 5*(18-19*σ)) (by linarith)

theorem energyClauseEightRate_div_eq_blueprint {σ : ℝ} (hhi : σ ≤ 84/109) :
    energyClauseEightRate σ/(1-σ) =
      max ((18-19*σ)/(2*(37*σ-27)*(1-σ)))
        (5*(18-19*σ)/(2*(13*σ-3)*(1-σ))) := by
  unfold energyClauseEightRate energyClauseEightFirstRate energyClauseEightSecondRate
  rw [← max_div_div_right (by linarith : 0 ≤ 1-σ)]
  simp only [div_div]

end TaoTrudgianYang2025
