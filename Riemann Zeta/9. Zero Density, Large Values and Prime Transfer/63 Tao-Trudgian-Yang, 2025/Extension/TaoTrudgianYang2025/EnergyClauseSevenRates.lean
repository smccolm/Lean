import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (vii)

The full closed interval agrees with blueprint imp-energy-bound6.
Both printed normalizations are kept explicit.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseSevenFirstRate (σ : ℝ) : ℝ := (18-19*σ)/(6*(15*σ-11))
def energyClauseSevenSecondRate (σ : ℝ) : ℝ := 3*(18-19*σ)/(4*(4*σ-1))
def energyClauseSevenRate (σ : ℝ) : ℝ :=
  max (energyClauseSevenFirstRate σ) (energyClauseSevenSecondRate σ)

theorem energyClauseSevenRate_eq_printed (σ : ℝ) :
    energyClauseSevenRate σ =
      max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))) := rfl

theorem energyClauseSevenFirstRate_le (σ : ℝ) :
    energyClauseSevenFirstRate σ ≤ energyClauseSevenRate σ := le_max_left _ _

theorem energyClauseSevenSecondRate_le (σ : ℝ) :
    energyClauseSevenSecondRate σ ≤ energyClauseSevenRate σ := le_max_right _ _

theorem energyClauseSeven_printed_denominators_pos {σ : ℝ} (hlo : 42/55 ≤ σ) :
    0 < 6*(15*σ-11) ∧ 0 < 4*(4*σ-1) := by
  constructor <;> linarith

theorem energyClauseSevenRate_pos {σ : ℝ}
    (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    0 < energyClauseSevenRate σ := by
  apply lt_of_lt_of_le _ (energyClauseSevenSecondRate_le σ)
  exact div_pos (by linarith : 0 < 3*(18-19*σ)) (by linarith)

theorem energyClauseSevenRate_div_eq_blueprint {σ : ℝ} (hhi : σ ≤ 79/103) :
    energyClauseSevenRate σ/(1-σ) =
      max ((18-19*σ)/(6*(15*σ-11)*(1-σ)))
        (3*(18-19*σ)/(4*(4*σ-1)*(1-σ))) := by
  unfold energyClauseSevenRate energyClauseSevenFirstRate energyClauseSevenSecondRate
  rw [← max_div_div_right (by linarith : 0 ≤ 1-σ)]
  simp only [div_div]

end TaoTrudgianYang2025
