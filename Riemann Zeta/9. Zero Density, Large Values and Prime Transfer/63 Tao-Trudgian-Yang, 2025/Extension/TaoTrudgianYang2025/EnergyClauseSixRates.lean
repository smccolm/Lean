import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (vi)

The analytic theorem is proved on the full blueprint interval
[664/877,31/40], then restricted to the printed [103/136,42/55].
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseSixFirstRate (σ : ℝ) : ℝ := (72-91*σ)/(7*(11*σ-8))
def energyClauseSixSecondRate (σ : ℝ) : ℝ := 5*(18-19*σ)/(2*(5*σ+3))
def energyClauseSixRate (σ : ℝ) : ℝ :=
  max (energyClauseSixFirstRate σ) (energyClauseSixSecondRate σ)

theorem energyClauseSixRate_eq_printed (σ : ℝ) :
    energyClauseSixRate σ =
      max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))) := rfl

theorem energyClauseSixFirstRate_le (σ : ℝ) :
    energyClauseSixFirstRate σ ≤ energyClauseSixRate σ := le_max_left _ _

theorem energyClauseSixSecondRate_le (σ : ℝ) :
    energyClauseSixSecondRate σ ≤ energyClauseSixRate σ := le_max_right _ _

theorem energyClauseSix_printed_denominators_pos {σ : ℝ} (hlo : 664/877 ≤ σ) :
    0 < 7*(11*σ-8) ∧ 0 < 2*(5*σ+3) := by
  constructor <;> linarith

theorem energyClauseSixRate_pos {σ : ℝ}
    (hlo : 664/877 ≤ σ) (hhi : σ ≤ 31/40) :
    0 < energyClauseSixRate σ := by
  apply lt_of_lt_of_le _ (energyClauseSixSecondRate_le σ)
  exact div_pos (by linarith : 0 < 5*(18-19*σ)) (by linarith)

theorem energyClauseSixRate_div_eq_blueprint {σ : ℝ} (hhi : σ ≤ 31/40) :
    energyClauseSixRate σ/(1-σ) =
      max ((72-91*σ)/(7*(11*σ-8)*(1-σ)))
        (5*(18-19*σ)/(2*(5*σ+3)*(1-σ))) := by
  unfold energyClauseSixRate energyClauseSixFirstRate energyClauseSixSecondRate
  rw [← max_div_div_right (by linarith : 0 ≤ 1-σ)]
  simp only [div_div]

end TaoTrudgianYang2025
