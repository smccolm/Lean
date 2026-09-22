import TaoTrudgianYang2025.EnergyClauseTwoCertificates
import TaoTrudgianYang2025.EnergyClauseOneZeta

/-!
# Exact rates for Add-est (ix)

The printed maximum is retained on the full closed interval [84/109,5/6].
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseNineFirstRate (σ : ℝ) : ℝ := (18-19*σ)/(9*(3*σ-2))
def energyClauseNineSecondRate (σ : ℝ) : ℝ := 4*(10-9*σ)/(5*(4*σ-1))
def energyClauseNineRate (σ : ℝ) : ℝ :=
  max (energyClauseNineFirstRate σ) (energyClauseNineSecondRate σ)

theorem energyClauseNineRate_eq_printed (σ : ℝ) :
    energyClauseNineRate σ =
      max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))) := rfl

theorem energyClauseNineFirstRate_le (σ : ℝ) :
    energyClauseNineFirstRate σ ≤ energyClauseNineRate σ := le_max_left _ _

theorem energyClauseNineSecondRate_le (σ : ℝ) :
    energyClauseNineSecondRate σ ≤ energyClauseNineRate σ := le_max_right _ _

theorem energyClauseNine_printed_denominators_pos {σ : ℝ} (hlo : 84/109 ≤ σ) :
    0 < 9*(3*σ-2) ∧ 0 < 5*(4*σ-1) := by
  constructor <;> linarith

theorem energyClauseNineRate_pos {σ : ℝ}
    (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    0 < energyClauseNineRate σ := by
  apply lt_of_lt_of_le _ (energyClauseNineSecondRate_le σ)
  exact div_pos (by linarith : 0 < 4*(10-9*σ)) (by linarith)

theorem energyClauseNineRate_div_eq_blueprint {σ : ℝ} (hhi : σ ≤ 5/6) :
    energyClauseNineRate σ/(1-σ) =
      max ((18-19*σ)/(9*(3*σ-2)*(1-σ)))
        (4*(10-9*σ)/(5*(4*σ-1)*(1-σ))) := by
  unfold energyClauseNineRate energyClauseNineFirstRate energyClauseNineSecondRate
  rw [← max_div_div_right (by linarith : 0 ≤ 1-σ)]
  simp only [div_div]

theorem energyClauseNineRate_ge_short_linear {σ : ℝ} (hlo : 84/109 ≤ σ) :
    15-18*σ ≤ energyClauseNineRate σ := by
  apply le_trans _ (energyClauseNineSecondRate_le σ)
  apply (le_div_iff₀ (by linarith : 0 < 5*(4*σ-1))).2
  nlinarith [mul_nonneg (by linarith : 0 ≤ σ-84/109)
    (by linarith : 0 ≤ 360*σ-426+360*(84/109))]

theorem energyClauseOneZetaRate_le_nine {σ : ℝ} (hlo : 84/109 ≤ σ) :
    energyClauseOneZetaRate σ ≤ energyClauseNineRate σ := by
  rw [energyClauseOneZetaRate_upper_piece (by linarith : 65/86 ≤ σ)]
  exact energyClauseNineSecondRate_le σ

theorem energyClauseOneGeneralRate_le_nine {σ : ℝ}
    (hlo : 4/5 ≤ σ) :
    energyClauseOneGeneralRate σ ≤ energyClauseNineRate σ := by
  rw [energyClauseOneGeneralRate_upper_piece hlo]
  apply le_trans _ (energyClauseNineSecondRate_le σ)
  apply (div_le_div_iff₀ (by linarith : 0 < 3*σ-1)
    (by linarith : 0 < 5*(4*σ-1))).2
  nlinarith [mul_nonneg (by linarith : 0 ≤ σ-4/5)
    (by linarith : 0 ≤ 32*σ-32*(4/5))]

end TaoTrudgianYang2025
