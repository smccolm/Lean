import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (iv)

The negative denominator in the first printed fraction is handled
by an explicit simultaneous sign reversal, valid even at totalized zero.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseFourFirstRate (σ : ℝ) : ℝ := (810*σ-593)/(5*(230*σ-171))
def energyClauseFourSecondRate (σ : ℝ) : ℝ := 4*(266-275*σ)/(5*(55*σ-7))
def energyClauseFourRate (σ : ℝ) : ℝ :=
  max (energyClauseFourFirstRate σ) (energyClauseFourSecondRate σ)

theorem energyClauseFourRate_eq_printed (σ : ℝ) :
    energyClauseFourRate σ =
      max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))) := by
  have h : (593-810*σ)/(5*(171-230*σ)) = (810*σ-593)/(5*(230*σ-171)) := by
    rw [show 593-810*σ = -(810*σ-593) by ring,
      show 5*(171-230*σ) = -(5*(230*σ-171)) by ring, neg_div_neg_eq]
  rw [h]
  rfl

theorem energyClauseFourFirstRate_le (σ : ℝ) :
    energyClauseFourFirstRate σ ≤ energyClauseFourRate σ := le_max_left _ _

theorem energyClauseFourSecondRate_le (σ : ℝ) :
    energyClauseFourSecondRate σ ≤ energyClauseFourRate σ := le_max_right _ _

theorem energyClauseFourRate_pos {σ : ℝ}
    (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    0 < energyClauseFourRate σ := by
  apply lt_of_lt_of_le _ (energyClauseFourSecondRate_le σ)
  exact div_pos (by linarith : 0 < 4*(266-275*σ)) (by linarith)

end TaoTrudgianYang2025
