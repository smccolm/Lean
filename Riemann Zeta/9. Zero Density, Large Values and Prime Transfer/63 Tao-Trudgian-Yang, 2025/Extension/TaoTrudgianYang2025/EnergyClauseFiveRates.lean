import TaoTrudgianYang2025.EnergyClauseTwoCertificates

/-!
# Exact rational rates in Add-est (v)

The printed first fraction has a negative denominator. Its normalization
reverses both signs; the source three-term maximum remains unchanged.
-/

noncomputable section

namespace TaoTrudgianYang2025

def energyClauseFiveFirstRate (σ : ℝ) : ℝ := (730*σ-533)/(30*(35*σ-26))
def energyClauseFiveSecondRate (σ : ℝ) : ℝ := 3*(26-33*σ)/(85*σ-62)
def energyClauseFiveThirdRate (σ : ℝ) : ℝ := (174-185*σ)/(31*σ+2)
def energyClauseFiveRate (σ : ℝ) : ℝ :=
  max (energyClauseFiveFirstRate σ)
    (max (energyClauseFiveSecondRate σ) (energyClauseFiveThirdRate σ))

theorem energyClauseFiveRate_eq_printed (σ : ℝ) :
    energyClauseFiveRate σ =
      max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))) := by
  have h : (533-730*σ)/(30*(26-35*σ)) = (730*σ-533)/(30*(35*σ-26)) := by
    rw [show 533-730*σ = -(730*σ-533) by ring,
      show 30*(26-35*σ) = -(30*(35*σ-26)) by ring, neg_div_neg_eq]
  rw [h]
  rfl

theorem energyClauseFiveFirstRate_le (σ : ℝ) :
    energyClauseFiveFirstRate σ ≤ energyClauseFiveRate σ := le_max_left _ _

theorem energyClauseFiveSecondRate_le (σ : ℝ) :
    energyClauseFiveSecondRate σ ≤ energyClauseFiveRate σ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem energyClauseFiveThirdRate_le (σ : ℝ) :
    energyClauseFiveThirdRate σ ≤ energyClauseFiveRate σ :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem energyClauseFive_printed_denominators_pos {σ : ℝ} (hlo : 373/493 ≤ σ) :
    0 < 30*(35*σ-26) ∧ 0 < 85*σ-62 ∧ 0 < 31*σ+2 := by
  constructor
  · linarith
  constructor <;> linarith

theorem energyClauseFiveRate_pos {σ : ℝ}
    (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    0 < energyClauseFiveRate σ := by
  apply lt_of_lt_of_le _ (energyClauseFiveThirdRate_le σ)
  exact div_pos (by linarith : 0 < 174-185*σ) (by linarith)

end TaoTrudgianYang2025
