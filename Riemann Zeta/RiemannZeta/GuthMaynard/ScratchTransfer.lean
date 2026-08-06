import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RiemannZeta.GuthMaynard

def EpsilonPowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ T ≥ 2, f T ≤ C * T ^ ε * g T

def InghamZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (2 - σ)))

def HuxleyZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 3/4 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (3 * σ - 1)))

def GuthMaynardZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (15 * (1 - σ) / (3 + 5 * σ)))

def CombinedZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (30 * (1 - σ) / 13))

def CombinedZeroDensityTransfer : Prop :=
  ∀ (zeroCount : ℝ → ℝ → ℕ),
    InghamZeroDensity zeroCount →
    HuxleyZeroDensity zeroCount →
    GuthMaynardZeroDensity zeroCount →
    CombinedZeroDensity zeroCount

lemma EpsilonPowerBound_mono (f g1 g2 : ℝ → ℝ) 
  (h : EpsilonPowerBound f g1)
  (h_bound : ∀ T ≥ 2, g1 T ≤ g2 T) : 
  EpsilonPowerBound f g2 := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hT⟩
  use C, hC
  intro T hT2
  have h1 := hT T hT2
  have h2 := h_bound T hT2
  have h3 : 0 ≤ C * T ^ ε := mul_nonneg (le_of_lt hC) (Real.rpow_nonneg_of_nonneg (by linarith) _)
  calc f T ≤ C * T ^ ε * g1 T := h1
       _ ≤ C * T ^ ε * g2 T := mul_le_mul_of_nonneg_left h2 h3

theorem combined_zero_density_transfer : CombinedZeroDensityTransfer := by
  intro zeroCount hIngham hHuxley hGuthMaynard
  intro σ h_half h_one
  by_cases h_710 : σ ≤ 7/10
  · have hIng := hIngham σ h_half h_one
    apply EpsilonPowerBound_mono _ _ _ hIng
    intro T hT
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hd1 : 0 < 2 - σ := by linarith
    have h1 : 3 * (1 - σ) / (2 - σ) ≤ 30 * (1 - σ) / 13 := by
      rw [div_le_div_iff₀ hd1 (by norm_num)]
      linarith
    exact h1
  · push_neg at h_710
    have hGM := hGuthMaynard σ (by linarith) h_one
    apply EpsilonPowerBound_mono _ _ _ hGM
    intro T hT
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hd2 : 0 < 3 + 5 * σ := by linarith
    have h2 : 15 * (1 - σ) / (3 + 5 * σ) ≤ 30 * (1 - σ) / 13 := by
      rw [div_le_div_iff₀ hd2 (by norm_num)]
      linarith
    exact h2

end RiemannZeta.GuthMaynard
