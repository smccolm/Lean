import TaoTrudgianYang2025.ZetaTwelfthMoment
import TaoTrudgianYang2025.EnergyClauseTwo
import Mathlib.Data.EReal.Operations

/-!
# New additive-energy estimates

Clauses (i) and (ii) are proved on their full printed intervals. The other seven
clauses remain open; no theorem asserting their conjunction is declared.
The exponent and epsilon--delta conclusions use the actual shifted
zero multiset and its analytic multiplicities.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem add_est_i_bound {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ
      (max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1)))/(1-σ)) :=
  energyClauseOne hlo hhi

theorem add_est_i {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ*((1-σ:ℝ):EReal) ≤
      ((max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1))):ℝ):EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_i_bound hlo hhi))
    (show (0:EReal) ≤ ((1-σ:ℝ):EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_i_zero_energy {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T:ℝ) ≤ C*T^
          (max ((18-19*σ)/(2*(3*σ-1))) (4*(10-9*σ)/(5*(4*σ-1)))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_i_bound hlo hhi

theorem add_est_ii_bound {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    IsZeroDensityEnergyBound σ
      (max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15))/(1-σ)) :=
  energyClauseTwo hlo hhi

theorem add_est_ii {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    zeroDensityEnergyExponent σ*((1-σ:ℝ):EReal) ≤
      ((max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15)):ℝ):EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_ii_bound hlo hhi))
    (show (0:EReal) ≤ ((1-σ:ℝ):EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_ii_zero_energy {σ : ℝ} (hlo : 7/10 ≤ σ) (hhi : σ ≤ 3/4) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T:ℝ) ≤ C*T^
          (max (5*(18-19*σ)/(2*(5*σ+3))) (2*(45-44*σ)/(2*σ+15))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_ii_bound hlo hhi

end TaoTrudgianYang2025
