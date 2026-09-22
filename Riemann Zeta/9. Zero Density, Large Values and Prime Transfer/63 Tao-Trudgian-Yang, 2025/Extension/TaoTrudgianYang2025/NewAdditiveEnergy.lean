import TaoTrudgianYang2025.ZetaTwelfthMoment
import TaoTrudgianYang2025.EnergyClauseTwo
import TaoTrudgianYang2025.EnergyClauseThree
import TaoTrudgianYang2025.EnergyClauseFour
import TaoTrudgianYang2025.EnergyClauseFive
import TaoTrudgianYang2025.EnergyClauseSix
import TaoTrudgianYang2025.EnergyClauseSeven
import TaoTrudgianYang2025.EnergyClauseEight
import TaoTrudgianYang2025.EnergyClauseNine
import Mathlib.Data.EReal.Operations

/-!
# New additive-energy estimates

All nine clauses are proved on their full printed closed intervals.
The proof uses the corrected independent cardinality and energy witnesses.
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

theorem add_est_iii_bound {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    IsZeroDensityEnergyBound σ
      ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))))/(1-σ)) := by
  simpa only [energyClauseThreeRate_eq_printed] using energyClauseThree hlo hhi

theorem add_est_iii {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_iii_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_iii_zero_energy {σ : ℝ} (hlo : 173/229 ≤ σ) (hhi : σ ≤ 443/586) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((173-270*σ)/(16*(93-125*σ)))
        (max ((653-890*σ)/(10*(93-125*σ))) ((1151-1190*σ)/(20*(15*σ-2)))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_iii_bound hlo hhi

theorem add_est_iv_bound {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    IsZeroDensityEnergyBound σ
      ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))))/(1-σ)) := by
  simpa only [energyClauseFourRate_eq_printed] using energyClauseFour hlo hhi

theorem add_est_iv {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_iv_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_iv_zero_energy {σ : ℝ} (hlo : 443/586 ≤ σ) (hhi : σ ≤ 373/493) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((593-810*σ)/(5*(171-230*σ))) (4*(266-275*σ)/(5*(55*σ-7))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_iv_bound hlo hhi

theorem add_est_v_bound {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    IsZeroDensityEnergyBound σ
      ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))))/(1-σ)) := by
  simpa only [energyClauseFiveRate_eq_printed] using energyClauseFive hlo hhi

theorem add_est_v {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_v_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_v_zero_energy {σ : ℝ} (hlo : 373/493 ≤ σ) (hhi : σ ≤ 103/136) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((533-730*σ)/(30*(26-35*σ)))
        (max (3*(26-33*σ)/(85*σ-62)) ((174-185*σ)/(31*σ+2))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_v_bound hlo hhi

theorem add_est_vi_bound {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    IsZeroDensityEnergyBound σ
      ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))))/(1-σ)) := by
  simpa only [energyClauseSixRate_eq_printed] using
    energyClauseSix (σ := σ) (by linarith) (by linarith)

theorem add_est_vi {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_vi_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_vi_zero_energy {σ : ℝ} (hlo : 103/136 ≤ σ) (hhi : σ ≤ 42/55) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((72-91*σ)/(7*(11*σ-8))) (5*(18-19*σ)/(2*(5*σ+3))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_vi_bound hlo hhi

theorem add_est_vii_bound {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))))/(1-σ)) := by
  simpa only [energyClauseSevenRate_eq_printed] using
    energyClauseSeven hlo hhi

theorem add_est_vii {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_vii_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_vii_zero_energy {σ : ℝ} (hlo : 42/55 ≤ σ) (hhi : σ ≤ 79/103) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(6*(15*σ-11))) (3*(18-19*σ)/(4*(4*σ-1))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_vii_bound hlo hhi

theorem add_est_viii_bound {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))))/(1-σ)) := by
  simpa only [energyClauseEightRate_eq_printed] using
    energyClauseEight hlo hhi

theorem add_est_viii {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_viii_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_viii_zero_energy {σ : ℝ} (hlo : 79/103 ≤ σ) (hhi : σ ≤ 84/109) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(2*(37*σ-27))) (5*(18-19*σ)/(2*(13*σ-3))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_viii_bound hlo hhi

theorem add_est_ix_bound {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ
      ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))))/(1-σ)) := by
  simpa only [energyClauseNineRate_eq_printed] using
    energyClauseNine hlo hhi

theorem add_est_ix {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))) : ℝ) : EReal) := by
  have hpos : 0 < 1-σ := by linarith
  have h := mul_le_mul_of_nonneg_right
    (zeroDensityEnergyExponent_le_of_bound (add_est_ix_bound hlo hhi))
    (show (0 : EReal) ≤ ((1-σ : ℝ) : EReal) by exact_mod_cast hpos.le)
  simpa only [← EReal.coe_mul,div_mul_cancel₀ _ hpos.ne'] using h

theorem add_est_ix_zero_energy {σ : ℝ} (hlo : 84/109 ≤ σ) (hhi : σ ≤ 5/6) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, C ≤ T →
        (zeroAdditiveEnergy (σ-δ) T : ℝ) ≤ C*T^
          ((max ((18-19*σ)/(9*(3*σ-2))) (4*(10-9*σ)/(5*(4*σ-1))))+ε) := by
  have hpos : 0 < 1-σ := by linarith
  simpa only [IsZeroDensityEnergyBound,div_mul_cancel₀ _ hpos.ne'] using
    add_est_ix_bound hlo hhi

end TaoTrudgianYang2025
