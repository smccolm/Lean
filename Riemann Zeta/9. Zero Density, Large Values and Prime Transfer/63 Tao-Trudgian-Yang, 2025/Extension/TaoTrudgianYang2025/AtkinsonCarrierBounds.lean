import TaoTrudgianYang2025.AtkinsonCarrierIntegrals

/-!
# Uniform bounds for the actual two-term arithmetic summand

Both signed carriers use the proved square-root-coordinate cancellation.
The leading and correction powers are kept separate; these bounds do
not assert that their unsmoothed majorants are summable in n.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_norm_atkinsonPowerPair_le (α : ℝ) (c d : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
      ‖c * atkinsonPowerIntegral T G L α b + d * atkinsonPowerIntegral T G L α (-b)‖ ≤
        C * G * T ^ (-α) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonPowerIntegral_le α
  refine ⟨(1 + ‖c‖ + ‖d‖) * C, by positivity, ?_⟩
  intro T G L b hT hG hGT hL hwidth
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (C * G * T ^ (-α)) + ‖d‖ * (C * G * T ^ (-α)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hbound T G L b hT hG hGT hL hwidth) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hbound T G L (-b) hT hG hGT hL hwidth) (norm_nonneg _))
    _ ≤ _ := by
      have hb : 0 ≤ C * G * T ^ (-α) := by positivity
      nlinarith

theorem atkinsonBesselScale_nonneg (α : ℝ) (n : ℕ) : 0 ≤ atkinsonBesselScale α n := by
  unfold atkinsonBesselScale
  positivity

theorem exists_norm_atkinsonTwoTermCarrierIntegral_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
      ‖atkinsonTwoTermCarrierIntegral T G L n‖ ≤
        C * G * T ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
        D * G * T ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨C, hC, hlead⟩ :=
    exists_norm_atkinsonPowerPair_le (1 / 4) neumannLeadingPlus neumannLeadingMinus
  obtain ⟨D, hD, hcorrection⟩ :=
    exists_norm_atkinsonPowerPair_le (3 / 4) neumannCorrectionPlus neumannCorrectionMinus
  let q : ℝ := Real.sqrt Real.pi / Real.pi
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q * (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * C,
    q * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) / 8 * D, by positivity, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  have hqn : ‖(Real.sqrt Real.pi / Real.pi : ℂ)‖ = q := by
    simp [q, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hs (α : ℝ) : ‖(atkinsonBesselScale α n : ℂ)‖ = atkinsonBesselScale α n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atkinsonBesselScale_nonneg α n)]
  rw [atkinsonTwoTermCarrierIntegral, norm_mul, hqn]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq.le).trans
  rw [norm_mul, norm_mul, norm_div, norm_ofNat, hs, hs]
  calc
    _ ≤ q * (atkinsonBesselScale (1 / 4) n * (C * G * T ^ (-(1 / 4 : ℝ))) +
        atkinsonBesselScale (3 / 4) n / 8 * (D * G * T ^ (-(3 / 4 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hq.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hlead T G L (Real.sqrt n) hT hG hGT hL hwidth)
          (atkinsonBesselScale_nonneg _ _))
        (mul_le_mul_of_nonneg_left (hcorrection T G L (Real.sqrt n) hT hG hGT hL hwidth)
          (div_nonneg (atkinsonBesselScale_nonneg _ _) (by norm_num)))
    _ = _ := by
      unfold atkinsonBesselScale
      norm_num only [show (-2 : ℝ) * (1 / 4) = -(1 / 2) by norm_num,
        show (-2 : ℝ) * (3 / 4) = -(3 / 2) by norm_num]
      ring

theorem exists_norm_zetaAtkinsonTwoTerm_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
      ‖zetaAtkinsonTwoTerm T G L n‖ ≤ ‖divisorWeight n‖ *
        (C * G * T ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
         D * G * T ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ))) := by
  obtain ⟨C, D, hC, hD, hbound⟩ := exists_norm_atkinsonTwoTermCarrierIntegral_le
  refine ⟨2 * Real.pi * C, 2 * Real.pi * D, by positivity, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth n
  rw [zetaAtkinsonTwoTerm_eq_carrierIntegral hT hG hL hwidth n, norm_mul, norm_mul]
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hpi]
  have h := mul_le_mul_of_nonneg_left (hbound T G L hT hG hGT hL hwidth n)
    (show 0 ≤ ‖divisorWeight n‖ * (2 * Real.pi) by positivity)
  convert h using 1
  ring

end TaoTrudgianYang2025
