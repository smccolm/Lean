import TaoTrudgianYang2025.AtkinsonCorrectionBounds

/-!
# Complete arithmetic removal of the Neumann correction

The actual correction is absolutely summable at divisor exponent 5/4.
Subtracting it from the genuinely convergent two-term source leaves
the complete leading signed-carrier series, with a uniform O(G) error.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def atkinsonLeadingIntegral (T G L : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt Real.pi / Real.pi : ℂ) * (atkinsonBesselScale (1 / 4) n : ℂ) *
    (neumannLeadingPlus * atkinsonPowerIntegral T G L (1 / 4) (Real.sqrt n) +
     neumannLeadingMinus * atkinsonPowerIntegral T G L (1 / 4) (-Real.sqrt n))

def atkinsonLeadingTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * atkinsonLeadingIntegral T G L n

def atkinsonLeadingSum (T G L : ℝ) : ℂ := ∑' n : ℕ, atkinsonLeadingTerm T G L n

def atkinsonCorrectionSum (T G L : ℝ) : ℂ := ∑' n : ℕ, atkinsonCorrectionTerm T G L n

theorem atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction (T G L : ℝ) (n : ℕ) :
    atkinsonTwoTermCarrierIntegral T G L n =
      atkinsonLeadingIntegral T G L n - atkinsonCorrectionIntegral T G L n := by
  unfold atkinsonTwoTermCarrierIntegral atkinsonLeadingIntegral atkinsonCorrectionIntegral
  ring

theorem zetaAtkinsonTwoTerm_eq_leading_sub_correction {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n = atkinsonLeadingTerm T G L n - atkinsonCorrectionTerm T G L n := by
  rw [zetaAtkinsonTwoTerm_eq_carrierIntegral hT hG hL hwidth,
    atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction]
  unfold atkinsonLeadingTerm atkinsonCorrectionTerm
  ring

theorem summable_atkinsonCorrectionTerm {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonCorrectionTerm T G L) := by
  obtain ⟨C, _, hbound⟩ := exists_norm_atkinsonCorrectionTerm_le
  exact Summable.of_norm_bounded
    ((summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm.mul_left (C * G))
    (hbound T G L hT hG hGT hL hwidth)

theorem exists_norm_atkinsonCorrectionSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ‖atkinsonCorrectionSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonCorrectionTerm_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (5 / 4) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hs := summable_atkinsonCorrectionTerm hT hG hGT hL hwidth
  have hd := (summable_divisorDirichletTerm (s := (5 / 4 : ℂ)) (by norm_num)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖atkinsonCorrectionTerm T G L n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (C * G) * ‖divisorDirichletTerm (5 / 4) n‖ :=
      hs.norm.tsum_le_tsum (hbound T G L hT hG hGT hL hwidth) (hd.mul_left _)
    _ = C * G * S := tsum_mul_left
    _ ≤ _ := by nlinarith

theorem summable_atkinsonLeadingTerm {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonLeadingTerm T G L) := by
  have h := (summable_zetaAtkinsonTwoTerm hT hG hGT hL hwidth).add
    (summable_atkinsonCorrectionTerm (by linarith : 1 ≤ T) hG hGT hL hwidth)
  apply h.congr
  intro n
  rw [zetaAtkinsonTwoTerm_eq_leading_sub_correction (by linarith) hG hL hwidth n]
  ring

theorem zetaAtkinsonTwoTermSum_eq_leading_sub_correction {T G L : ℝ}
    (hT : 16 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    zetaAtkinsonTwoTermSum T G L = atkinsonLeadingSum T G L - atkinsonCorrectionSum T G L := by
  unfold zetaAtkinsonTwoTermSum atkinsonLeadingSum atkinsonCorrectionSum
  simp_rw [zetaAtkinsonTwoTerm_eq_leading_sub_correction (by linarith : 0 < T) hG hL hwidth]
  exact (summable_atkinsonLeadingTerm hT hG hGT hL hwidth).tsum_sub
    (summable_atkinsonCorrectionTerm (by linarith : 1 ≤ T) hG hGT hL hwidth)

theorem exists_norm_zetaAtkinsonTwoTermSum_sub_leading_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
        ‖zetaAtkinsonTwoTermSum T G L - atkinsonLeadingSum T G L‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonCorrectionSum_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth
  rw [zetaAtkinsonTwoTermSum_eq_leading_sub_correction hT hG hGT hL hwidth,
    sub_sub_cancel_left, norm_neg]
  exact hbound T G L (by linarith) hG hGT hL hwidth

end TaoTrudgianYang2025
