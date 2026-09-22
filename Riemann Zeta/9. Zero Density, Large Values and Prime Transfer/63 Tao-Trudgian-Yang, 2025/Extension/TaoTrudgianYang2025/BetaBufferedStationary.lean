import TaoTrudgianYang2025.BetaBufferedMorseBounds
import TaoTrudgianYang2025.BetaMorseStationaryEstimate

/-!
# Quantitative stationary errors for the varying cutoff family

All constants precede both endpoints and the width. This removes the
uncontrolled lattice-gap dependence of the earlier fixed-cutoff theorem.
The explicitly recorded width power is not yet a summed B-process error.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem quadraticRemainderConstant_scale (H M₀ M₂ M₃ A : ℝ) :
    quadraticRemainderConstant H (M₀*A) (M₂*A) (M₃*A) =
      quadraticRemainderConstant H M₀ M₂ M₃*A := by
  unfold quadraticRemainderConstant
  ring

def bufferedStationaryPhaseOrder : ℕ :=
  morseWeightDerivativeOrder 0+morseWeightDerivativeOrder 2+morseWeightDerivativeOrder 3

def bufferedStationaryWidthDegree : ℕ := 3

theorem bufferedStationaryPhaseOrder_pos : 1 ≤ bufferedStationaryPhaseOrder := by
  unfold bufferedStationaryPhaseOrder
  have h := morseWeightDerivativeOrder_pos 0
  omega

theorem modelPhaseBufferedMorseRemainder_uniform
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        ‖modelPhaseMorseRemainder (modelPhaseBufferedCutoff l r η) F T v‖ ≤
          C*(η⁻¹)^bufferedStationaryWidthDegree/T := by
  obtain ⟨C₀,hC₀,h₀⟩ := modelPhaseBufferedMorseWeight_uniform_derivative hσ 0
  obtain ⟨C₂,hC₂,h₂⟩ := modelPhaseBufferedMorseWeight_uniform_derivative hσ 2
  obtain ⟨C₃,hC₃,h₃⟩ := modelPhaseBufferedMorseWeight_uniform_derivative hσ 3
  let H := Real.sqrt (σ+1)+1
  refine ⟨max (quadraticRemainderConstant H C₀ C₂ C₃) 1,le_max_right _ _,?_⟩
  intro l r η hl hr hη hη₁ F δ v T hδ hF hv hT
  let χ := modelPhaseBufferedCutoff l r η
  let A := (η⁻¹)^bufferedStationaryWidthDegree
  have hA₀ : 0 ≤ A := pow_nonneg (inv_nonneg.mpr hη.le) _
  have hηinv : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη₁
  have hF₁ := approximateModelPhase_mono hF bufferedStationaryPhaseOrder_pos le_rfl
  have hs := modelPhaseBufferedCutoff_tsupport_model hη hl hr
  have hb₀ : ∀ z : ℝ, |iteratedDeriv 0 (modelPhaseMorseWeight χ F v) z| ≤ C₀*A := by
    intro z
    exact (h₀ l r η hl hr hη hη₁ F δ v hδ
      (approximateModelPhase_mono hF (by unfold bufferedStationaryPhaseOrder; omega) le_rfl) hv z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hηinv
        (by unfold bufferedStationaryWidthDegree bufferedMorseDerivativeDegree; omega)) (zero_le_one.trans hC₀))
  have hb₂ : ∀ z : ℝ, |iteratedDeriv 2 (modelPhaseMorseWeight χ F v) z| ≤ C₂*A := by
    intro z
    exact (h₂ l r η hl hr hη hη₁ F δ v hδ
      (approximateModelPhase_mono hF (by unfold bufferedStationaryPhaseOrder; omega) le_rfl) hv z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hηinv
        (by unfold bufferedStationaryWidthDegree bufferedMorseDerivativeDegree; omega)) (zero_le_one.trans hC₂))
  have hb₃ : ∀ z : ℝ, |iteratedDeriv 3 (modelPhaseMorseWeight χ F v) z| ≤ C₃*A := by
    intro z
    exact (h₃ l r η hl hr hη hη₁ F δ v hδ
      (approximateModelPhase_mono hF (by unfold bufferedStationaryPhaseOrder; omega) le_rfl) hv z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hηinv
        (by unfold bufferedStationaryWidthDegree bufferedMorseDerivativeDegree; omega)) (zero_le_one.trans hC₃))
  have hsupport : Function.support (modelPhaseMorseWeight χ F v) ⊆ Ioc (-H) H := by
    intro z hz
    have h := modelPhaseMorseWeight_tsupport_uniform hs hσ hδ hF₁ hv (subset_tsupport _ hz)
    dsimp [H]
    constructor <;> linarith [h.1,h.2]
  rw [modelPhaseMorseRemainder_eq_global hσ hδ hF₁ hv]
  have h := norm_quadratic_global_remainder_le
    (modelPhaseMorseWeight_contDiff (modelPhaseBufferedCutoff_contDiff l r η) hs hσ hδ hF₁ hv)
    hT (by dsimp [H]; positivity : 0 < H) hsupport
    (by simpa only [iteratedDeriv_zero] using hb₀ 0) hb₂ hb₃
  rw [quadraticRemainderConstant_scale] at h
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hA₀) hT.le)

theorem modelPhaseBufferedFourierMode_stationary_uniform
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N q : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedStationaryPhaseOrder δ →
        0 < T → 0 < N → q*N/T ∈ modelPhaseSlopeRange F →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          (modelPhaseBufferedCutoff l r η
            (modelPhaseInverseSlope F (q*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N q‖ ≤
          C*(η⁻¹)^bufferedStationaryWidthDegree*N/T := by
  obtain ⟨C,hC,hR⟩ := modelPhaseBufferedMorseRemainder_uniform hσ
  refine ⟨C,hC,?_⟩
  intro l r η hl hr hη hη₁ F δ T N q hδ hF hT hN hv
  rw [norm_modelPhaseFourierMode_sub_main
    (modelPhaseBufferedCutoff_tsupport_model hη hl hr) hσ hδ
    (approximateModelPhase_mono hF bufferedStationaryPhaseOrder_pos le_rfl) hT hN hv]
  exact (mul_le_mul_of_nonneg_left
    (hR l r η hl hr hη hη₁ F δ (q*N/T) T hδ hF hv hT) hN.le).trans_eq (by ring)

end TaoTrudgianYang2025
