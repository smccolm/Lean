import TaoTrudgianYang2025.BetaMorseWeightBounds
import TaoTrudgianYang2025.BetaQuadraticRemainder

/-!
# Uniform stationary remainder for the original cutoff and phase

For a fixed original smooth cutoff, constants and the finite phase order
are chosen before F, the actual slope, T and N. The physical error is
O(N/T), with the original cutoff value retained in the main term.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhaseMorseRemainder_eq_global
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseMorseRemainder χ F T v =
      (∫ z : ℝ, (modelPhaseMorseWeight χ F v z : ℂ)*betaQuadraticKernel T z)-
        (modelPhaseMorseWeight χ F v 0 : ℂ)*
          ((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) := by
  rw [modelPhaseMorseRemainder,modelPhaseMorseWeightedIntegral_eq_global hσ hδ hF hv,
    modelPhaseMorseWeight_eq (zero_mem_modelPhaseMorseRange hv)]
  simp only [betaQuadraticKernel]
  ring

theorem modelPhaseMorseRemainder_uniform
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ v T : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        v ∈ modelPhaseSlopeRange F → 0 < T →
        ‖modelPhaseMorseRemainder χ F T v‖ ≤ C/T := by
  obtain ⟨C₀,hC₀,h₀⟩ := modelPhaseMorseWeight_uniform_derivative hχ hs hσ 0
  obtain ⟨C₂,hC₂,h₂⟩ := modelPhaseMorseWeight_uniform_derivative hχ hs hσ 2
  obtain ⟨C₃,hC₃,h₃⟩ := modelPhaseMorseWeight_uniform_derivative hχ hs hσ 3
  let P := morseWeightDerivativeOrder 0+morseWeightDerivativeOrder 2+morseWeightDerivativeOrder 3
  let H := Real.sqrt (σ+1)+1
  have hP : 1 ≤ P := by
    dsimp [P]
    have h := morseWeightDerivativeOrder_pos 0
    omega
  refine ⟨P,hP,max (quadraticRemainderConstant H C₀ C₂ C₃) 1,le_max_right _ _,?_⟩
  intro F δ v T hδ hF hv hT
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hb₀ := h₀ F δ v hδ (approximateModelPhase_mono hF (by dsimp [P]; omega) le_rfl) hv
  have hb₂ := h₂ F δ v hδ (approximateModelPhase_mono hF (by dsimp [P]; omega) le_rfl) hv
  have hb₃ := h₃ F δ v hδ (approximateModelPhase_mono hF (by dsimp [P]; omega) le_rfl) hv
  have hsupport : Function.support (modelPhaseMorseWeight χ F v) ⊆ Ioc (-H) H := by
    intro z hz
    have h := modelPhaseMorseWeight_tsupport_uniform hs hσ hδ hF₁ hv (subset_tsupport _ hz)
    dsimp [H]
    constructor <;> linarith [h.1,h.2]
  rw [modelPhaseMorseRemainder_eq_global hσ hδ hF₁ hv]
  have h := norm_quadratic_global_remainder_le
    (modelPhaseMorseWeight_contDiff hχ hs hσ hδ hF₁ hv) hT
    (by dsimp [H]; positivity : 0 < H) hsupport (by simpa only [iteratedDeriv_zero] using hb₀ 0)
    hb₂ hb₃
  exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) hT.le)

theorem modelPhaseFourierMode_stationary_uniform
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (δ T N r : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ P δ →
        0 < T → 0 < N → r*N/T ∈ modelPhaseSlopeRange F →
        ‖modelPhaseFourierMode χ F T N r-
          (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r‖ ≤
            C*N/T := by
  obtain ⟨P,hP,C,hC,hR⟩ := modelPhaseMorseRemainder_uniform hχ hs hσ
  refine ⟨P,hP,C,hC,?_⟩
  intro F δ T N r hδ hF hT hN hv
  rw [norm_modelPhaseFourierMode_sub_main hs hσ hδ
    (approximateModelPhase_mono hF hP le_rfl) hT hN hv]
  exact (mul_le_mul_of_nonneg_left (hR F δ (r*N/T) T hδ hF hv hT) hN.le).trans_eq (by ring)

end TaoTrudgianYang2025
