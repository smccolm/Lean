import TaoTrudgianYang2025.BetaMorsePoisson

/-!
# Exact source remainder around the cutoff-weighted stationary main term

The Gaussian leading coefficient is normalized to the actual physical
curvature amplitude and negative-curvature phase. These are identities;
a uniform upper bound for the remainder is still an analytic obligation.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform

namespace TaoTrudgianYang2025

def modelPhaseMorseRemainder (χ F : ℝ → ℝ) (T v : ℝ) : ℂ :=
  modelPhaseMorseWeightedIntegral χ F T v -
    (modelPhaseMorseAmplitude χ F v 0/Real.sqrt T : ℂ)*(𝐞 (-(1 : ℝ)/8) : ℂ)

theorem modelPhaseMorseLeadingTerm_scale
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        ((modelPhaseMorseAmplitude χ F (r*N/T) 0/Real.sqrt T : ℂ)*
          (𝐞 (-(1 : ℝ)/8) : ℂ)) =
      (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r := by
  rw [modelPhaseMorseAmplitude_zero hσ hδ hF hv,modelPhaseStationaryMainTerm,
    modelPhasePhysicalAmplitude_eq hF hT hN hv]
  unfold modelPhaseStationaryCharacter
  rw [sub_eq_add_neg,AddChar.map_add_eq_mul,Circle.coe_mul]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,neg_div]
  ring

theorem modelPhaseFourierMode_sub_main_eq_morseRemainder
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r -
        (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        modelPhaseMorseRemainder χ F T (r*N/T) := by
  rw [modelPhaseFourierMode_morse hs hσ hδ hF hT.ne' hN hv,
    ← modelPhaseMorseLeadingTerm_scale hσ hδ hF hT hN hv]
  unfold modelPhaseMorseRemainder
  ring

theorem norm_modelPhaseFourierMode_sub_main
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    ‖modelPhaseFourierMode χ F T N r -
        (χ (modelPhaseInverseSlope F (r*N/T)) : ℂ)*modelPhaseStationaryMainTerm F T N r‖ =
      N*‖modelPhaseMorseRemainder χ F T (r*N/T)‖ := by
  rw [modelPhaseFourierMode_sub_main_eq_morseRemainder hs hσ hδ hF hT hN hv,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,Circle.norm_coe,mul_one]

end TaoTrudgianYang2025

