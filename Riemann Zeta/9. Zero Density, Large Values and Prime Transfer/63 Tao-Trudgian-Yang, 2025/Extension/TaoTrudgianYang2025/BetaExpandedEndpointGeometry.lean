import TaoTrudgianYang2025.BetaTaylorPastedUniform

/-!
# Positive compact bounds for the genuine closed endpoint slopes

This includes the original one-sided endpoint convention. It does not
differentiate an arbitrary exterior extension of the original phase.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

theorem modelPhaseClosedSlope_positive_window
    {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseClosedSlope F u ∈ Icc ((2 : ℝ)^(-σ)/2) 2 := by
  have he := abs_le.mp (modelPhaseClosedSlope_model_error hF hu)
  have hp : 0 < u := zero_lt_one.trans_le hu.1
  have hlow := Real.rpow_le_rpow_of_nonpos hp hu.2 (neg_nonpos.mpr hσ.le)
  have hhigh := Real.rpow_le_one_of_one_le_of_nonpos hu.1 (neg_nonpos.mpr hσ.le)
  have hd₁ := hδ.trans (min_le_left _ _)
  have hd₂ := hδ.trans (min_le_right _ _)
  have hbase : 0 < (2 : ℝ)^(-σ) := by positivity
  constructor <;> linarith [he.1,he.2]

theorem modelPhaseClosedSlope_endpoint_width
    {F : ℝ → ℝ} {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseCurvatureLower σ ≤ modelPhaseClosedSlope F 1-modelPhaseClosedSlope F 2 := by
  simpa only [show (2 : ℝ)-1 = 1 by norm_num,mul_one] using
    modelPhaseClosedSlope_drop hσ hδ hF
      (u := 1) (v := 2) (by norm_num) (by norm_num) (by norm_num)

end TaoTrudgianYang2025
