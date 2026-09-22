import TaoTrudgianYang2025.BetaMorseInverse

/-!
# Uniform first-derivative bounds for the quadratic change of variables

The original curvature bounds control both the coordinate and its
actual inverse on their full open domains. No compactness constant
depending on the individual phase is used in these bounds.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem approximateModelPhase_slope_gap_upper_abs
    {F : ℝ → ℝ} {σ δ u w : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) :
    |deriv F u-deriv F w| ≤ (σ+1)*|u-w| := by
  have hd : ∀ x ∈ Ioo (1 : ℝ) 2,
      HasDerivWithinAt (deriv F) (deriv (deriv F) x) (Ioo (1 : ℝ) 2) x :=
    fun _ hx => ((approximateModelPhase_deriv_contDiffAt hF hx).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.hasDerivWithinAt
  have hb : ∀ x ∈ Ioo (1 : ℝ) 2, ‖deriv (deriv F) x‖ ≤ σ+1 := by
    intro x hx
    have h := approximateModelPhase_curvature_deriv_bounds hσ hδ hF hx
    have hp := modelPhaseCurvatureLower_pos hσ
    rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : deriv (deriv F) x ≤ 0)]
    exact h.2
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (1 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hw hu

theorem modelPhaseMorseCoordinate_deriv_bounds
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤ deriv (modelPhaseMorseCoordinate F v) u ∧
      deriv (modelPhaseMorseCoordinate F v) u ≤ (σ+1)/Real.sqrt (modelPhaseCurvatureLower σ) := by
  have hc := modelPhaseCurvatureLower_pos hσ
  have hC : 0 < σ+1 := by linarith
  have hsc := Real.sqrt_pos.mpr hc
  have hsC := Real.sqrt_pos.mpr hC
  by_cases heq : u = modelPhaseInverseSlope F v
  · rw [heq,(modelPhaseMorseCoordinate_hasDerivAt_inverse hF hv).deriv]
    have h := modelPhaseCurvatureAt_bounds hσ hδ hF hv
    have h₁ := Real.sqrt_le_sqrt h.1
    have h₂ := Real.sqrt_le_sqrt h.2
    constructor
    · apply (div_le_iff₀ hsC).mpr
      calc
        modelPhaseCurvatureLower σ =
            Real.sqrt (modelPhaseCurvatureLower σ)*Real.sqrt (modelPhaseCurvatureLower σ) := by
          rw [← sq,Real.sq_sqrt hc.le]
        _ ≤ Real.sqrt (modelPhaseCurvatureAt F v)*Real.sqrt (σ+1) :=
          mul_le_mul h₁ (h₁.trans h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply (le_div_iff₀ hsc).mpr
      calc
        Real.sqrt (modelPhaseCurvatureAt F v)*Real.sqrt (modelPhaseCurvatureLower σ) ≤
            Real.sqrt (σ+1)*Real.sqrt (σ+1) :=
          mul_le_mul h₂ (h₁.trans h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = σ+1 := by rw [← sq,Real.sq_sqrt hC.le]
  · have hdist : 0 < |u-modelPhaseInverseSlope F v| :=
      abs_pos.mpr (sub_ne_zero.mpr heq)
    have hp := modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu
    have hrel := congrArg abs (modelPhaseMorseCoordinate_deriv_mul hσ hδ hF hv hu)
    rw [abs_mul,abs_of_pos hp] at hrel
    have hgl := approximateModelPhase_slope_gap_abs hσ hδ hF hu (modelPhaseInverseSlope_mem hv)
    have hgu := approximateModelPhase_slope_gap_upper_abs hσ hδ hF hu (modelPhaseInverseSlope_mem hv)
    rw [deriv_modelPhaseInverseSlope_apply hv,abs_sub_comm (deriv F u) v] at hgl hgu
    have hd := modelPhaseMorseCoordinate_bounds hσ hδ hF hv hu
    constructor
    · apply (div_le_iff₀ hsC).mpr
      have h := hgl.trans (hrel.symm.le.trans
        (mul_le_mul_of_nonneg_right hd.2 hp.le))
      apply le_of_mul_le_mul_left (a := |u-modelPhaseInverseSlope F v|) ?_ hdist
      nlinarith only [h]
    · apply (le_div_iff₀ hsc).mpr
      have h := (mul_le_mul_of_nonneg_right hd.1 hp.le).trans (hrel.le.trans hgu)
      apply le_of_mul_le_mul_left (a := |u-modelPhaseInverseSlope F v|) ?_ hdist
      nlinarith only [h]

theorem modelPhaseMorseInverse_deriv_bounds
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    Real.sqrt (modelPhaseCurvatureLower σ)/(σ+1) ≤ deriv (modelPhaseMorseInverse F v) z ∧
      deriv (modelPhaseMorseInverse F v) z ≤ Real.sqrt (σ+1)/modelPhaseCurvatureLower σ := by
  rw [(modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv hz).hasDerivAt.deriv]
  have h := modelPhaseMorseCoordinate_deriv_bounds hσ hδ hF hv (modelPhaseMorseInverse_mem hz)
  have hp := modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv (modelPhaseMorseInverse_mem hz)
  have hc := modelPhaseCurvatureLower_pos hσ
  have hC : 0 < σ+1 := by linarith
  constructor
  · have h' := one_div_le_one_div_of_le hp h.2
    simpa only [one_div,inv_div] using h'
  · have h' := one_div_le_one_div_of_le (div_pos hc (Real.sqrt_pos.mpr hC)) h.1
    simpa only [one_div,inv_div] using h'

end TaoTrudgianYang2025
