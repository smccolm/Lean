import TaoTrudgianYang2025.BetaModelJetEstimates

/-!
# Uniform bounds for the actual inverse-derivative jet coordinates

The magnitude and error constants depend only on sigma and the finite
coordinate index. They are derived from the original model-phase errors.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def inverseJetMagnitude (σ : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => (modelPhaseCurvatureLower σ)⁻¹
  | n+2 => modelPhaseJetCoefficient σ (n+1)+1

def inverseJetError (σ : ℝ) : ℕ → ℝ
  | 0 => (modelPhaseCurvatureLower σ)⁻¹
  | 1 => (1+modelPhaseJetCoefficient σ 2/modelPhaseCurvatureLower σ) /
      (modelPhaseCurvatureLower σ)^2
  | n+2 => 1+modelPhaseJetCoefficient σ (n+2)/modelPhaseCurvatureLower σ

theorem inverseJetMagnitude_nonneg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ inverseJetMagnitude σ j := by
  have hc := (modelPhaseCurvatureLower_pos hσ).le
  match j with
  | 0 => norm_num [inverseJetMagnitude]
  | 1 => exact inv_nonneg.mpr hc
  | n+2 => exact add_nonneg (modelPhaseJetCoefficient_nonneg σ (n+1)) zero_le_one

theorem inverseJetError_nonneg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ inverseJetError σ j := by
  have hc := (modelPhaseCurvatureLower_pos hσ).le
  match j with
  | 0 => exact inv_nonneg.mpr hc
  | 1 =>
      exact div_nonneg (add_nonneg zero_le_one
        (div_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hc)) (sq_nonneg _)
  | n+2 =>
      exact add_nonneg zero_le_one
        (div_nonneg (modelPhaseJetCoefficient_nonneg σ (n+2)) hc)

theorem modelPhaseInverseJet_abs_le
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (j : ℕ) (hj : j ≤ P) :
    |modelPhaseInverseJet F v j| ≤ inverseJetMagnitude σ j := by
  have hu := modelPhaseInverseSlope_mem hv
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  match j with
  | 0 =>
      change |modelPhaseInverseSlope F v| ≤ 2
      rw [abs_of_pos (zero_lt_one.trans hu.1)]
      exact hu.2.le
  | 1 =>
      have hb := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF₁ hu).1
      have hc := modelPhaseCurvatureLower_pos hσ
      have hn : deriv (deriv F) (modelPhaseInverseSlope F v) < 0 := by linarith
      change |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹| ≤
        (modelPhaseCurvatureLower σ)⁻¹
      rw [abs_inv, abs_of_neg hn]
      exact inv_anti₀ hc hb
  | n+2 =>
      have hp : n+1 ≤ P := by omega
      have he := approximateModelPhase_iteratedDeriv_error hF hu (n+1) hp
      have hb := iteratedDeriv_modelPhase_abs_le hσ.le hu (n+1)
      have ht := abs_add_le
        (iteratedDeriv (n+2) F (modelPhaseInverseSlope F v) -
          iteratedDeriv (n+1) (modelPhase σ) (modelPhaseInverseSlope F v))
        (iteratedDeriv (n+1) (modelPhase σ) (modelPhaseInverseSlope F v))
      rw [sub_add_cancel] at ht
      change |iteratedDeriv (n+2) F (modelPhaseInverseSlope F v)| ≤
        modelPhaseJetCoefficient σ (n+1)+1
      have hd : δ ≤ 1 := hδ.trans (min_le_right _ _)
      linarith

theorem modelPhaseInverseJet_reference_error
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (j : ℕ) (hj : j ≤ P) :
    |modelPhaseInverseJet F v j -
      modelPhaseInverseJet (referenceModelPrimitive σ) v j| ≤ inverseJetError σ j * δ := by
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  match j with
  | 0 =>
      change |modelPhaseInverseSlope F v -
        modelPhaseInverseSlope (referenceModelPrimitive σ) v| ≤
        (modelPhaseCurvatureLower σ)⁻¹ * δ
      rw [referenceModelPrimitive_inverse hσ hm]
      simpa only [div_eq_mul_inv, mul_comm] using
        modelPhaseInverseSlope_model_error hσ hδ hF₁ hv hm
  | 1 =>
      have hu := modelPhaseInverseSlope_mem hv
      have hr := modelPhaseInverseSlope_mem (referenceModelPrimitive_slopeRange hσ hm)
      have hc := modelPhaseCurvatureLower_pos hσ
      have ha := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF₁ hu).1
      have hb := (approximateModelPhase_curvature_deriv_bounds hσ
        (le_min hc.le zero_le_one) (referenceModelPrimitive_approximate σ 1) hr).1
      have he := modelPhaseInverse_iteratedDeriv_reference_error hσ hδ hP hF hv hm 1 hP
      simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
      have hi := inverse_difference_le_curvature hc ha hb
      change |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ -
        (deriv (deriv (referenceModelPrimitive σ))
          (modelPhaseInverseSlope (referenceModelPrimitive σ) v))⁻¹| ≤ _
      exact hi.trans ((div_le_div_of_nonneg_right he (sq_nonneg _)).trans_eq (by
        dsimp [inverseJetError]
        ring))
  | n+2 =>
      have hp : n+1 ≤ P := by omega
      exact modelPhaseInverse_iteratedDeriv_reference_error hσ hδ hP hF hv hm (n+1) hp

end TaoTrudgianYang2025
