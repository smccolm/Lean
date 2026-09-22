import TaoTrudgianYang2025.BetaInverseJetBounds

/-!
# Uniform all-order model errors for the actual Legendre phase

For each fixed derivative order, one explicit finite expression yields a
bound depending only on sigma and that order. The phase and slope point
are arbitrary within the original model assumptions and common slope domain.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

def inverseJetMagnitudeBudget (σ : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), inverseJetMagnitude σ j

def inverseJetErrorBudget (σ : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), inverseJetError σ j

def legendreModelErrorConstant (σ : ℝ) (n : ℕ) : ℝ :=
  inversePhaseSensitivity (inversePhaseDerivativeExpression n)
    (inverseJetMagnitudeBudget σ (inversePhaseOrder (inversePhaseDerivativeExpression n))) *
      inverseJetErrorBudget σ (inversePhaseOrder (inversePhaseDerivativeExpression n))

theorem inverseJetMagnitudeBudget_nonneg {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    0 ≤ inverseJetMagnitudeBudget σ K :=
  Finset.sum_nonneg fun j _ => inverseJetMagnitude_nonneg hσ j

theorem inverseJetErrorBudget_nonneg {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    0 ≤ inverseJetErrorBudget σ K :=
  Finset.sum_nonneg fun j _ => inverseJetError_nonneg hσ j

theorem inverseJetMagnitude_le_budget {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    inverseJetMagnitude σ j ≤ inverseJetMagnitudeBudget σ K :=
  Finset.single_le_sum (fun k _ => inverseJetMagnitude_nonneg hσ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem inverseJetError_le_budget {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    inverseJetError σ j ≤ inverseJetErrorBudget σ K :=
  Finset.single_le_sum (fun k _ => inverseJetError_nonneg hσ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem legendreModelErrorConstant_nonneg {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 ≤ legendreModelErrorConstant σ n :=
  mul_nonneg (inversePhaseSensitivity_nonneg _
    (inverseJetMagnitudeBudget_nonneg hσ _)) (inverseJetErrorBudget_nonneg hσ _)

theorem approximateModelPhase_tolerance_nonneg
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    0 ≤ δ :=
  (norm_nonneg _).trans (hF.2 0 (Nat.zero_le P) ⟨1, by norm_num [phaseInterval]⟩)

theorem modelPhaseLegendreDual_iteratedDeriv_model_error
    {σ δ : ℝ} {F : ℝ → ℝ} (n : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ
      (inversePhaseOrder (inversePhaseDerivativeExpression n)+1) δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
      iteratedDeriv n (modelPhase σ⁻¹) v| ≤ legendreModelErrorConstant σ n * δ := by
  let K := inversePhaseOrder (inversePhaseDerivativeExpression n)
  have hP : 1 ≤ K+1 := by omega
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  rw [iteratedDeriv_modelPhaseLegendreDual_formula hσ hδ hF₁ hv n,
    referenceModelPrimitive_inverseJet_formula hσ hm n]
  have hx : ∀ j ≤ K, |modelPhaseInverseJet F v j| ≤ inverseJetMagnitudeBudget σ K := by
    intro j hj
    exact (modelPhaseInverseJet_abs_le hσ hδ hP hF hv j (by omega)).trans
      (inverseJetMagnitude_le_budget hσ hj)
  have hy : ∀ j ≤ K, |modelPhaseInverseJet (referenceModelPrimitive σ) v j| ≤
      inverseJetMagnitudeBudget σ K := by
    intro j hj
    exact (modelPhaseInverseJet_abs_le hσ
      (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one) hP
      (referenceModelPrimitive_approximate σ (K+1))
      (referenceModelPrimitive_slopeRange hσ hm) j (by omega)).trans
      (inverseJetMagnitude_le_budget hσ hj)
  have he : ∀ j ≤ K, |modelPhaseInverseJet F v j -
      modelPhaseInverseJet (referenceModelPrimitive σ) v j| ≤ inverseJetErrorBudget σ K*δ := by
    intro j hj
    exact (modelPhaseInverseJet_reference_error hσ hδ hP hF hv hm j (by omega)).trans
      (mul_le_mul_of_nonneg_right (inverseJetError_le_budget hσ hj)
        (approximateModelPhase_tolerance_nonneg hF))
  have h := inversePhaseEval_difference_le (inversePhaseDerivativeExpression n)
    (inverseJetMagnitudeBudget_nonneg hσ K) hx hy he
  simpa only [legendreModelErrorConstant, mul_assoc] using h

theorem modelPhaseLegendreDual_allOrder_uniformity {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ P : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ P δ →
      ∀ v : ℝ, v ∈ modelPhaseSlopeRange F → v ∈ Ioo ((2 : ℝ)^(-σ)) 1 →
        |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ C*δ := by
  refine ⟨inversePhaseOrder (inversePhaseDerivativeExpression n)+1,
    legendreModelErrorConstant σ n+1, by linarith [legendreModelErrorConstant_nonneg hσ n], ?_⟩
  intro δ hδ F hF v hv hm
  exact (modelPhaseLegendreDual_iteratedDeriv_model_error n hσ hδ hF hv hm).trans
    (mul_le_mul_of_nonneg_right (by linarith) (approximateModelPhase_tolerance_nonneg hF))

end TaoTrudgianYang2025
