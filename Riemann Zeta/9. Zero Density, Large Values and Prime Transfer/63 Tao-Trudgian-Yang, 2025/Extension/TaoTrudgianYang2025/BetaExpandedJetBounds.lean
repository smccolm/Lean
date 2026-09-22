import TaoTrudgianYang2025.BetaExpandedReferenceJets
import TaoTrudgianYang2025.BetaLegendreAllOrders

/-!
# Uniform expanded-reference jet budgets

Reference coordinates are bounded on a fixed positive slope compact set.
Each actual coordinate is compared with the explicit reciprocal reference
using the original finite-order errors, including reciprocal curvature.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem expandedReferenceInverseJet_uniform_bound
    {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v ∈ Icc ((2 : ℝ)^(-σ)/2) 2,
      ∀ j ≤ K, |expandedReferenceInverseJet σ v j| ≤ B := by
  have hlo : 0 < (2 : ℝ)^(-σ)/2 := by positivity
  have hb (j : ℕ) : ∃ B : ℝ, ∀ v ∈ Icc ((2 : ℝ)^(-σ)/2) 2,
      ‖expandedReferenceInverseJet σ v j‖ ≤ B := by
    apply isCompact_Icc.exists_bound_of_continuousOn
    intro v hv
    exact (expandedReferenceInverseJet_hasDerivAt hσ (hlo.trans_le hv.1) j).continuousAt.continuousWithinAt
  choose B hB using hb
  have hs : 0 ≤ ∑ j ∈ Finset.range (K+1), |B j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨1+(∑ j ∈ Finset.range (K+1), |B j|),by linarith,?_⟩
  intro v hv j hj
  have hsingle := Finset.single_le_sum (s := Finset.range (K+1))
    (fun i _ => abs_nonneg (B i)) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have h := hB j v hv
  rw [Real.norm_eq_abs] at h
  exact h.trans ((le_abs_self (B j)).trans (hsingle.trans (by linarith)))

theorem abs_inverse_sub_inverse_le_product
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |a⁻¹-b⁻¹| ≤ |a-b| *|a⁻¹| *|b⁻¹| := by
  have he : a⁻¹-b⁻¹ = (b-a)*a⁻¹*b⁻¹ := by field_simp
  rw [he,abs_mul,abs_mul,abs_sub_comm]

theorem modelPhaseInverseJet_expanded_reference_error
    {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ) (P : ℕ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      1 ≤ P → IsApproximateModelPhaseFunction F σ P δ → j ≤ P →
      ∀ v ∈ modelPhaseSlopeRange F,
        |modelPhaseInverseJet F v j-expandedReferenceInverseJet σ v j| ≤ C*δ := by
  match j with
  | 0 =>
      obtain ⟨C,hC,hbound⟩ := modelPhaseInverseSlope_expanded_model_error hσ
      refine ⟨C,hC,?_⟩
      intro F δ P _ hpos _ hF _ v hv
      exact hbound F δ P hpos hF v hv
  | 1 =>
      obtain ⟨A,hA,hjet⟩ := modelPhaseInverse_iteratedDeriv_expanded_reference_error hσ 1
      obtain ⟨B,hB,hreference⟩ := expandedReferenceInverseJet_uniform_bound hσ 1
      let M := (modelPhaseCurvatureLower σ)⁻¹
      have hM : 0 ≤ M := inv_nonneg.mpr (modelPhaseCurvatureLower_pos hσ).le
      refine ⟨max 1 (A*M*B),le_max_left _ _,?_⟩
      intro F δ P hδ hpos hP hF hj v hv
      have hF₁ := approximateModelPhase_mono hF hP le_rfl
      have hu := modelPhaseInverseSlope_mem hv
      have hw := modelPhaseSlopeRange_positive_window hσ hpos hF hv
      have hvpos : 0 < v := (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le hw.1
      have ha := approximateModelPhase_secondDeriv_ne_zero hσ hδ hF₁ hu
      have hb := referenceModelPrimitive_secondDeriv_reciprocal_ne_zero hσ hvpos
      have hx := modelPhaseInverseJet_abs_le hσ hδ hP hF hv 1 hj
      have hy := hreference v hw 1 le_rfl
      have he := hjet F δ P hpos hF hj v hv
      simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
      change |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹| ≤ M at hx
      change |(deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹| ≤ B at hy
      change |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹-
        (deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹| ≤ _
      have hd := approximateModelPhase_tolerance_nonneg hF
      calc
        _ ≤ |deriv (deriv F) (modelPhaseInverseSlope F v)-
            deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹))| *
            |(deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹| *
            |(deriv (deriv (referenceModelPrimitive σ)) (v^(-σ⁻¹)))⁻¹| :=
          abs_inverse_sub_inverse_le_product ha hb
        _ ≤ (A*δ)*M*B := mul_le_mul
          (mul_le_mul he hx (abs_nonneg _) (mul_nonneg (zero_le_one.trans hA) hd))
          hy (abs_nonneg _) (mul_nonneg (mul_nonneg (zero_le_one.trans hA) hd) hM)
        _ = (A*M*B)*δ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hd
  | n+2 =>
      obtain ⟨C,hC,hbound⟩ := modelPhaseInverse_iteratedDeriv_expanded_reference_error hσ (n+1)
      refine ⟨C,hC,?_⟩
      intro F δ P _ hpos _ hF hj v hv
      exact hbound F δ P hpos hF (by omega) v hv

end TaoTrudgianYang2025
