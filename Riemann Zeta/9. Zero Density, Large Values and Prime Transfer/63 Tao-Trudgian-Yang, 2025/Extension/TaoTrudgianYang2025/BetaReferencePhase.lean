import TaoTrudgianYang2025.BetaInverseJets
import TaoTrudgianYang2025.BetaInverseStability

/-!
# Exact reference primitive and its reciprocal-exponent inverse

The logarithmic and power primitives are genuine zero-error model phases,
including every derivative order and both endpoints of [1,2].
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def referenceModelPrimitive (σ u : ℝ) : ℝ :=
  if σ = 1 then Real.log u else u^(1-σ)/(1-σ)

theorem referenceModelPrimitive_contDiffAt (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (referenceModelPrimitive σ) u := by
  unfold referenceModelPrimitive
  by_cases hσ : σ = 1
  · simpa only [hσ, if_pos rfl] using
      (Real.contDiffAt_log.mpr hu.ne' : ContDiffAt ℝ ∞ Real.log u)
  · simp only [if_neg hσ]
    exact (Real.contDiffAt_rpow_const_of_ne hu.ne').div_const (1-σ)

theorem referenceModelPrimitive_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (referenceModelPrimitive σ) (u^(-σ)) u := by
  unfold referenceModelPrimitive
  by_cases hσ : σ = 1
  · subst σ
    simpa only [if_pos rfl, Real.rpow_neg_one] using
      Real.hasDerivAt_log hu.ne'
  · have hn : 1-σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
    simp only [if_neg hσ]
    convert (Real.hasDerivAt_rpow_const (Or.inl hu.ne') (p := 1-σ)).div_const (1-σ) using 1
    rw [show 1-σ-1 = -σ by ring]
    field_simp

theorem referenceModelPrimitive_iteratedDeriv (σ : ℝ) {u : ℝ} (hu : 0 < u) (p : ℕ) :
    iteratedDeriv (p+1) (referenceModelPrimitive σ) u =
      iteratedDeriv p (modelPhase σ) u := by
  have he : deriv (referenceModelPrimitive σ) =ᶠ[𝓝 u] modelPhase σ := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with w hw
    exact (referenceModelPrimitive_hasDerivAt σ hw).deriv
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq p]

theorem referenceModelPrimitive_approximate (σ : ℝ) (P : ℕ) :
    IsApproximateModelPhaseFunction (referenceModelPrimitive σ) σ P 0 := by
  refine ⟨fun u hu => (referenceModelPrimitive_contDiffAt σ
    (zero_lt_one.trans_le hu.1)).contDiffWithinAt, ?_⟩
  intro p _ u
  have hu : 0 < (u : ℝ) := zero_lt_one.trans_le u.property.1
  have hc : ContDiffAt ℝ (p+1) (referenceModelPrimitive σ) u :=
    (referenceModelPrimitive_contDiffAt σ hu).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p+1))
  have hm : ContDiffAt ℝ p (modelPhase σ) u :=
    Real.contDiffAt_rpow_const_of_ne hu.ne'
  rw [modelPhaseErrorAt, iteratedDerivWithin_eq_iteratedDeriv
    uniqueDiffOn_phaseInterval hc u.property,
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm u.property,
    referenceModelPrimitive_iteratedDeriv σ hu p, sub_self, norm_zero]

theorem referenceModelPrimitive_inverse {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    modelPhaseInverseSlope (referenceModelPrimitive σ) v = v^(-σ⁻¹) := by
  have hw := reciprocal_modelPhase_mem hσ hv
  have hp : 0 ≤ v :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).le.trans hv.1.le
  have he := (referenceModelPrimitive_hasDerivAt σ (zero_lt_one.trans hw.1)).deriv
  rw [reciprocal_modelPhase_identity hσ hp] at he
  have hi := modelPhaseInverseSlope_deriv hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one)
    (referenceModelPrimitive_approximate σ 1) hw
  rwa [he] at hi

theorem referenceModelPrimitive_slopeRange {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) :
    v ∈ modelPhaseSlopeRange (referenceModelPrimitive σ) := by
  have hw := reciprocal_modelPhase_mem hσ hv
  refine ⟨v^(-σ⁻¹), hw, ?_⟩
  rw [(referenceModelPrimitive_hasDerivAt σ (zero_lt_one.trans hw.1)).deriv]
  apply reciprocal_modelPhase_identity hσ
  exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).le.trans hv.1.le

theorem referenceModelPrimitive_inverseJet_formula {σ v : ℝ} (hσ : 0 < σ)
    (hv : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) (n : ℕ) :
    iteratedDeriv n (modelPhase σ⁻¹) v =
      inversePhaseEval (inversePhaseDerivativeExpression n)
        (modelPhaseInverseJet (referenceModelPrimitive σ) v) := by
  have he : modelPhaseInverseSlope (referenceModelPrimitive σ) =ᶠ[𝓝 v]
      modelPhase σ⁻¹ := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
    exact referenceModelPrimitive_inverse hσ hw
  rw [← he.iteratedDeriv_eq n]
  exact iteratedDeriv_modelPhaseInverseSlope_formula hσ
    (le_min (modelPhaseCurvatureLower_pos hσ).le zero_le_one)
    (referenceModelPrimitive_approximate σ 1)
    (referenceModelPrimitive_slopeRange hσ hv) n

end TaoTrudgianYang2025
