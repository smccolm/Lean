import TaoTrudgianYang2025.BetaSlopeInverse

/-!
# Sign-normalized Legendre dual of an actual model phase

The dual is v*u-F(u), where F'(u)=v. It is smooth on the actual slope
image and has negative reciprocal curvature. The stationary-phase exponent
F(u)-v*u has the opposite sign; the identity below records that convention.
This does not yet prove the B-process exponential-sum transformation.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def modelPhaseLegendreDual (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * modelPhaseInverseSlope F v - F (modelPhaseInverseSlope F v)

theorem modelPhaseLegendreDual_contDiffAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseLegendreDual F) v := by
  have hi := modelPhaseInverseSlope_contDiffAt hσ hδ hF hv
  exact (contDiffAt_id.mul hi).sub
    ((approximateModelPhase_contDiffAt hF (modelPhaseInverseSlope_mem hv)).comp v hi)

theorem modelPhaseLegendreDual_hasDerivAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v) v := by
  have hi := (modelPhaseInverseSlope_hasStrictDerivAt hσ hδ hF hv).hasDerivAt
  have hf := (approximateModelPhase_contDiffAt hF (modelPhaseInverseSlope_mem hv)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  convert ((hasDerivAt_id v).mul hi).sub (hf.hasDerivAt.comp v hi) using 1
  rw [deriv_modelPhaseInverseSlope_apply hv, id_eq]
  ring

theorem deriv_modelPhaseLegendreDual {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    deriv (modelPhaseLegendreDual F) v = modelPhaseInverseSlope F v :=
  (modelPhaseLegendreDual_hasDerivAt hσ hδ hF hv).deriv

theorem modelPhaseLegendreDual_deriv_hasDerivAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (deriv (modelPhaseLegendreDual F))
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ v := by
  apply (modelPhaseInverseSlope_hasStrictDerivAt hσ hδ hF hv).hasDerivAt.congr_of_eventuallyEq
  filter_upwards [(modelPhaseSlopeRange_isOpen hσ hδ hF).mem_nhds hv] with w hw
  exact deriv_modelPhaseLegendreDual hσ hδ hF hw

theorem modelPhaseLegendreDual_secondDeriv {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    deriv (deriv (modelPhaseLegendreDual F)) v =
      (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹ :=
  (modelPhaseLegendreDual_deriv_hasDerivAt hσ hδ hF hv).deriv

theorem modelPhaseLegendreDual_curvature_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    (σ+1)⁻¹ ≤ -deriv (deriv (modelPhaseLegendreDual F)) v ∧
      -deriv (deriv (modelPhaseLegendreDual F)) v ≤ (modelPhaseCurvatureLower σ)⁻¹ := by
  rw [modelPhaseLegendreDual_secondDeriv hσ hδ hF hv, ← inv_neg]
  have hb := approximateModelPhase_curvature_deriv_bounds hσ hδ hF
    (modelPhaseInverseSlope_mem hv)
  have hp := modelPhaseCurvatureLower_pos hσ
  exact ⟨inv_anti₀ (hp.trans_le hb.1) hb.2, inv_anti₀ hp hb.1⟩

theorem modelPhaseLegendreDual_at_deriv {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseLegendreDual F (deriv F u) = deriv F u * u - F u := by
  simp only [modelPhaseLegendreDual, modelPhaseInverseSlope_deriv hσ hδ hF hu]

theorem modelPhaseLegendreDual_stationary_sign {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    F u - deriv F u * u = -modelPhaseLegendreDual F (deriv F u) := by
  rw [modelPhaseLegendreDual_at_deriv hσ hδ hF hu]
  ring

end TaoTrudgianYang2025
