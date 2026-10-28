import Dubon2026.SourceSmoothModularGeometry
import Dubon2026.SourceComplexHolomorphicStokes

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> smooth divisor integral.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
Reuse the proved action geometry and compact-support continuity. The finite
orbit sum is unfolded by native change of variables. Compact support permits
eventual exact equality instead of a separate dominated-convergence argument.
No integral identity, comparison function or period identity is assumed. -/
namespace Dubon2026.SourceSmoothOrbitIntegral
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set Metric SourceSmoothDivisor
open scoped MatrixGroups Topology Real ComplexConjugate
local notation "UHP" => UpperHalfPlane.upperHalfPlaneSet

theorem sm_image (σ : SL(2, ℤ)) : sm σ '' UHP = UHP := by
  ext w
  constructor
  · rintro ⟨z, -, rfl⟩; exact im_sm_pos σ z
  · intro hw
    exact ⟨sm σ⁻¹ w, im_sm_pos _ _, by rw [← sm_mul, mul_inv_cancel, sm_one hw]⟩

theorem continuousAt_ofComplex' {z : ℂ} (hz : 0 < z.im) : ContinuousAt ofComplex z :=
  (mdifferentiableAt_ofComplex hz).continuousAt

theorem hasFDerivAt_sm_matrix (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (sm σ) (UpperHalfPlane.smulFDeriv (σ : GL (Fin 2) ℝ) z) z := by
  have := (UpperHalfPlane.hasStrictFDerivAt_smul (σ : GL (Fin 2) ℝ) ⟨z, hz⟩).hasFDerivAt
  exact this

theorem continuousOn_sm (σ : SL(2, ℤ)) : ContinuousOn (sm σ) UHP := fun _ hz =>
  (hasFDerivAt_sm_matrix σ hz).continuousAt.continuousWithinAt

theorem denom_ofComplex {σ : SL(2, ℤ)} {z : ℂ} (hz : 0 < z.im) :
    denom (σ : GL (Fin 2) ℝ) (ofComplex z) = denom (σ : GL (Fin 2) ℝ) z := by
  simp only [denom, coe_ofComplex hz]

theorem denom_ne_zero' (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom (σ : GL (Fin 2) ℝ) z ≠ 0 := by
  rw [← denom_ofComplex hz]; exact denom_ne_zero _ _

theorem continuousOn_dsm (σ : SL(2, ℤ)) : ContinuousOn (dsm σ) UHP := by
  have h : ContinuousOn (fun z : ℂ => 1 / denom (σ : GL (Fin 2) ℝ) z ^ 2) UHP := by
    refine continuousOn_const.div ?_ fun z hz => pow_ne_zero _ (denom_ne_zero' σ hz)
    simp only [denom]
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousOn.pow 2
  refine h.congr fun z hz => ?_
  simp only [dsm, denom_ofComplex (σ := σ) hz]

theorem eq_zero_of_notMem {ψ : ℂ → ℂ} (hψV : tsupport ψ ⊆ UHP) {z : ℂ} (hz : ¬ 0 < z.im) : ψ z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (hψV h)


end
end Dubon2026.SourceSmoothOrbitIntegral
