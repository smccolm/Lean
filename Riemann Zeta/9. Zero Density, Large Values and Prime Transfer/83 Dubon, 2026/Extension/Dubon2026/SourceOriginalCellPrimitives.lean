import Dubon2026.SourceOriginalAnalyticCells
import Dubon2026.SourceOriginalCellCoefficientPullback
import Dubon2026.SourceCellRadialPrimitive

/-! DUB-17/18 -> raw geometric reciprocity -> cell primitives.
Every original regular differential has a normalized analytic primitive on an
open star-convex neighborhood of a genuine cell. The domain and primitive are
constructed from the proved radial geometry and actual coefficient calculus;
neither is supplied as a hypothesis. Cell dissection, jumps and reciprocity remain.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem AnalyticCoord.analyticAt_coeff (A : AnalyticCoord N) (θ : Ω[F⁄ℂ])
    {w : ℂ} (hw : w ∈ A.ζ.target)
    (hθ : (A.ζ.symm w).differentialCoeff θ ∈ (A.ζ.symm w).toValuationSubring) :
    AnalyticAt ℂ (coeffIn A.ζ θ) w := by
  have h := (A.coeff_eq_near (A.ζ.map_target hw) hθ).2
  rwa [A.ζ.right_inv hw] at h

theorem Cell.exists_regular_primitives (C : Cell N) {ι : Type*} (η : ι → Ω[F⁄ℂ])
    (hη : ∀ i, η i ∈ regularDifferentials ℂ F) :
    ∃ (V : Set ℂ) (Ψ : ι → ℂ → ℂ), IsOpen V ∧ C.R.q ∈ V ∧
      StarConvex ℝ C.R.q V ∧ C.R.K ⊆ V ∧ V ⊆ C.ζ.target ∧
      ∀ i, Ψ i C.R.q = 0 ∧ ∀ w ∈ V, HasDerivAt (Ψ i) (coeffIn C.ζ (η i) w) w := by
  obtain ⟨V, hVo, hVq, hVs, hKV, hVt⟩ := C.exists_primitive_domain
  have hprim : ∀ i, ∃ Ψ : ℂ → ℂ, Ψ C.R.q = 0 ∧
      ∀ w ∈ V, HasDerivAt Ψ (coeffIn C.ζ (η i) w) w := by
    intro i
    apply exists_radial_primitive hVo hVs
    intro w hw
    exact (C.toAnalyticCoord.analyticAt_coeff (η i) (hVt hw)
      ((mem_original_regularDifferentials_iff N ℂ (η i)).mp (hη i) _)).differentiableAt.differentiableWithinAt
  choose Ψ hΨ0 hΨ using hprim
  exact ⟨V, Ψ, hVo, hVq, hVs, hKV, hVt, fun i => ⟨hΨ0 i, hΨ i⟩⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
