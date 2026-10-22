import Dubon2026.SourceOriginalInteriorArcIncidence

/-! DUB-17/18 -> original Abel-Jacobi -> curve intersection chains at the outer window.
Pull a specified outer side back by reciprocal evaluation, use exact power
lap incidence through the original place, then return its full j-side image.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {W : RadialRegion} (B : OriginalPoleRegionFamily N W)
local notation "F" => modularFunctionFieldOver N ℂ

theorem arc_through (v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0) (k : Fin W.N) {P : Place ℂ F}
    (hP : P ∈ (B.C v).carrier) (hv : originalPlaceEval N ℂ P (jOver N ℂ) ∈ W.arcSet k) :
    ∃ a : Fin (B.C v).R.N, P ∈ (B.C v).arc a ∧ LiesOver ((B.C v).arc a) (W.arcSet k) := by
  obtain ⟨σ, _, hσ⟩ := B.reciprocal.2.2.2.2.2.2
  have hvInv : originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ B.R.arcSet (σ k) := by
    rw [originalPlaceEval_inv]
    rw [← hσ k] at hv
    obtain ⟨u, hu, he⟩ := hv
    rw [← he, inv_inv]
    exact hu
  have hread (Q : Place ℂ F) (hQ : Q ∈ (B.C v).ζ.source) :
      originalPlaceEval N ℂ Q (jOver N ℂ)⁻¹ = B.R.q + (B.C v).ζ Q ^
        ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat := by
    rw [B.reciprocal.1, zero_add]
    exact ((B.geometry v).2.2.2 Q hQ).2
  obtain ⟨a, ha, himg⟩ := (B.C v).powered_arc_through (B.geometry v).2.2.1 (σ k)
    (fun Q => originalPlaceEval N ℂ Q (jOver N ℂ)⁻¹) hread hP hvInv
  refine ⟨a, ha, LiesOver.of_image_eq (B.arc_image v a).1 ?_⟩
  calc
    (fun Q => originalPlaceEval N ℂ Q (jOver N ℂ)) '' (B.C v).arc a =
        (fun z : ℂ => z⁻¹) '' ((fun Q => originalPlaceEval N ℂ Q (jOver N ℂ)⁻¹) '' (B.C v).arc a) := by
      rw [image_image]
      apply image_congr
      intro Q _
      exact (by rw [originalPlaceEval_inv, inv_inv])
    _ = W.arcSet k := by rw [himg]; exact hσ k

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
