import Dubon2026.SourceOriginalGlobalCellCover

/-! DUB-17/18 -> original Abel-Jacobi -> marked dissection conditions.
The actual coordinate identifies a unique cell center and places it in the
cell interior. These facts turn the constructed marked grid into the exact
one-pole-per-carrier and centered-pole hypotheses of the residue theorem.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem RadialRegion.center_mem_Kint (R : RadialRegion) : R.q ∈ R.Kint := by
  change ‖R.q - R.q‖ < R.r (Complex.arg (R.q - R.q))
  simpa only [sub_self, norm_zero] using R.hpos (Complex.arg (0 : ℂ))

theorem Cell.mem_interior_iff_coordinate (C : Cell N) (P : Place ℂ F) :
    P ∈ C.interior' ↔ P ∈ C.ζ.source ∧ C.ζ P ∈ C.R.Kint := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hK : z ∈ C.R.K := by
      change ‖z - C.R.q‖ ≤ C.R.r (Complex.arg (z - C.R.q))
      exact (show ‖z - C.R.q‖ < C.R.r (Complex.arg (z - C.R.q)) from hz).le
    exact ⟨C.ζ.map_target (C.hKt hK), (C.ζ.right_inv (C.hKt hK)).symm ▸ hz⟩
  · rintro ⟨hP, hz⟩
    exact ⟨C.ζ P, hz, C.ζ.left_inv hP⟩

theorem Cell.center_interior (C : Cell N) {P : Place ℂ F} (hP : P ∈ C.carrier)
    (hcenter : C.ζ P = C.R.q) : P ∈ C.interior' := by
  apply (C.mem_interior_iff_coordinate P).mpr
  refine ⟨((C.mem_carrier_iff_coordinate P).mp hP).1, ?_⟩
  rw [hcenter]
  exact C.R.center_mem_Kint

theorem Cell.eq_of_coordinate_eq (C : Cell N) {P Q : Place ℂ F}
    (hP : P ∈ C.carrier) (hQ : Q ∈ C.carrier) (heq : C.ζ P = C.ζ Q) : P = Q := by
  have hp := ((C.mem_carrier_iff_coordinate P).mp hP).1
  have hq := ((C.mem_carrier_iff_coordinate Q).mp hQ).1
  calc
    P = C.ζ.symm (C.ζ P) := (C.ζ.left_inv hp).symm
    _ = C.ζ.symm (C.ζ Q) := congrArg C.ζ.symm heq
    _ = Q := C.ζ.left_inv hq

end
end Dubon2026.SourceFunctionField.CellGeometry
