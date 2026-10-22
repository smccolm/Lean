import Dubon2026.SourceOriginalCarrierRegions

/-! DUB-17/18 -> original Abel-Jacobi -> lifting planar intersection chains.
If the coordinate value of an actual point belongs to a specified base side,
one power lap contains that point and maps onto that entire side. Reuse the
proved root-exhaustion theorem and exact coordinate image of a cell arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.Cell
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (C : Cell N)
local notation "F" => modularFunctionFieldOver N ℂ

theorem powered_arc_through {R : RadialRegion} {e : ℕ}
    (hgeom : PowPullback.PowerGeometry R e C.R) (k : Fin R.N)
    (f : Place ℂ F → ℂ) (hread : ∀ P ∈ C.ζ.source, f P = R.q + C.ζ P ^ e)
    {P : Place ℂ F} (hP : P ∈ C.carrier) (hv : f P ∈ R.arcSet k) :
    ∃ a : Fin C.R.N, P ∈ C.arc a ∧ f '' C.arc a = R.arcSet k := by
  have he := hgeom.exponent_ne_zero
  have hs := (C.mem_carrier_iff_coordinate P).mp hP |>.1
  obtain ⟨_, _, _, _, _, lap, _, _, himg, _, hsep⟩ := hgeom
  rw [hread P hs] at hv
  obtain ⟨j, hj⟩ := PowPullback.exists_lap_of_pow_mem he himg hsep hv
  refine ⟨lap j k, (C.mem_arc_iff_coordinate _ P).mpr ⟨hs, hj⟩, ?_⟩
  rw [← himg j k, ← C.coordinate_arc_image (lap j k), image_image]
  exact image_congr fun Q hQ => hread Q ((C.mem_arc_iff_coordinate _ Q).mp hQ).1

end
end Dubon2026.SourceFunctionField.CellGeometry.Cell
