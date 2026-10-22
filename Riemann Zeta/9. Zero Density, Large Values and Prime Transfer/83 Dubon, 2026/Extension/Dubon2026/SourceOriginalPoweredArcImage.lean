import Dubon2026.SourceOriginalPoweredArcMatching

/-! DUB-17/18 -> original Abel-Jacobi -> the actual pairing involution.
Every powered original-cell arc maps injectively and onto a specific planar
side. This supplies the forward side assignment used with the proved unique
arc matching on the adjacent planar region.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.Cell
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (C : Cell N)
local notation "F" => modularFunctionFieldOver N ℂ

theorem powered_arc_image {R : RadialRegion} {e : ℕ}
    (hgeom : PowPullback.PowerGeometry R e C.R) (a : Fin C.R.N)
    (f : Place ℂ F → ℂ) (hread : ∀ P ∈ C.ζ.source, f P = R.q + C.ζ P ^ e) :
    ∃ k : Fin R.N, f '' C.arc a = R.arcSet k ∧ InjOn f (C.arc a) := by
  obtain ⟨_, _, _, _, _, lap, hbij, _, himg, hinj, _⟩ := hgeom
  obtain ⟨⟨j, k⟩, ha⟩ := hbij.2 a
  change lap j k = a at ha
  subst a
  have hcoord : f '' C.arc (lap j k) =
      (fun u : ℂ => R.q + u ^ e) '' C.R.arcSet (lap j k) := by
    rw [← C.coordinate_arc_image (lap j k), image_image]
    apply image_congr
    intro P hP
    exact hread P ((C.mem_arc_iff_coordinate (lap j k) P).mp hP).1
  refine ⟨k, hcoord.trans (himg j k), ?_⟩
  intro P hP Q hQ hPQ
  have hp := (C.mem_arc_iff_coordinate (lap j k) P).mp hP
  have hq := (C.mem_arc_iff_coordinate (lap j k) Q).mp hQ
  apply C.ζ.injOn hp.1 hq.1
  apply hinj j k hp.2 hq.2
  change R.q + C.ζ P ^ e = R.q + C.ζ Q ^ e
  rw [← hread P hp.1, ← hread Q hq.1]
  exact hPQ

end
end Dubon2026.SourceFunctionField.CellGeometry.Cell
