import Dubon2026.SourceCellWindowArcGeometry
import Dubon2026.SourceOriginalCellCoverConnectivity
import Dubon2026.SourceOriginalCellDissectionInteriors
import Dubon2026.SourceCellFiniteClosedSelection

/-! DUB-17/18 -> original Abel-Jacobi -> actual lifted arc matching.
Reuse radial loop injectivity and compact carriers. Every original-cell arc
is a nonempty connected compact image, its coordinate image is exact, and
its boundary index is unique. These facts apply uniformly to ordinary,
branched and pole cells; no separate powered-arc uniqueness proof is needed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

theorem RadialRegion.arcSet_subset_K (R : RadialRegion) (k : Fin R.N) : R.arcSet k ⊆ R.K := by
  rintro z ⟨t, _, rfl⟩
  exact R.loop_mem_K t

theorem RadialRegion.arcSet_nonempty (R : RadialRegion) (k : Fin R.N) : (R.arcSet k).Nonempty :=
  ⟨R.loop (R.φs k.castSucc), _, GridWindow.castSucc_mem_arcIcc R k, rfl⟩

theorem RadialRegion.arcSet_isPreconnected (R : RadialRegion) (k : Fin R.N) :
    IsPreconnected (R.arcSet k) :=
  isPreconnected_Icc.image R.loop R.continuous_loop.continuousOn

theorem RadialRegion.arcSet_not_mem_Kint (R : RadialRegion) (k : Fin R.N)
    {z : ℂ} (hz : z ∈ R.arcSet k) : z ∉ R.Kint := by
  obtain ⟨t, _, rfl⟩ := hz
  change ¬ ‖R.loop t - R.q‖ < R.r (Complex.arg (R.loop t - R.q))
  rw [R.norm_loop_sub_center, R.radius_arg_loop]
  exact lt_irrefl _

namespace Cell
variable {N : ℕ} [NeZero N] (C : Cell N)

theorem mem_arc_iff_coordinate (k : Fin C.R.N) (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
    P ∈ C.arc k ↔ P ∈ C.ζ.source ∧ C.ζ P ∈ C.R.arcSet k := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have ht := C.hKt (C.R.arcSet_subset_K k hz)
    exact ⟨C.ζ.map_target ht, by rwa [C.ζ.right_inv ht]⟩
  · rintro ⟨hP, hz⟩
    exact ⟨C.ζ P, hz, C.ζ.left_inv hP⟩

theorem arc_nonempty (k : Fin C.R.N) : (C.arc k).Nonempty :=
  (C.R.arcSet_nonempty k).image C.ζ.symm

theorem arc_isPreconnected (k : Fin C.R.N) : IsPreconnected (C.arc k) :=
  (C.R.arcSet_isPreconnected k).image C.ζ.symm
    (C.ζ.continuousOn_symm.mono ((C.R.arcSet_subset_K k).trans C.hKt))

theorem coordinate_arc_image (k : Fin C.R.N) : C.ζ '' C.arc k = C.R.arcSet k := by
  ext z
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ((C.mem_arc_iff_coordinate k P).mp hP).2
  · intro hz
    have ht := C.hKt (C.R.arcSet_subset_K k hz)
    exact ⟨C.ζ.symm z, ⟨z, hz, rfl⟩, C.ζ.right_inv ht⟩

theorem arc_index_injective {k k' : Fin C.R.N} (h : C.arc k = C.arc k') : k = k' := by
  apply GridWindow.arcSet_injective C.R
  rw [← C.coordinate_arc_image k, ← C.coordinate_arc_image k', h]

end Cell
end
end Dubon2026.SourceFunctionField.CellGeometry
