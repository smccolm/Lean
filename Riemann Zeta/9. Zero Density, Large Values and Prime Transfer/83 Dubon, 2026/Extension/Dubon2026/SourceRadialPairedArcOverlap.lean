import Dubon2026.SourceRadialReversedArcImages
import Dubon2026.SourceRadialCellBoundaryCoordinates

/-! DUB-17/18 -> cover reciprocity -> constant primitive jumps.
The already proved equality of reversed radial arc images supplies both
coordinate overlaps, including the endpoints, for the actual dissection. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set
variable {X : Type*} [TopologicalSpace X]

theorem RadialCellDissection.paired_arc_overlap (D : RadialCellDissection X) (e : D.ιE) :
    let p := D.arcOf (e, true)
    let n := D.arcOf (e, false)
    ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
      (D.cell p.1).bdry s ∈ (D.cell n.1).ζ.source ∧
        (D.cell n.1).ζ ((D.cell p.1).bdry s) ∈ (D.cell n.1).R.K := by
  dsimp only
  let p := D.arcOf (e, true)
  let n := D.arcOf (e, false)
  have hp : D.side p.1 p.2 = (e, true) := D.side_arcOf _
  have hn : D.side n.1 n.2 = (e, false) := D.side_arcOf _
  obtain ⟨ψ, hanti, hc, ha, hb, hbd⟩ := D.arc_rev p.1 p.2 n.1 n.2
    (by rw [hp, hn]) (by rw [hp]) (by rw [hn])
  have he := RadialRegion.reversed_arc_images (D.cell p.1).R (D.cell n.1).R p.2 n.2
    (D.cell p.1).ζ.symm (D.cell n.1).ζ.symm ψ hanti hc.continuousOn ha hb hbd
  intro s hs
  have hm : (D.cell p.1).bdry s ∈ (D.cell n.1).ζ.symm '' (D.cell n.1).R.arcSet n.2 := by
    rw [he]
    exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  obtain ⟨z, ⟨t, _, rfl⟩, hz⟩ := hm
  rw [← hz]
  exact ⟨((D.cell n.1).bdry_coordinates t).1,
    by
      change (D.cell n.1).ζ ((D.cell n.1).bdry t) ∈ (D.cell n.1).R.K
      rw [((D.cell n.1).bdry_coordinates t).2]
      exact (D.cell n.1).R.loop_mem_K t⟩

end Dubon2026.SourceFunctionField.CellGeometry
