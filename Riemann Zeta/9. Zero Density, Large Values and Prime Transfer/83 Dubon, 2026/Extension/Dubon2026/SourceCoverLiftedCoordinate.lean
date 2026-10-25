import Dubon2026.SourceCoverStarConvexLift

/-! DUB-17/18 -> cover geometric reciprocity -> lifted cell coordinates.
Turn the proved open lift of a star-convex base chart into an actual open
partial homeomorphism on the cover, retaining the exact restriction formula. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem exists_coordinate_of_open_lift (p : E → X)
    (e : OpenPartialHomeomorph X ℂ) {V : Set ℂ} (hV : IsOpen V)
    {q : ℂ} (hq : q ∈ V) (hVe : V ⊆ e.target)
    (s : C(V, E)) (hs : IsOpenEmbedding s) (he : ∀ z : V, p (s z) = e.symm z) :
    ∃ ζ : OpenPartialHomeomorph E ℂ,
      ζ.source = Set.range s ∧ ζ.target = V ∧
      (∀ z : V, ζ (s z) = z) ∧
      (∀ z (hz : z ∈ V), ζ.symm z = s ⟨z, hz⟩) ∧
      (∀ w ∈ ζ.source, p w ∈ e.source ∧ ζ w = e (p w)) := by
  letI : Nonempty V := ⟨⟨q, hq⟩⟩
  let v := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → ℂ)
  let ζ := v.lift_openEmbedding hs
  have hsource : ζ.source = Set.range s := by
    change s '' v.source = Set.range s
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.image_univ]
  have htarget : ζ.target = V := by
    change v.target = V
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_val]
  have hforward (z : V) : ζ (s z) = z := v.lift_openEmbedding_apply hs
  refine ⟨ζ, hsource, htarget, hforward, ?_, ?_⟩
  · intro z hz
    have hm : s ⟨z, hz⟩ ∈ ζ.source := by rw [hsource]; exact ⟨⟨z, hz⟩, rfl⟩
    exact (congrArg ζ.symm (hforward ⟨z, hz⟩)).symm.trans (ζ.left_inv hm)
  · intro w hw
    rw [hsource] at hw
    obtain ⟨z, rfl⟩ := hw
    rw [he z]
    exact ⟨e.map_target (hVe z.2), (hforward z).trans (e.right_inv (hVe z.2)).symm⟩

end
end Dubon2026.SourceFunctionField.SheetCover
