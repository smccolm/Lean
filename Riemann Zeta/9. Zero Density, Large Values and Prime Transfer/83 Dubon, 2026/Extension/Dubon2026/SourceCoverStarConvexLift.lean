import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! DUB-17/18 -> cover raw reciprocity -> lifted original analytic cells.
The actual star-convex neighborhood of a base cell lifts through a covering.
Native simply-connected lifting and open-section lemmas supply an embedded
sheet through each chosen point of the actual fiber. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem exists_open_lift_of_starConvex (p : E → X) (hp : IsCoveringMap p)
    (e : OpenPartialHomeomorph X ℂ) {V : Set ℂ} (hV : IsOpen V)
    {q : ℂ} (hq : q ∈ V) (hc : StarConvex ℝ q V) (hVe : V ⊆ e.target)
    (w : E) (hw : p w = e.symm q) :
    ∃ s : C(V, E), s ⟨q, hq⟩ = w ∧
      (∀ z : V, p (s z) = e.symm z) ∧ IsOpenEmbedding s := by
  letI : ContractibleSpace V := hc.contractibleSpace ⟨q, hq⟩
  letI : LocPathConnectedSpace V := hV.locPathConnectedSpace
  let b : C(V, X) := ⟨fun z => e.symm z,
    (e.continuousOn_symm.mono hVe).comp_continuous continuous_subtype_val Subtype.prop⟩
  obtain ⟨s, hs, _⟩ := hp.existsUnique_continuousMap_lifts b ⟨q, hq⟩ w hw
  refine ⟨s, hs.1, fun z => congrFun hs.2 z, ?_⟩
  apply hp.isLocalHomeomorph.isOpenEmbedding_of_comp _ s.continuous
  rw [hs.2]
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨b.continuous, ?_, ?_⟩
  · intro z t h
    exact Subtype.ext (e.symm.injOn (hVe z.2) (hVe t.2) h)
  · intro U hU
    change IsOpen ((e.symm ∘ Subtype.val) '' U)
    rw [Set.image_comp]
    exact e.symm.isOpen_image_of_subset_source (hV.isOpenMap_subtype_val U hU)
      (fun z hz => hVe (by obtain ⟨t, _, rfl⟩ := hz; exact t.2))

end
end Dubon2026.SourceFunctionField.SheetCover
