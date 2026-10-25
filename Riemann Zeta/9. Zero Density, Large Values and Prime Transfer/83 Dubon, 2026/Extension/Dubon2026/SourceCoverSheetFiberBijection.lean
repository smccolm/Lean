import Dubon2026.SourceCoverLiftedCoordinateFamily

/-! DUB-17/18 -> lifted arc pairing involution -> actual endpoint fibers.
The constructed disjoint exhaustive sheets identify their index set bijectively
with every actual fiber in their common coordinate domain. Neighboring-sheet
transport can therefore use inverse equivalences, rather than new choices. -/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Topology
variable {E X J : Type*} [TopologicalSpace E] [TopologicalSpace X]

theorem sheet_fiber_bijective (p : E → X) (e : OpenPartialHomeomorph X ℂ)
    {V : Set ℂ} (ζ : J → OpenPartialHomeomorph E ℂ)
    (ht : ∀ i, V ⊆ (ζ i).target)
    (hr : ∀ i z, z ∈ V → p ((ζ i).symm z) = e.symm z)
    (hd : Pairwise fun i j => Disjoint (ζ i).source (ζ j).source)
    (hx : ∀ w z, z ∈ V → p w = e.symm z → ∃ i, (ζ i).symm z = w)
    (z : ℂ) (hz : z ∈ V) :
    Function.Bijective (fun i : J => (⟨(ζ i).symm z, hr i z hz⟩ : p ⁻¹' {e.symm z})) := by
  constructor
  · intro i j hij
    by_contra hne
    have hi : (ζ i).symm z ∈ (ζ i).source := (ζ i).map_target (ht i hz)
    have hj : (ζ j).symm z ∈ (ζ j).source := (ζ j).map_target (ht j hz)
    have he : (ζ i).symm z = (ζ j).symm z := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hd hne) hi (he.symm ▸ hj)
  · intro w
    obtain ⟨i, hi⟩ := hx w.1 z hz w.2
    exact ⟨i, Subtype.ext hi⟩

end
end Dubon2026.SourceFunctionField.SheetCover
