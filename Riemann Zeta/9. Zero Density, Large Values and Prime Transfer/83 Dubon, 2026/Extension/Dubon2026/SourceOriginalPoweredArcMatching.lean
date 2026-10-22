import Dubon2026.SourceCellConnectedPowerArc
import Dubon2026.SourceOriginalDisjointArcUniqueness

/-! DUB-17/18 -> original Abel-Jacobi -> original branch/pole arc matching.
Transport the connected power-arc result through an actual original-place
coordinate. The actual evaluation power formula supplies the forward map;
coordinate injectivity and exhaustive lap geometry identify the complete arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.Cell
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] (C : Cell N)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_powered_arc_over {R : RadialRegion} {e : ℕ}
    (hgeom : PowPullback.PowerGeometry R e C.R) (k : Fin R.N)
    (f : Place ℂ F → ℂ) (hread : ∀ P ∈ C.ζ.source, f P = R.q + C.ζ P ^ e)
    {L : Set (Place ℂ F)} (hL : IsPreconnected L) (hne : L.Nonempty)
    (hcarrier : L ⊆ C.carrier) (hover : ∀ P ∈ L, f P ∈ R.arcSet k)
    (honto : R.arcSet k ⊆ f '' L) :
    ∃ a : Fin C.R.N, L = C.arc a ∧ InjOn f (C.arc a) ∧ f '' C.arc a = R.arcSet k := by
  have hsrc : L ⊆ C.ζ.source := fun P hP => ((C.mem_carrier_iff_coordinate P).mp (hcarrier hP)).1
  have hc : IsPreconnected (C.ζ '' L) := hL.image C.ζ (C.ζ.continuousOn.mono hsrc)
  have hv : ∀ u ∈ C.ζ '' L, R.q + u ^ e ∈ R.arcSet k := by
    rintro _ ⟨P, hP, rfl⟩
    rw [← hread P (hsrc hP)]
    exact hover P hP
  have ho : R.arcSet k ⊆ (fun u : ℂ => R.q + u ^ e) '' (C.ζ '' L) := by
    intro z hz
    obtain ⟨P, hP, hPz⟩ := honto hz
    exact ⟨C.ζ P, ⟨P, hP, rfl⟩, (hread P (hsrc hP)).symm.trans hPz⟩
  obtain ⟨a, ha, hi, himg⟩ := hgeom.exists_arc_of_connected_image k hc (hne.image C.ζ) hv ho
  have heq : L = C.arc a := by
    ext P
    constructor
    · intro hP
      apply (C.mem_arc_iff_coordinate a P).mpr
      exact ⟨hsrc hP, ha ▸ mem_image_of_mem C.ζ hP⟩
    · intro hP
      have hp := (C.mem_arc_iff_coordinate a P).mp hP
      obtain ⟨Q, hQ, hQP⟩ := ha.symm ▸ hp.2
      have he := C.ζ.injOn (hsrc hQ) hp.1 hQP
      exact he ▸ hQ
  have hf : InjOn f (C.arc a) := by
    intro P hP Q hQ hPQ
    have hp := (C.mem_arc_iff_coordinate a P).mp hP
    have hq := (C.mem_arc_iff_coordinate a Q).mp hQ
    apply C.ζ.injOn hp.1 hq.1
    apply hi hp.2 hq.2
    change R.q + C.ζ P ^ e = R.q + C.ζ Q ^ e
    rw [← hread P hp.1, ← hread Q hq.1]
    exact hPQ
  refine ⟨a, heq, hf, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    exact hover P (heq.symm ▸ hP)
  · intro z hz
    obtain ⟨u, hu, huz⟩ := himg.symm ▸ hz
    have ht := C.hKt (C.R.arcSet_subset_K a hu)
    refine ⟨C.ζ.symm u, ⟨u, hu, rfl⟩, ?_⟩
    rw [hread _ (C.ζ.map_target ht), C.ζ.right_inv ht]
    exact huz

end
end Dubon2026.SourceFunctionField.CellGeometry.Cell
