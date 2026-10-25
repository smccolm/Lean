import Dubon2026.SourceOriginalCellArcGeometry
import Mathlib.Topology.Order.IntermediateValue

/-! DUB-17/18 -> cover reciprocity -> lifted pointwise intersection chains.
The original C1 arc reversal has both endpoints and is onto by the native
intermediate value theorem. This gives equality of the full lifted arc images,
which is needed to transport a common cover point through each base step. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set

theorem RadialRegion.reversed_arc_images {X : Type*} (R S : RadialRegion)
    (k : Fin R.N) (l : Fin S.N) (f g : ℂ → X) (ψ : ℝ → ℝ)
    (hanti : StrictAntiOn ψ (S.arcIcc l)) (hc : ContinuousOn ψ (S.arcIcc l))
    (ha : ψ (S.φs l.castSucc) = R.φs k.succ)
    (hb : ψ (S.φs l.succ) = R.φs k.castSucc)
    (he : ∀ t ∈ S.arcIcc l, g (S.loop t) = f (R.loop (ψ t))) :
    g '' S.arcSet l = f '' R.arcSet k := by
  have honto := intermediate_value_Icc' (S.hmono Fin.castSucc_lt_succ).le hc
  rw [ha, hb] at honto
  apply Set.Subset.antisymm
  · rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    have hleft : S.φs l.castSucc ∈ S.arcIcc l :=
      ⟨le_rfl, (S.hmono Fin.castSucc_lt_succ).le⟩
    have hright : S.φs l.succ ∈ S.arcIcc l :=
      ⟨(S.hmono Fin.castSucc_lt_succ).le, le_rfl⟩
    have hψ : ψ t ∈ R.arcIcc k := by
      constructor
      · rw [← hb]; exact hanti.antitoneOn ht hright ht.2
      · rw [← ha]; exact hanti.antitoneOn hleft ht ht.1
    exact ⟨R.loop (ψ t), ⟨ψ t, hψ, rfl⟩, (he t ht).symm⟩
  · rintro x ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨t, ht, hts⟩ := honto hs
    exact ⟨S.loop t, ⟨t, ht, rfl⟩, (he t ht).trans (congrArg (fun u => f (R.loop u)) hts)⟩

end Dubon2026.SourceFunctionField.CellGeometry
