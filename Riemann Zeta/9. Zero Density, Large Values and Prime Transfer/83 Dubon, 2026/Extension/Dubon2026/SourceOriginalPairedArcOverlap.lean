import Dubon2026.SourceOriginalCellDissection
import Dubon2026.SourceOriginalCellBoundaryIntegrability
import Mathlib.Topology.Order.IntermediateValue

/-! DUB-17/18 -> raw reciprocity -> genuine shared-edge primitive jumps.
The source reversed-arc map covers the entire other arc by the intermediate
value theorem. Thus the actual paired arcs give the precise coordinate overlap
needed by the proved primitive-jump theorem, including both endpoints.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem Cell.reversed_arc_overlap (C C' : Cell N) (k : Fin C.R.N) (k' : Fin C'.R.N)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (C'.R.arcIcc k'))
    (ha : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ t ∈ C'.R.arcIcc k', C'.bdry t = C.bdry (ψ t)) :
    ∀ s ∈ C.R.arcIcc k, C.bdry s ∈ C'.ζ.source ∧ C'.ζ (C.bdry s) ∈ C'.R.K := by
  intro s hs
  have honto := intermediate_value_Icc' (C'.R.hmono Fin.castSucc_lt_succ).le hc
  rw [ha, hb] at honto
  obtain ⟨t, ht, he⟩ := honto hs
  rw [← he, ← hbd t ht]
  refine ⟨(C'.bdry_coordinates t).1, ?_⟩
  rw [(C'.bdry_coordinates t).2]
  exact C'.R.loop_mem_K t

theorem CellDissection.side_arcOf (𝒟 : CellDissection N) (q : 𝒟.ιE × Bool) :
    𝒟.side (𝒟.arcOf q).1 (𝒟.arcOf q).2 = q :=
  Function.surjInv_eq 𝒟.side_bij.surjective q

theorem CellDissection.paired_arc_overlap (𝒟 : CellDissection N) (e : 𝒟.ιE) :
    let p := 𝒟.arcOf (e, true)
    let n := 𝒟.arcOf (e, false)
    ∀ s ∈ (𝒟.cell p.1).R.arcIcc p.2,
      (𝒟.cell p.1).bdry s ∈ (𝒟.cell n.1).ζ.source ∧
        (𝒟.cell n.1).ζ ((𝒟.cell p.1).bdry s) ∈ (𝒟.cell n.1).R.K := by
  let p := 𝒟.arcOf (e, true)
  let n := 𝒟.arcOf (e, false)
  have hp : 𝒟.side p.1 p.2 = (e, true) := 𝒟.side_arcOf _
  have hn : 𝒟.side n.1 n.2 = (e, false) := 𝒟.side_arcOf _
  obtain ⟨ψ, _, hc, ha, hb, hbd⟩ := 𝒟.arc_rev p.1 p.2 n.1 n.2
    (by rw [hp, hn]) (by rw [hp]) (by rw [hn])
  exact (𝒟.cell p.1).reversed_arc_overlap (𝒟.cell n.1) p.2 n.2 ψ hc.continuousOn ha hb hbd

end
end Dubon2026.SourceFunctionField.CellGeometry
