import Dubon2026.SourceOriginalAnalyticCells
import Dubon2026.SourceOriginalComplexConnected
import Mathlib.Topology.Connected.Clopen

/-! DUB-17/18 -> raw reciprocity -> construction of the source dissection.
The actual original curve is already proved connected. A finite cell cover
whose intersecting carriers are connected by the supplied adjacency chains
therefore has globally connected adjacency. This discharges the `conn` field
when constructing the dissection from actual paired cells; no connectivity
premise is added. Finite closed unions and native clopen connectedness suffice.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.carrier_isClosed (C : Cell N) : IsClosed C.carrier := by
  letI := OriginalChart.place_t2Space N
  exact C.carrier_isCompact.isClosed

theorem Cell.carrier_nonempty (C : Cell N) : C.carrier.Nonempty := by
  refine ⟨C.ζ.symm C.R.q, C.R.q, ?_, rfl⟩
  change ‖C.R.q - C.R.q‖ ≤ C.R.r (Complex.arg (C.R.q - C.R.q))
  rw [sub_self, norm_zero]
  exact (C.R.hpos _).le

theorem cell_cover_reachable {ι : Type*} [Finite ι] (cell : ι → Cell N) (adj : ι → ι → Prop)
    (hcover : ∀ x : Place ℂ F, ∃ C, x ∈ (cell C).carrier)
    (hinter : ∀ C C' (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
      Relation.ReflTransGen adj C C') (C C' : ι) : Relation.ReflTransGen adj C C' := by
  classical
  letI := OriginalChart.place_connectedSpace N
  let reach : Set ι := {D | Relation.ReflTransGen adj C D}
  let U : Set (Place ℂ F) := ⋃ D ∈ reach, (cell D).carrier
  let V : Set (Place ℂ F) := ⋃ D ∈ reachᶜ, (cell D).carrier
  have hUc : IsClosed U := (Set.toFinite reach).isClosed_biUnion fun D _ => (cell D).carrier_isClosed
  have hVc : IsClosed V := (Set.toFinite reachᶜ).isClosed_biUnion fun D _ => (cell D).carrier_isClosed
  have hdisj : ∀ x ∈ U, x ∉ V := by
    intro x hxU hxV
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
    obtain ⟨D', hD', hxD'⟩ := mem_iUnion₂.mp hxV
    exact hD' (hD.trans (hinter D D' x hxD hxD'))
  have hcov : ∀ x : Place ℂ F, x ∈ U ∨ x ∈ V := by
    intro x
    obtain ⟨D, hxD⟩ := hcover x
    by_cases hD : D ∈ reach
    · exact Or.inl (mem_iUnion₂.mpr ⟨D, hD, hxD⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨D, hD, hxD⟩)
  have hcompl : Uᶜ = V := by
    ext x
    exact ⟨fun hx => (hcov x).resolve_left hx, fun hx hxU => hdisj x hxU hx⟩
  have hUo : IsOpen U := by
    rw [← isClosed_compl_iff, hcompl]
    exact hVc
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := (cell C).carrier_nonempty
    exact ⟨x, mem_iUnion₂.mpr ⟨C, Relation.ReflTransGen.refl, hx⟩⟩
  have hUuniv : U = univ := IsClopen.eq_univ ⟨hUc, hUo⟩ hUne
  obtain ⟨x, hx⟩ := (cell C').carrier_nonempty
  have hxU : x ∈ U := hUuniv ▸ mem_univ x
  obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
  exact hD.trans (hinter D C' x hxD hx)

end
end Dubon2026.SourceFunctionField.CellGeometry
