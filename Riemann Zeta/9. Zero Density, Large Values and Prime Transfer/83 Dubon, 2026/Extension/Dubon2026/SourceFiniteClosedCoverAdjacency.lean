import Mathlib.Topology.Connected.Clopen

/-! DUB-17/18 -> cover dissection -> global adjacency.
This is the existing finite closed-cover connectivity proof with the original
curve parameter made explicit. The actual Kummer cover supplies connectedness,
compact carriers and pointwise intersection chains in the consumer. -/
namespace Dubon2026.SourceFunctionField.SheetCover
open Set

theorem finite_closed_cover_reachable {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {ι : Type*} [Finite ι] (carrier : ι → Set X) (adj : ι → ι → Prop)
    (hclosed : ∀ C, IsClosed (carrier C)) (hnonempty : ∀ C, (carrier C).Nonempty)
    (hcover : ∀ x : X, ∃ C, x ∈ (carrier C))
    (hinter : ∀ C C' (x : X), x ∈ (carrier C) → x ∈ (carrier C') →
      Relation.ReflTransGen adj C C') (C C' : ι) : Relation.ReflTransGen adj C C' := by
  classical
  let reach : Set ι := {D | Relation.ReflTransGen adj C D}
  let U : Set (X) := ⋃ D ∈ reach, (carrier D)
  let V : Set (X) := ⋃ D ∈ reachᶜ, (carrier D)
  have hUc : IsClosed U := (Set.toFinite reach).isClosed_biUnion fun D _ => hclosed D
  have hVc : IsClosed V := (Set.toFinite reachᶜ).isClosed_biUnion fun D _ => hclosed D
  have hdisj : ∀ x ∈ U, x ∉ V := by
    intro x hxU hxV
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
    obtain ⟨D', hD', hxD'⟩ := mem_iUnion₂.mp hxV
    exact hD' (hD.trans (hinter D D' x hxD hxD'))
  have hcov : ∀ x : X, x ∈ U ∨ x ∈ V := by
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
    obtain ⟨x, hx⟩ := hnonempty C
    exact ⟨x, mem_iUnion₂.mpr ⟨C, Relation.ReflTransGen.refl, hx⟩⟩
  have hUuniv : U = univ := IsClopen.eq_univ ⟨hUc, hUo⟩ hUne
  obtain ⟨x, hx⟩ := hnonempty C'
  have hxU : x ∈ U := hUuniv ▸ mem_univ x
  obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp hxU
  exact hD.trans (hinter D C' x hxD hx)


end Dubon2026.SourceFunctionField.SheetCover
