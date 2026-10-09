import Dubon2026.GramSpanCompletion

/-! # Density of an original family in its literal closed span -/

namespace Dubon2026

noncomputable section

/-- An original family whose ambient closed span is a given subspace remains dense in that actual subspace with its inherited topology. -/
theorem closedSpan_subtype_family_dense {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (S : Submodule ℂ E) (u : ι → S)
    (h : (Submodule.span ℂ (Set.range (fun i => (u i).val))).topologicalClosure = S) :
    (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  change x ∈ closure (Submodule.span ℂ (Set.range u) : Set S)
  rw [(Topology.IsInducing.subtypeVal (t := (S : Set E))).closure_eq_preimage_closure_image]
  have he : Subtype.val '' (Submodule.span ℂ (Set.range u) : Set S) =
      (Submodule.span ℂ (Set.range (fun i => (u i).val)) : Set E) := by
    change (Submodule.map S.subtype (Submodule.span ℂ (Set.range u)) : Set E) = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hx : x.val ∈ closure (Submodule.span ℂ (Set.range (fun i => (u i).val)) : Set E) := by
    change x.val ∈ (Submodule.span ℂ (Set.range (fun i => (u i).val))).topologicalClosure
    rw [h]
    exact x.property
  exact (congrArg (fun s : Set E => x.val ∈ closure s) he).mpr hx

end
end Dubon2026
