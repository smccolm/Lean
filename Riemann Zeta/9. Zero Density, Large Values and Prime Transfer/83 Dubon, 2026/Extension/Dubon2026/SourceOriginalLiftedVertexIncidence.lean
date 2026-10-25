import Dubon2026.SourceOriginalCellPairingLiftVertices

/-! DUB-17/18 -> cover reciprocity -> incidence of every actual vertex.
Every vertex is an actual arc endpoint. The proved oriented endpoint law
identifies it with an endpoint of its actual geometric lifted edge. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type) {X : Type*} (f : (i : ι) → J i → ℂ → X)

theorem lifted_vertex_incident
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (hends : ∀ (e : P.Edge) (j : J e.1.1),
      liftedEndpoint J f ⟨P.pair e.1, T e j⟩ false = liftedEndpoint J f ⟨e.1, j⟩ true ∧
        liftedEndpoint J f ⟨P.pair e.1, T e j⟩ true = liftedEndpoint J f ⟨e.1, j⟩ false)
    (v : LiftedVertex (cell := cell) J f) :
    ∃ e : Σ e : P.Edge, J e.1.1, (P.liftedEnds J f e).1 = v ∨ (P.liftedEnds J f e).2 = v := by
  obtain ⟨v, ⟨⟨a, b⟩, rfl⟩⟩ := v
  have h := P.lifted_arc_endpoints J f T hends a
  refine ⟨(P.liftedSideEquiv J T a).1, ?_⟩
  cases b
  · cases hs : (P.liftedSideEquiv J T a).2
    · right; apply Subtype.ext
      simpa only [hs, Bool.false_eq_true, if_false] using h.1.symm
    · left; apply Subtype.ext
      simpa only [hs, if_true] using h.1.symm
  · cases hs : (P.liftedSideEquiv J T a).2
    · left; apply Subtype.ext
      simpa only [hs, Bool.false_eq_true, if_false] using h.2.symm
    · right; apply Subtype.ext
      simpa only [hs, if_true] using h.2.symm

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
