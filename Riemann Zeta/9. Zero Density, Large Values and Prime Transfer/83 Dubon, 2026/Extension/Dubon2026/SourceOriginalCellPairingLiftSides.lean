import Dubon2026.SourceOriginalCellPairingLiftIndices

/-! DUB-17/18 -> actual cover dissection -> finite edge/sign indexing.
The invertible sheet transport identifies both sides with the sheet of the
positive base arc. Thus every actual lifted arc has exactly one edge and sign. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type)

/-- Exact lifted arc to geometric lifted edge/sign equivalence. -/
def liftedSideEquiv (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) :
    (Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) ≃ (Σ e : P.Edge, J e.1.1) × Bool :=
  (P.liftedSignedEquiv J).trans
    { toFun := by
        rintro ⟨e, j | j⟩
        · exact (⟨e, (T e).symm j⟩, false)
        · exact (⟨e, j⟩, true)
      invFun := by
        rintro ⟨⟨e, j⟩, b⟩
        cases b
        · exact ⟨e, Sum.inl (T e j)⟩
        · exact ⟨e, Sum.inr j⟩
      left_inv := by rintro ⟨e, j | j⟩ <;> simp
      right_inv := by rintro ⟨⟨e, j⟩, b⟩; cases b <;> simp }

theorem liftedSideEquiv_symm_true
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) (e : P.Edge) (j : J e.1.1) :
    (P.liftedSideEquiv J T).symm (⟨e, j⟩, true) = ⟨e.1, j⟩ := rfl

theorem liftedSideEquiv_symm_false
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) (e : P.Edge) (j : J e.1.1) :
    (P.liftedSideEquiv J T).symm (⟨e, j⟩, false) = ⟨P.pair e.1, T e j⟩ := rfl

theorem liftedSideEquiv_pair
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    P.liftedSideEquiv J T (P.liftedPair J T a) =
      ((P.liftedSideEquiv J T a).1, !(P.liftedSideEquiv J T a).2) := by
  obtain ⟨⟨⟨e, j⟩, b⟩, rfl⟩ := (P.liftedSideEquiv J T).symm.surjective a
  rw [Equiv.apply_symm_apply]
  cases b
  · rw [P.liftedSideEquiv_symm_false]
    have h := P.liftedPair_involutive J T (⟨e.1, j⟩)
    rw [P.liftedPair_positive J T e.1 e.2 j] at h
    change P.liftedPair J T ⟨P.pair e.1, T e j⟩ = ⟨e.1, j⟩ at h
    rw [h]
    exact (P.liftedSideEquiv J T).apply_symm_apply (⟨e, j⟩, true)
  · rw [P.liftedSideEquiv_symm_true, P.liftedPair_positive J T e.1 e.2 j]
    exact (P.liftedSideEquiv J T).apply_symm_apply (⟨e, j⟩, false)

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
