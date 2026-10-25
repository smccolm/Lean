import Dubon2026.SourceOriginalCellPairing
import Mathlib.Logic.Equiv.Sum

/-! DUB-17/18 -> actual lifted dissection -> pairing involution.
Reuse the proved base arc/sign equivalence. A sheet equivalence for each
positive base edge swaps the two lifted sides by mutually inverse maps.
Conjugating this explicit swap gives an involution on the actual lifted arc
indices, with exactly the base pairing and opposite orientation. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type)

/-- Reindex actual lifted arcs by a base positive edge and its two sheet sets. -/
def liftedSignedEquiv :
    (Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) ≃
      Σ e : P.Edge, J (P.pair e.1).1 ⊕ J e.1.1 :=
  (Equiv.sigmaCongrLeft' (β := fun a => J a.1) P.sideEquiv).trans
    { toFun := by
        rintro ⟨⟨e, b⟩, j⟩
        cases b
        · exact ⟨e, Sum.inl j⟩
        · exact ⟨e, Sum.inr j⟩
      invFun := by
        rintro ⟨e, j | j⟩
        · exact ⟨(e, false), j⟩
        · exact ⟨(e, true), j⟩
      left_inv := by rintro ⟨⟨e, b⟩, j⟩; cases b <;> rfl
      right_inv := by rintro ⟨e, j | j⟩ <;> rfl }

/-- Swap the two actual sheet sets by a chosen equivalence and its inverse. -/
def liftedSheetSwap (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) :
    (Σ e : P.Edge, J (P.pair e.1).1 ⊕ J e.1.1) →
      Σ e : P.Edge, J (P.pair e.1).1 ⊕ J e.1.1
  | ⟨e, Sum.inl j⟩ => ⟨e, Sum.inr ((T e).symm j)⟩
  | ⟨e, Sum.inr j⟩ => ⟨e, Sum.inl (T e j)⟩

theorem liftedSheetSwap_involutive (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) :
    Function.Involutive (P.liftedSheetSwap J T) := by
  rintro ⟨e, j | j⟩ <;> simp [liftedSheetSwap]

/-- The pairing on the genuine lifted base-arc indices. -/
def liftedPair (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1 :=
  (P.liftedSignedEquiv J).symm (P.liftedSheetSwap J T (P.liftedSignedEquiv J a))

theorem liftedPair_involutive (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) :
    Function.Involutive (P.liftedPair J T) := by
  intro a
  unfold liftedPair
  rw [Equiv.apply_symm_apply, P.liftedSheetSwap_involutive J T ((P.liftedSignedEquiv J) a),
    Equiv.symm_apply_apply]

theorem liftedPair_base (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    (P.liftedPair J T a).1 = P.pair a.1 := by
  obtain ⟨⟨e, j | j⟩, rfl⟩ := (P.liftedSignedEquiv J).symm.surjective a
  · unfold liftedPair
    rw [Equiv.apply_symm_apply]
    change e.1 = P.pair (P.pair e.1)
    exact (P.involutive e.1).symm
  · unfold liftedPair
    rw [Equiv.apply_symm_apply]
    rfl

theorem liftedPair_orientation (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    P.orient (P.liftedPair J T a).1 = !P.orient a.1 := by
  rw [P.liftedPair_base, P.orient_pair]

theorem liftedSignedEquiv_apply_positive (a : Σ c : ι, Fin (cell c).R.N)
    (ha : P.orient a = true) (j : J a.1) :
    P.liftedSignedEquiv J ⟨a, j⟩ = ⟨⟨a, ha⟩, Sum.inr j⟩ :=
  (P.liftedSignedEquiv J).apply_symm_apply ⟨⟨a, ha⟩, Sum.inr j⟩

theorem liftedPair_positive (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a : Σ c : ι, Fin (cell c).R.N) (ha : P.orient a = true) (j : J a.1) :
    P.liftedPair J T ⟨a, j⟩ = ⟨P.pair a, T ⟨a, ha⟩ j⟩ := by
  unfold liftedPair
  rw [P.liftedSignedEquiv_apply_positive J a ha j]
  rfl

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
