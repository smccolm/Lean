import Dubon2026.SourceOriginalCellPairingLiftSides

/-! DUB-17/18 -> actual cover dissection -> genuine finite vertices.
Vertices are the literal range of all lifted arc endpoints. The actual C1
reversal gives the oriented endpoint law; the range inclusion is injective.
This adapts the proved original-cell vertex construction to the cover sheets. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
open Set
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type) {X : Type*} (f : (i : ι) → J i → ℂ → X)

/-- The actual endpoint of the specified lifted oriented arc. -/
def liftedEndpoint (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) (b : Bool) : X :=
  f a.1.1 a.2 ((cell a.1.1).R.loop
    (if b then (cell a.1.1).R.φs a.1.2.succ else (cell a.1.1).R.φs a.1.2.castSucc))

/-- Literal finite range of the actual lifted arc endpoints. -/
def LiftedVertex := Set.range (fun q : (Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) × Bool =>
  liftedEndpoint J f q.1 q.2)

instance [Fintype ι] [∀ i, Fintype (J i)] : Fintype (LiftedVertex (cell := cell) J f) :=
  (Set.finite_range _).fintype

/-- An actual lifted endpoint as an element of the actual vertex set. -/
def liftedEndpointVertex (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) (b : Bool) :
    LiftedVertex (cell := cell) J f := ⟨liftedEndpoint J f a b, ⟨(a, b), rfl⟩⟩

/-- The ordered actual endpoints of a lifted positively oriented edge. -/
def liftedEnds (e : Σ e : P.Edge, J e.1.1) :
    LiftedVertex (cell := cell) J f × LiftedVertex (cell := cell) J f :=
  (liftedEndpointVertex J f ⟨e.1.1, e.2⟩ false, liftedEndpointVertex J f ⟨e.1.1, e.2⟩ true)

theorem lifted_endpoint_reversal
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) (e : P.Edge) (j : J e.1.1)
    (ψ : ℝ → ℝ)
    (hl : ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.castSucc) = (cell e.1.1).R.φs e.1.2.succ)
    (hr : ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.succ) = (cell e.1.1).R.φs e.1.2.castSucc)
    (he : ∀ t ∈ (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2,
      f (P.pair e.1).1 (T e j) ((cell (P.pair e.1).1).R.loop t) =
        f e.1.1 j ((cell e.1.1).R.loop (ψ t))) :
    liftedEndpoint J f ⟨P.pair e.1, T e j⟩ false = liftedEndpoint J f ⟨e.1, j⟩ true ∧
      liftedEndpoint J f ⟨P.pair e.1, T e j⟩ true = liftedEndpoint J f ⟨e.1, j⟩ false := by
  have hleft : (cell (P.pair e.1).1).R.φs (P.pair e.1).2.castSucc ∈
      (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 :=
    ⟨le_rfl, ((cell (P.pair e.1).1).R.hmono Fin.castSucc_lt_succ).le⟩
  have hright : (cell (P.pair e.1).1).R.φs (P.pair e.1).2.succ ∈
      (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 :=
    ⟨((cell (P.pair e.1).1).R.hmono Fin.castSucc_lt_succ).le, le_rfl⟩
  constructor
  · simp only [liftedEndpoint, Bool.false_eq_true, if_false, if_true]
    rw [he _ hleft, hl]
  · simp only [liftedEndpoint, Bool.false_eq_true, if_false, if_true]
    rw [he _ hright, hr]

theorem lifted_arc_endpoints
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (hends : ∀ (e : P.Edge) (j : J e.1.1),
      liftedEndpoint J f ⟨P.pair e.1, T e j⟩ false = liftedEndpoint J f ⟨e.1, j⟩ true ∧
        liftedEndpoint J f ⟨P.pair e.1, T e j⟩ true = liftedEndpoint J f ⟨e.1, j⟩ false)
    (a : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) :
    liftedEndpoint J f a false =
      (if (P.liftedSideEquiv J T a).2 then (P.liftedEnds J f (P.liftedSideEquiv J T a).1).1
        else (P.liftedEnds J f (P.liftedSideEquiv J T a).1).2).1 ∧
    liftedEndpoint J f a true =
      (if (P.liftedSideEquiv J T a).2 then (P.liftedEnds J f (P.liftedSideEquiv J T a).1).2
        else (P.liftedEnds J f (P.liftedSideEquiv J T a).1).1).1 := by
  obtain ⟨⟨⟨e, j⟩, b⟩, rfl⟩ := (P.liftedSideEquiv J T).symm.surjective a
  rw [Equiv.apply_symm_apply]
  cases b
  · rw [P.liftedSideEquiv_symm_false]
    exact hends e j
  · rw [P.liftedSideEquiv_symm_true]
    exact ⟨rfl, rfl⟩

theorem lifted_vertex_injective :
    Function.Injective (Subtype.val : LiftedVertex (cell := cell) J f → X) := Subtype.val_injective

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
