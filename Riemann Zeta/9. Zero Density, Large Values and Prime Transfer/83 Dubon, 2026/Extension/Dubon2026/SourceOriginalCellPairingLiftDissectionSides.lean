import Dubon2026.SourceOriginalCellPairingLiftSides

/-! DUB-17/18 -> actual cover dissection -> source-format sides and reversal.
Reindex lifted arcs by their lifted cell, then retain the exact edge/sign
bijection. Equal opposite edge labels recover the actual paired arcs and
the complete C1 reversal already constructed for their positive base edge. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type} {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type)

/-- Rearrange actual lifted-arc indices into lifted-cell/arc indices. -/
def liftedArcReindex :
    (Σ c : (Σ i : ι, J i), Fin (cell c.1).R.N) ≃
      (Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1) where
  toFun := fun ⟨⟨i, j⟩, k⟩ => ⟨⟨i, k⟩, j⟩
  invFun := fun ⟨⟨i, k⟩, j⟩ => ⟨⟨i, j⟩, k⟩
  left_inv := by rintro ⟨⟨i, j⟩, k⟩; rfl
  right_inv := by rintro ⟨⟨i, k⟩, j⟩; rfl

/-- The source-format lifted-cell/arc to edge/sign bijection. -/
def liftedCellSideEquiv (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1) :
    (Σ c : (Σ i : ι, J i), Fin (cell c.1).R.N) ≃ (Σ e : P.Edge, J e.1.1) × Bool :=
  (liftedArcReindex (cell := cell) J).trans (P.liftedSideEquiv J T)

theorem lifted_pair_of_same_edge
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (a b : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1)
    (he : (P.liftedSideEquiv J T a).1 = (P.liftedSideEquiv J T b).1)
    (ha : (P.liftedSideEquiv J T a).2 = true) (hb : (P.liftedSideEquiv J T b).2 = false) :
    P.liftedPair J T a = b := by
  apply (P.liftedSideEquiv J T).injective
  rw [P.liftedSideEquiv_pair]
  exact Prod.ext he (by rw [ha, hb]; rfl)

theorem lifted_reversed_side_arcs {X : Type*} (f : (i : ι) → J i → ℂ → X)
    (T : (e : P.Edge) → J e.1.1 ≃ J (P.pair e.1).1)
    (hrev : ∀ e : P.Edge, ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
      ContDiffOn ℝ 1 ψ ((cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2) ∧
      ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.castSucc) = (cell e.1.1).R.φs e.1.2.succ ∧
      ψ ((cell (P.pair e.1).1).R.φs (P.pair e.1).2.succ) = (cell e.1.1).R.φs e.1.2.castSucc ∧
      ∀ j t, t ∈ (cell (P.pair e.1).1).R.arcIcc (P.pair e.1).2 →
        f (P.pair e.1).1 (T e j) ((cell (P.pair e.1).1).R.loop t) =
          f e.1.1 j ((cell e.1.1).R.loop (ψ t)))
    (a b : Σ a : (Σ c : ι, Fin (cell c).R.N), J a.1)
    (he : (P.liftedSideEquiv J T a).1 = (P.liftedSideEquiv J T b).1)
    (ha : (P.liftedSideEquiv J T a).2 = true) (hb : (P.liftedSideEquiv J T b).2 = false) :
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell b.1.1).R.arcIcc b.1.2) ∧
      ContDiffOn ℝ 1 ψ ((cell b.1.1).R.arcIcc b.1.2) ∧
      ψ ((cell b.1.1).R.φs b.1.2.castSucc) = (cell a.1.1).R.φs a.1.2.succ ∧
      ψ ((cell b.1.1).R.φs b.1.2.succ) = (cell a.1.1).R.φs a.1.2.castSucc ∧
      ∀ t ∈ (cell b.1.1).R.arcIcc b.1.2,
        f b.1.1 b.2 ((cell b.1.1).R.loop t) = f a.1.1 a.2 ((cell a.1.1).R.loop (ψ t)) := by
  have hpair := P.lifted_pair_of_same_edge J T a b he ha hb
  subst b
  obtain ⟨⟨⟨e, j⟩, s⟩, rfl⟩ := (P.liftedSideEquiv J T).symm.surjective a
  rw [Equiv.apply_symm_apply] at ha
  change s = true at ha
  subst s
  rw [P.liftedSideEquiv_symm_true, P.liftedPair_positive J T e.1 e.2 j]
  obtain ⟨ψ, hanti, hc, hl, hr, hpoint⟩ := hrev e
  exact ⟨ψ, hanti, hc, hl, hr, hpoint j⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
