import Dubon2026.SourceOriginalCellPairing

/-! DUB-17/18 -> raw reciprocity -> dissection side and reversal fields.
The explicit arc/edge equivalence proves pairing preserves the geometric edge
and reverses its orientation. Thus equal positive/negative edge labels recover
the actual paired arcs and their source C1 boundary reparameterization.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type*} {cell : ι → Cell N} (P : CellPairing cell)

theorem side_snd (a : Σ C : ι, Fin (cell C).R.N) : (P.side a).2 = P.orient a := by
  unfold side
  split
  · next h => exact h.symm
  · next h => exact (Bool.eq_false_iff.mpr h).symm

theorem side_pair (a : Σ C : ι, Fin (cell C).R.N) :
    P.side (P.pair a) = ((P.side a).1, !(P.side a).2) := by
  by_cases h : P.orient a = true
  · have hn : P.orient (P.pair a) ≠ true := by rw [P.orient_pair, h]; decide
    simp only [side, dif_neg hn, dif_pos h, Bool.not_true]
    refine Prod.ext ?_ rfl
    exact Subtype.ext (P.involutive a)
  · have hp := P.orient_pair_of_not h
    simp only [side, dif_pos hp, dif_neg h, Bool.not_false]

theorem pair_eq_of_same_edge (a b : Σ C : ι, Fin (cell C).R.N)
    (he : (P.side a).1 = (P.side b).1) (ha : (P.side a).2 = true) (hb : (P.side b).2 = false) :
    P.pair a = b := by
  apply P.side_bijective.injective
  rw [P.side_pair]
  exact Prod.ext he (by rw [ha, hb]; rfl)

theorem reversed_side_arcs (a b : Σ C : ι, Fin (cell C).R.N)
    (he : (P.side a).1 = (P.side b).1) (ha : (P.side a).2 = true) (hb : (P.side b).2 = false) :
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell b.1).R.arcIcc b.2) ∧
      ContDiffOn ℝ 1 ψ ((cell b.1).R.arcIcc b.2) ∧
      ψ ((cell b.1).R.φs b.2.castSucc) = (cell a.1).R.φs a.2.succ ∧
      ψ ((cell b.1).R.φs b.2.succ) = (cell a.1).R.φs a.2.castSucc ∧
      ∀ t ∈ (cell b.1).R.arcIcc b.2, (cell b.1).bdry t = (cell a.1).bdry (ψ t) := by
  apply P.reverse a b (P.pair_eq_of_same_edge a b he ha hb)
  rwa [P.side_snd] at ha

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
