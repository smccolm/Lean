import Dubon2026.SourceOriginalCellDissection

/-! DUB-17/18 -> raw reciprocity -> constructing the actual cell dissection.
The source geometric cell family supplies a fixed-point-free orientation-
reversing involution of its actual boundary arcs. Positive arcs index geometric
edges. An explicit equivalence with edge/sign pairs proves the required side
bijection directly, without transporting the cell indices through `Fin`.
No existence of the geometric paired family is claimed by this data structure.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type*}

/-- The exact source pairing and reversed-arc data for an actual cell family. -/
structure CellPairing (cell : ι → Cell N) where
  /-- The paired oriented boundary arc. -/
  pair : (Σ C : ι, Fin (cell C).R.N) → (Σ C : ι, Fin (cell C).R.N)
  /-- Pairing twice recovers the original arc. -/
  involutive : Function.Involutive pair
  /-- The chosen orientation of each arc. -/
  orient : (Σ C : ι, Fin (cell C).R.N) → Bool
  /-- Paired arcs have opposite orientations. -/
  orient_pair : ∀ a, orient (pair a) = !orient a
  /-- The actual source C1 reversal of each positive arc. -/
  reverse : ∀ (a b : Σ C : ι, Fin (cell C).R.N), pair a = b → orient a = true →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell b.1).R.arcIcc b.2) ∧
      ContDiffOn ℝ 1 ψ ((cell b.1).R.arcIcc b.2) ∧
      ψ ((cell b.1).R.φs b.2.castSucc) = (cell a.1).R.φs a.2.succ ∧
      ψ ((cell b.1).R.φs b.2.succ) = (cell a.1).R.φs a.2.castSucc ∧
      ∀ t ∈ (cell b.1).R.arcIcc b.2, (cell b.1).bdry t = (cell a.1).bdry (ψ t)

namespace CellPairing
variable {cell : ι → Cell N} (P : CellPairing cell)

/-- Geometric edges indexed by their positively oriented actual arcs. -/
def Edge := {a : Σ C : ι, Fin (cell C).R.N // P.orient a = true}

instance [Fintype ι] : Fintype P.Edge := by
  classical
  unfold Edge
  infer_instance

theorem orient_pair_of_not {a : Σ C : ι, Fin (cell C).R.N} (h : P.orient a ≠ true) :
    P.orient (P.pair a) = true := by
  rw [P.orient_pair, Bool.eq_false_iff.mpr h]
  rfl

/-- The actual oriented arc as its positive geometric edge and orientation. -/
def side (a : Σ C : ι, Fin (cell C).R.N) : P.Edge × Bool :=
  if h : P.orient a = true then (⟨a, h⟩, true)
  else (⟨P.pair a, P.orient_pair_of_not h⟩, false)

/-- Exact equivalence between actual arcs and geometric edge/sign pairs. -/
def sideEquiv : (Σ C : ι, Fin (cell C).R.N) ≃ P.Edge × Bool where
  toFun := P.side
  invFun := fun q => if q.2 then q.1.1 else P.pair q.1.1
  left_inv := by
    intro a
    by_cases h : P.orient a = true
    · simp only [side, dif_pos h, if_true]
    · simp only [side, dif_neg h, Bool.false_eq_true, if_false]
      exact P.involutive a
  right_inv := by
    rintro ⟨e, b⟩
    cases b
    · have h : P.orient (P.pair e.1) ≠ true := by rw [P.orient_pair, e.2]; decide
      simp only [Bool.false_eq_true, if_false, side, dif_neg h]
      refine Prod.ext ?_ rfl
      exact Subtype.ext (P.involutive e.1)
    · simp only [if_true, side, dif_pos e.2]
      rfl

theorem side_bijective : Function.Bijective P.side := P.sideEquiv.bijective

end CellPairing
end
end Dubon2026.SourceFunctionField.CellGeometry
