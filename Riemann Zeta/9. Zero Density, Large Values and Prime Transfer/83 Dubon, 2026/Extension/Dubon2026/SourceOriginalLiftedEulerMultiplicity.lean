import Dubon2026.SourceOriginalCellPairingLiftVertices
import Dubon2026.SourceOriginalCellPairingVertices
import Mathlib.SetTheory.Cardinal.Finite

/-! DUB-17/18 -> cover Euler/cycle count -> exact finite counting transfer.
Every lifted cell and positive edge is indexed by its actual finite sheet set.
Together with the proved vertex multiplicity, native finite sigma cardinality
gives multiplication of the complete Euler expression by the cover degree. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.CellPairing
noncomputable section
variable {N : ℕ} [NeZero N] {ι : Type} [Fintype ι] {cell : ι → Cell N}
variable (P : CellPairing cell) (J : ι → Type) [∀ i, Fintype (J i)]

theorem lifted_euler_multiplicity {X : Type*} (f : (i : ι) → J i → ℂ → X) (d : ℕ)
    (hc : ∀ i, Nat.card (J i) = d)
    (hv : Nat.card (LiftedVertex (cell := cell) J f) = Nat.card (Vertex (cell := cell)) * d) :
    (Fintype.card (LiftedVertex (cell := cell) J f) : ℤ) -
        (Fintype.card (Σ e : P.Edge, J e.1.1) : ℤ) + (Fintype.card (Σ i : ι, J i) : ℤ) =
      (d : ℤ) * ((Fintype.card (Vertex (cell := cell)) : ℤ) -
        (Fintype.card P.Edge : ℤ) + (Fintype.card ι : ℤ)) := by
  have hc' (i : ι) : Fintype.card (J i) = d := by
    simpa only [Nat.card_eq_fintype_card] using hc i
  have hC : Fintype.card (Σ i : ι, J i) = Fintype.card ι * d := by
    rw [Fintype.card_sigma]
    simp only [hc', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hE : Fintype.card (Σ e : P.Edge, J e.1.1) = Fintype.card P.Edge * d := by
    rw [Fintype.card_sigma]
    simp only [hc', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hV : Fintype.card (LiftedVertex (cell := cell) J f) = Fintype.card (Vertex (cell := cell)) * d := by
    simpa only [Nat.card_eq_fintype_card] using hv
  rw [hC, hE, hV]
  push_cast
  ring

end
end Dubon2026.SourceFunctionField.CellGeometry.CellPairing
