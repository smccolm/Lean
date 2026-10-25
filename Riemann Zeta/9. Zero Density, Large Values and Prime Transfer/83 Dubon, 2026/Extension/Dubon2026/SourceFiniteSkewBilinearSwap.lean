import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-! DUB-17/18 -> cover Abel converse -> third-kind reciprocity.
This is the existing finite skew-symmetry calculation from the original-curve
residue proof, isolated from the large actual-field expression. Its sole
consumer fixes the order and sign of the two actual period factors. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods

theorem finite_skew_bilinear_swap {E : Type*} (s : Finset E) (Q : E → E → ℤ)
    (a b : E → ℂ) (hskew : ∀ j ∈ s, ∀ l ∈ s, Q l j = -Q j l) :
    (∑ j ∈ s, ∑ l ∈ s, (Q j l : ℂ) * a j * b l) =
      -(∑ j ∈ s, ∑ l ∈ s, b j * (Q j l : ℂ) * a l) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hskew j hj l hl, Int.cast_neg]
  ring

end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
