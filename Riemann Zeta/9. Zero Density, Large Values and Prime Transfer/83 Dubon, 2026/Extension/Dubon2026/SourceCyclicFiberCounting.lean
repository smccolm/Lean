import Mathlib.Data.Multiset.Count
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! The finite-fiber counting step for the all-level actual cyclic-root
bijection. The quotient values and modular roots both fit in the composition
root multiset, whose degree is less than twice their common cardinality.
Transitivity is needed only for membership of quotient values, not for
invariance of all multiplicities. This shortens the archived FLT argument
while preserving the required multiplicities and original source contract.
The elliptic application must discharge every premise below. -/

namespace Dubon2026.SourceEllipticCyclicCount

/-- A transitive root set occupying over half the ambient multiset is exactly the equally sized quotient multiset. -/
theorem quotient_multiset_eq_of_transitive_support
    {α : Type*} [DecidableEq α] (R : Finset α) (M Q : Multiset α)
    (hM : M ≤ Q) (hR : R.val ≤ Q) (hcard : M.card = R.card)
    (hbound : Q.card < 2 * R.card)
    (horbit : ∀ x ∈ R, ∀ y ∈ R, x ∈ M ↔ y ∈ M) : M = R.val := by
  have hcover : R.val ≤ M := by
    apply (Multiset.le_iff_subset R.nodup).mpr
    intro x hx
    by_contra hxm
    have hmiss (y : α) (hy : y ∈ R) : y ∉ M :=
      fun hym => hxm ((horbit y hy x hx).mp hym)
    have hsum : M + R.val ≤ Q := by
      apply Multiset.le_iff_count.mpr
      intro y
      rw [Multiset.count_add]
      by_cases hy : y ∈ R
      · rw [Multiset.count_eq_zero.mpr (hmiss y hy), zero_add]
        exact Multiset.le_iff_count.mp hR y
      · rw [Multiset.count_eq_zero.mpr hy, add_zero]
        exact Multiset.le_iff_count.mp hM y
    have hn := Multiset.card_le_card hsum
    rw [Multiset.card_add, hcard] at hn
    change R.card + R.card ≤ Q.card at hn
    omega
  apply (Multiset.eq_of_le_of_card_le hcover ?_).symm
  exact hcard.le

end Dubon2026.SourceEllipticCyclicCount
