import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! # Bounded connecting-image cardinalities have unit growth factor

The original cyclic cohomology groups have two-periodic cardinalities.
The long exact sequence then gives a fixed multiplicative recurrence
for finite connecting-image orders. Their positive bounded orders force
the factor to be one. This avoids an additional naturality construction
for periodicity while proving DUB-17's required Herbrand multiplicativity
in the existing original cohomology model.
-/

namespace Dubon2026

/-- A positive bounded sequence of actual orders cannot have a nonunit fixed multiplicative growth factor. -/
theorem bounded_positive_cardinality_recurrence
    (d : ℕ → ℕ) (a b bound : ℕ) (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, d n ≤ bound) (hrec : ∀ n, d (n + 1) * a = d n * b) : a = b := by
  have hfin : (Set.range d).Finite := (Set.finite_Iic bound).subset (by
    rintro x ⟨n, rfl⟩
    exact hbound n)
  obtain ⟨lo, ⟨imin, rfl⟩, hmin⟩ :=
    (Set.range d).exists_min_image id hfin (Set.range_nonempty d)
  obtain ⟨hi, ⟨imax, rfl⟩, hmax⟩ :=
    (Set.range d).exists_max_image id hfin (Set.range_nonempty d)
  have hlo : d imin ≤ d (imin + 1) := hmin _ (Set.mem_range_self _)
  have hhi : d (imax + 1) ≤ d imax := hmax _ (Set.mem_range_self _)
  have hab : a ≤ b := by
    have h := Nat.mul_le_mul_right a hlo
    rw [hrec imin] at h
    nlinarith [hpos imin]
  have hba : b ≤ a := by
    have h := Nat.mul_le_mul_right a hhi
    rw [hrec imax] at h
    nlinarith [hpos imax]
  exact Nat.le_antisymm hab hba

end Dubon2026
