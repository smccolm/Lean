import Dubon2026.ZModAdditionCarry

/-! # Exact addition-carry sums for every original finite cyclic step -/

namespace Dubon2026

open scoped BigOperators

/-- The actual carries along repeated addition telescope to the exact
canonical final representative, for any step and any number of terms. -/
theorem zmodAdditionCarry_sum_balance {n : ℕ} [NeZero n] (a : ZMod n) (N : ℕ) :
    (N • a).val + n * (∑ i ∈ Finset.range N, zmodAdditionCarry (i • a) a) =
      N * a.val := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [succ_nsmul, Finset.sum_range_succ]
    have h := zmodAdditionCarry_balance (N • a) a
    nlinarith

/-- Along an actual closed cyclic period the original carry sum is
determined exactly by the step's canonical representative. -/
theorem zmodAdditionCarry_sum_period {n : ℕ} [NeZero n] (a : ZMod n)
    (N : ℕ) (hN : N • a = 0) :
    n * (∑ i ∈ Finset.range N, zmodAdditionCarry (i • a) a) = N * a.val := by
  have h := zmodAdditionCarry_sum_balance a N
  simpa only [hN, ZMod.val_zero, zero_add] using h

end Dubon2026
