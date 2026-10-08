import Dubon2026.HigherPoleCancellation

/-! # Nonvanishing at one from genuine entire symmetric continuations -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- A hypothetical higher symmetric zero at one identifies the actual entire pole-cancelled
function with the genuine nonnegative augmented tensor Dirichlet series in a far half-plane. -/
theorem higherSymmetricPoleCancellation_eq_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n)
      {s | (n : ℝ) + 1 < s.re}) {r : ℕ} (hr : 0 < r) (hz : H r 1 = 0)
    {s : ℂ} (hs : ((2 * r + (r + 2) ^ 2 + 1 : ℕ) : ℝ) + 1 < s.re) :
    higherSymmetricPoleCancellation Q H r s = LSeries (primitiveHigherAugmentedCoefficient f r) s := by
  have hs1 : 1 < s.re := by
    push_cast at hs
    nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg ((r : ℝ) + 2)]
  have hM (n : ℕ) (hn : 0 < n) (hnr : n ≤ 2 * r) :
      H n s = primitiveSymmetricLFunction f n s := by
    apply hmatch n hn
    have hnrR : (n : ℝ) ≤ 2 * r := by exact_mod_cast hnr
    change (n : ℝ) + 1 < s.re
    push_cast at hs
    nlinarith [sq_nonneg ((r : ℝ) + 2)]
  have hE : (∏ t ∈ Finset.range r, H (2 * (t + 1)) s) =
      ∏ t ∈ Finset.range r, primitiveSymmetricLFunction f (2 * (t + 1)) s := by
    apply Finset.prod_congr rfl
    intro t ht
    exact hM _ (by omega) (by have := Finset.mem_range.mp ht; omega)
  rw [higherSymmetricPoleCancellation_eq Q H r hz (by intro he; simp [he] at hs1),
    hM r hr (by omega), hE, primitiveHigherAugmentedCoefficient_LSeries f hk r hs,
    Finset.prod_range_succ' (fun t => primitiveSymmetricLFunction f (2 * t) s),
    Nat.mul_zero, primitiveSymmetric_zero_eq_principal f hk hs1]
  ring

/-- Entire positive-order continuations of the actual symmetric Euler products force every
positive symmetric function to be nonzero at one. The theorem consumes actual coefficient
positivity and the actual principal trivial zero, not a nonvanishing hypothesis. -/
theorem primitive_symmetric_one_ne_zero_of_entire_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n)
      {s | (n : ℝ) + 1 < s.re}) {r : ℕ} (hr : 0 < r) : H r 1 ≠ 0 := by
  intro hz
  have hpos : 0 < higherSymmetricPoleCancellation Q H r ((-2 : ℝ) : ℂ) :=
    LSeries.positive_of_differentiable_of_eqOn
      (primitiveHigherAugmentedCoefficient_nonneg f r)
      (by rw [primitiveHigherAugmentedCoefficient_one]; exact zero_lt_one)
      (higherSymmetricPoleCancellation_differentiable Q H hH hr)
      (primitiveHigherAugmentedCoefficient_abscissa_le f hk r)
      (fun _ hs => higherSymmetricPoleCancellation_eq_LSeries f hk H hmatch hr hz hs) (-2)
  exact (ne_of_gt hpos) (by simpa using higherSymmetricPoleCancellation_neg_two Q H r)

end
end Dubon2026
