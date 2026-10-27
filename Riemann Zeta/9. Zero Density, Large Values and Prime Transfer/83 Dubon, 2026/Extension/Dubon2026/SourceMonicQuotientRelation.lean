import Mathlib.Tactic

/-! DUB-17/18 -> rational Fourier spanning -> holomorphic recovery of the
integral Laurent summands. At a point where the denominator is nonzero,
the cleared monic equation gives the monic equation for the actual quotient.
The existing monic-root bound will then give the local boundedness required
by the already proved holomorphic quotient extension. -/
namespace Dubon2026.SourceFunctionField

theorem cleared_monic_relation_eq_scaled {K : Type*} [Field K]
    {a b : K} (hb : b ≠ 0) (d : ℕ) (c : ℕ → K) :
    a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k =
      b ^ d * ((a / b) ^ d + ∑ k ∈ Finset.range d, c k * (a / b) ^ k) := by
  have htop : b ^ d * (a / b) ^ d = a ^ d := by
    rw [div_pow]
    field_simp
  have hterm : ∀ k ∈ Finset.range d,
      b ^ d * (c k * (a / b) ^ k) = c k * b ^ (d - k) * a ^ k := by
    intro k hk
    have hk' : k ≤ d := (Finset.mem_range.mp hk).le
    rw [show b ^ d = b ^ (d - k) * b ^ k from by rw [← pow_add, Nat.sub_add_cancel hk'], div_pow]
    field_simp
  rw [mul_add, Finset.mul_sum, htop, Finset.sum_congr rfl hterm]

theorem monic_div_relation_of_cleared {K : Type*} [Field K]
    {a b : K} (hb : b ≠ 0) {d : ℕ} {c : ℕ → K}
    (h : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    (a / b) ^ d + ∑ k ∈ Finset.range d, c k * (a / b) ^ k = 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d hb)
  rw [← cleared_monic_relation_eq_scaled hb, h, mul_zero]

theorem cleared_monic_relation_of_div {K : Type*} [Field K]
    {a b : K} (hb : b ≠ 0) {d : ℕ} {c : ℕ → K}
    (h : (a / b) ^ d + ∑ k ∈ Finset.range d, c k * (a / b) ^ k = 0) :
    a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0 := by
  rw [cleared_monic_relation_eq_scaled hb, h, mul_zero]

end Dubon2026.SourceFunctionField
