import Dubon2026.CuspCoefficientLSeries
import Dubon2026.LocalRecurrenceSeries
import Dubon2026.PrimitiveSatakeParameters

/-! # Genuine unramified Euler factors from actual normalized primitive coefficients -/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual prime-power local Dirichlet summand in its power-series coordinate. -/
def primitiveLocalTerm {Q : ℕ} [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (p : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  normalizedCuspCoefficients f.toCuspForm (p ^ r) * ((p : ℂ) ^ (-s)) ^ r

/-- The local term is exactly the original coefficient times its principal Dirichlet power. -/
theorem primitiveLocalTerm_eq_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : ℕ) (s : ℂ) (r : ℕ) :
    primitiveLocalTerm f p s r =
      normalizedCuspCoefficients f.toCuspForm (p ^ r) * ((p ^ r : ℕ) : ℂ) ^ (-s) := by
  unfold primitiveLocalTerm
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Absolute convergence of the actual global coefficients supplies convergence at every genuine prime. -/
theorem summable_primitiveLocalTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    Summable (primitiveLocalTerm f p s) := by
  have he := (summable_norm_cusp_dirichlet f.toCuspForm hk hs).of_norm.comp_injective
    (Nat.pow_right_injective hp.one_lt)
  apply he.congr
  intro r
  exact (primitiveLocalTerm_eq_dirichlet f p s r).symm

/-- The good-prime local series has the exact normalized Hecke recurrence with both spectral factors. -/
theorem primitiveLocalTerm_good_recurrence {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (s : ℂ) (r : ℕ) :
    primitiveLocalTerm f p s (r + 2) =
      (normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s)) * primitiveLocalTerm f p s (r + 1) -
        ((p : ℂ) ^ (-s)) ^ 2 * primitiveLocalTerm f p s r := by
  unfold primitiveLocalTerm
  rw [primitiveCuspForm_normalized_primePower_recurrence f hp hpQ, pow_add, pow_succ]
  ring

/-- The genuine unramified Euler series equals its inverse quadratic, with convergence discharged from the original cusp form. -/
theorem primitive_good_euler_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveLocalTerm f p s r) =
      (1 - normalizedCuspCoefficients f.toCuspForm p * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  apply tsum_second_order_eq_euler_inverse (summable_primitiveLocalTerm f hk hp hs)
  · simp only [primitiveLocalTerm, pow_zero, mul_one,
      normalizedCuspCoefficients_one f.toCuspForm f.normalized]
  · simp only [primitiveLocalTerm, pow_one]
  · exact primitiveLocalTerm_good_recurrence f hp hpQ s

/-- The exact inverse quadratic is the product of the two actual local root factors. -/
theorem primitive_good_euler_series_roots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveLocalTerm f p s r) =
      ((1 - primitiveSatakePlus f p * (p : ℂ) ^ (-s)) *
        (1 - primitiveSatakeMinus f p * (p : ℂ) ^ (-s)))⁻¹ := by
  rw [primitive_good_euler_series f hk hp hpQ hs]
  exact congrArg Inv.inv (satakeRoot_euler_factor (normalizedCuspCoefficients f.toCuspForm p) ((p : ℂ) ^ (-s))).symm

end
end Dubon2026
