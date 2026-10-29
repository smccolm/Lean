import Dubon2026.SourceToricIntegerFourierTransform
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. Clear exactly the level-squared
constant-term denominator of the torsion coordinate, and express every
coefficient as evaluation of an integer polynomial. These polynomials
feed the finite integral Fourier transform. Adapted from Anthropic FLT,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
open Polynomial
variable {F : Type*} [Field F] {M : ℕ} [NeZero M] {z : F} (hz : IsPrimitiveRoot z M)

/-- The finite weighted geometric polynomial used to clear the constant-term denominator. -/
def S1 (M : ℕ) : ℤ[X] := ∑ j ∈ Finset.range M, (j : ℤ[X]) * X ^ j

omit [NeZero M] in
theorem aeval_S1 (u : F) : aeval u (S1 M) = ∑ j ∈ Finset.range M, (j : F) * u ^ j := by
  simp [S1, map_sum]

theorem one_sub_mul_S1 {a : ZMod M} (ha : a ≠ 0) :
    (1 - ψ hz a) * aeval (ψ hz a) (S1 M) = -(M : F) := by
  set u := ψ hz a with hu
  set T : F := ∑ j ∈ Finset.range M, (j : F) * u ^ j with hT
  rw [aeval_S1, ← hT]
  have h1 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j = T + M * u ^ M := Finset.sum_range_succ _ M
  have h2 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j =
      ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h3 : ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) =
      u * T + u * ∑ j ∈ Finset.range M, u ^ j := by
    rw [hT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [geom_ψ hz ha, ψ_pow_M] at *
  have key : u * T = T + M := by
    have := h1.symm.trans (h2.trans h3)
    rw [mul_zero, add_zero, mul_one] at this
    exact this.symm
  linear_combination -key

theorem inv_formula {a : ZMod M} (ha : a ≠ 0) :
    (M : F) ^ 2 * (ψ hz a / (1 - ψ hz a) ^ 2) = ψ hz a * (aeval (ψ hz a) (S1 M)) ^ 2 := by
  have h := one_sub_mul_S1 hz ha
  have hne := one_sub_ψ_ne_zero hz ha
  have : aeval (ψ hz a) (S1 M) = -(M : F) / (1 - ψ hz a) := by
    rw [eq_div_iff hne, mul_comm]; exact h
  rw [this]
  field_simp

/-- The divisor-sum coefficients of the toric x-coordinate series. -/
def xcoef (u : F) (n : ℕ) : F :=
  if n = 0 then u / (1 - u) ^ 2
  else (∑ d ∈ n.divisors, (d : F) * (u ^ d + u⁻¹ ^ d)) - 2 * ∑ d ∈ n.divisors, (d : F)

/-- An integer polynomial representing the level-squared toric x coefficient. -/
def xT (M : ℕ) (n : ℕ) : ℤ[X] :=
  if n = 0 then X * S1 M ^ 2
  else C ((M : ℤ) ^ 2) *
    ((∑ d ∈ n.divisors, (d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) - C (2 * ∑ d ∈ n.divisors, (d : ℤ)))

theorem aeval_xT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (xT M n) = (M : F) ^ 2 * xcoef (ψ hz a) n := by
  by_cases hn : n = 0
  · subst hn
    rw [xT, if_pos rfl, xcoef, if_pos rfl, map_mul, map_pow, aeval_X, inv_formula hz ha]
  · rw [xT, if_neg hn, xcoef, if_neg hn]
    have h : ∀ d ∈ n.divisors, aeval (ψ hz a) ((d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) =
        (d : F) * (ψ hz a ^ d + (ψ hz a)⁻¹ ^ d) := by
      intro d _
      rw [map_mul, map_natCast, map_add, map_pow, map_pow, aeval_X, pow_mul, ψ_pow_sub_one hz a]
    rw [map_mul, map_sub, map_sum, Finset.sum_congr rfl h, aeval_C, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_pow, Int.cast_natCast, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sum]

/-- The coefficients of one plus twelve times the toric x series. -/
def wcoef (u : F) (n : ℕ) : F := (if n = 0 then (1 : F) else 0) + 12 * xcoef u n

/-- An integer polynomial representing the level-squared normalized weight-two coefficient. -/
def wT (M : ℕ) (n : ℕ) : ℤ[X] := C ((M : ℤ) ^ 2 * (if n = 0 then 1 else 0)) + C 12 * xT M n

theorem aeval_wT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (wT M n) = (M : F) ^ 2 * wcoef (ψ hz a) n := by
  have hx := aeval_xT hz ha n
  by_cases hn : n = 0
  · subst hn
    simp only [wT, if_true, mul_one, map_add, map_mul, map_pow, map_natCast, map_ofNat, hx, wcoef]
    ring
  · simp only [wT, hn, if_false, mul_zero, map_zero, zero_add, map_mul, map_ofNat, hx, wcoef]
    ring

end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier
