import Tao2026.BurgessWeilPrimeKummer
import Mathlib.Algebra.Field.GeomSum

/-!
# Character orthogonality for the prime Kummer trace

This file begins the source-facing finite-field geometry layer below the
remaining Burgess Weil boundary.  For a multiplicative character `χ`, the
positive powers `χ, χ^2, ..., χ^(orderOf χ)` detect exactly the nonzero
values on which `χ` is one.  Summing that identity over polynomial values
turns the corresponding family of complete character sums into an exact
Kummer-fiber count.

No cancellation estimate is assumed here: both identities are elementary
consequences of the geometric-series formula and `χ ^ orderOf χ = 1`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The polynomial inputs whose nonzero value lies in the kernel of `χ`.
The equation `χ (P.eval x) = 1` already excludes `P.eval x = 0`. -/
def primeKummerKernelFiber
    (p : ℕ) [NeZero p] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter fun x => χ (P.eval x) = 1

/-- Positive character-power orthogonality at a single field element.  The
index `k + 1` is essential at zero: unlike a positive character power, the
zeroth power character still maps zero to zero. -/
theorem sum_range_mulChar_apply_pow_succ
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (a : F) :
    (∑ k ∈ Finset.range (orderOf χ), χ a ^ (k + 1)) =
      if χ a = 1 then (orderOf χ : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst a
    simp [χ.map_zero]
  · by_cases hχa : χ a = 1
    · simp [hχa]
    · rw [if_neg hχa]
      have hpow : χ a ^ orderOf χ = 1 := by
        rw [← χ.pow_apply' χ.orderOf_pos.ne' a, pow_orderOf_eq_one]
        exact MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)
      calc
        (∑ k ∈ Finset.range (orderOf χ), χ a ^ (k + 1)) =
            χ a * ∑ k ∈ Finset.range (orderOf χ), χ a ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [pow_succ']
        _ = χ a * ((χ a ^ orderOf χ - 1) / (χ a - 1)) := by
          rw [geom_sum_eq hχa]
        _ = 0 := by rw [hpow]; simp

/-- Exact Kummer-fiber formula for the positive powers of a complete
polynomial character sum.  This is the finite affine-fiber identity that a
future projective Kummer-curve point-count estimate will consume. -/
theorem sum_range_primePolynomialCharacterCorrelation_pow_succ_eq_kernelFiber
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (∑ k ∈ Finset.range (orderOf χ),
        primePolynomialCharacterCorrelation p (χ ^ (k + 1)) P) =
      (orderOf χ : ℂ) * (primeKummerKernelFiber p χ P).card := by
  unfold primePolynomialCharacterCorrelation
  rw [Finset.sum_comm]
  simp_rw [χ.pow_apply' (Nat.succ_ne_zero _)]
  simp_rw [sum_range_mulChar_apply_pow_succ]
  calc
    (∑ x : ZMod p,
        if χ (P.eval x) = 1 then (orderOf χ : ℂ) else 0) =
        ∑ x : ZMod p, (orderOf χ : ℂ) *
          if χ (P.eval x) = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      split <;> simp_all
    _ = (orderOf χ : ℂ) *
        ∑ x : ZMod p, if χ (P.eval x) = 1 then 1 else 0 := by
      rw [Finset.mul_sum]
    _ = (orderOf χ : ℂ) * (primeKummerKernelFiber p χ P).card := by
      simp [primeKummerKernelFiber, Finset.sum_boole]

/-- Split-polynomial form of the same exact fiber identity, stated in the
distinct-root normal form used by the sharp Kummer Weil boundary. -/
theorem sum_range_primeKummerRootCorrelation_pow_succ_eq_kernelFiber
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    (∑ k ∈ Finset.range (orderOf χ),
        primeKummerRootCorrelation (χ ^ (k + 1)) P) =
      (orderOf χ : ℂ) * (primeKummerKernelFiber p χ P).card := by
  rw [← sum_range_primePolynomialCharacterCorrelation_pow_succ_eq_kernelFiber
    p χ P]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (primePolynomialCharacterCorrelation_eq_kummerRootCorrelation
    (χ ^ (k + 1)) P hP).symm

end

end Tao2026
