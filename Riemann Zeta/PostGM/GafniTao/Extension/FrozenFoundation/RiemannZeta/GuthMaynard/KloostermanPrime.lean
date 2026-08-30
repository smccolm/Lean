import RiemannZeta.GuthMaynard.KloostermanCRT
import Mathlib.Data.Fintype.Units

/-!
# Prime-modulus reduction for the Kloosterman Weil estimate

This file resolves every elementary prime-modulus case in DFI equation (25):
the two degenerate frequencies, symmetry, and unit normalization of the two
nonzero frequencies.  The remaining local statement is thereby reduced
exactly to the normalized sum `S(1,c;p)` with `c ≠ 0`.
-/

open Complex
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- Inversion of the unit variable exchanges `ZMod` frequencies. -/
theorem kloostermanSumZMod_comm (q : ℕ) [NeZero q] (A B : ZMod q) :
    kloostermanSumZMod q A B = kloostermanSumZMod q B A := by
  unfold kloostermanSumZMod
  apply Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ)
  intro d
  simp only [Equiv.inv_apply, inv_inv]
  apply congrArg ZMod.stdAddChar
  ring

/-- A nontrivial additive character sums to `-1` over the nonzero elements
of a prime field. -/
theorem sum_units_stdAddChar_mul_eq_neg_one
    (p : ℕ) [NeZero p] [Fact p.Prime] (A : ZMod p) (hA : A ≠ 0) :
    (∑ d : (ZMod p)ˣ, ZMod.stdAddChar (A * (d : ZMod p))) = (-1 : ℂ) := by
  have hfull : (∑ x : ZMod p, ZMod.stdAddChar (A * x)) = (0 : ℂ) :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hA)
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : ZMod p)] at hfull
  have hnonzero :
      (∑ x : {x : ZMod p // x ≠ 0}, ZMod.stdAddChar (A * x.1)) =
        ∑ d : (ZMod p)ˣ, ZMod.stdAddChar (A * (d : ZMod p)) := by
    apply Fintype.sum_equiv unitsEquivNeZero.symm
    intro x
    rfl
  rw [hnonzero] at hfull
  norm_num at hfull ⊢
  linear_combination hfull

/-- Exact right-degenerate prime-modulus Kloosterman sum. -/
theorem kloostermanSumZMod_prime_zero_right
    (p : ℕ) [NeZero p] [Fact p.Prime] (A : ZMod p) (hA : A ≠ 0) :
    kloostermanSumZMod p A 0 = (-1 : ℂ) := by
  unfold kloostermanSumZMod
  simpa only [zero_mul, add_zero] using
    sum_units_stdAddChar_mul_eq_neg_one p A hA

/-- Exact left-degenerate prime-modulus Kloosterman sum. -/
theorem kloostermanSumZMod_prime_zero_left
    (p : ℕ) [NeZero p] [Fact p.Prime] (B : ZMod p) (hB : B ≠ 0) :
    kloostermanSumZMod p 0 B = (-1 : ℂ) := by
  rw [kloostermanSumZMod_comm]
  exact kloostermanSumZMod_prime_zero_right p B hB

/-- Exact doubly degenerate prime-modulus Kloosterman sum. -/
theorem kloostermanSumZMod_prime_zero_zero
    (p : ℕ) [NeZero p] [Fact p.Prime] :
    kloostermanSumZMod p 0 0 = ((p - 1 : ℕ) : ℂ) := by
  unfold kloostermanSumZMod
  calc
    (∑ d : (ZMod p)ˣ,
        ZMod.stdAddChar
          ((0 : ZMod p) * (d : ZMod p) +
            (0 : ZMod p) * (↑(d⁻¹) : ZMod p))) =
        ∑ _d : (ZMod p)ˣ, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      simpa only [zero_mul, zero_add] using
        (AddChar.map_zero_eq_one (ZMod.stdAddChar : AddChar (ZMod p) ℂ))
    _ = (Fintype.card (ZMod p)ˣ : ℂ) := by simp
    _ = (Nat.totient p : ℂ) := by rw [ZMod.card_units_eq_totient]
    _ = ((p - 1 : ℕ) : ℂ) := by rw [Nat.totient_prime Fact.out]

/-- The nondegenerate prime-modulus sum depends only on the product of its
frequencies.  This is the exact local normalization preceding the genuine
Weil argument. -/
theorem kloostermanSumZMod_prime_eq_normalized
    (p : ℕ) [NeZero p] [Fact p.Prime] (A B : ZMod p) (hA : A ≠ 0) :
    kloostermanSumZMod p A B = kloostermanSumZMod p 1 (A * B) := by
  let u : (ZMod p)ˣ := (Units.mk0 A hA)⁻¹
  rw [kloostermanSumZMod_mul_unit_inv p A B u]
  change kloostermanSumZMod p (A * (↑u : ZMod p))
      (B * (↑u⁻¹ : ZMod p)) = _
  have hu : (↑u : ZMod p) = A⁻¹ := rfl
  have huinv : (↑u⁻¹ : ZMod p) = A := by
    change ↑((Units.mk0 A hA)⁻¹)⁻¹ = A
    rw [inv_inv]
    rfl
  rw [hu, huinv, mul_inv_cancel₀ hA, mul_comm B A]

end RiemannZeta.GuthMaynard
