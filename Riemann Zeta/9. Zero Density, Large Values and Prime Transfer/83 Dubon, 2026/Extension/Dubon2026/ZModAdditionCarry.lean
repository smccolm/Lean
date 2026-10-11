import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-! # The actual addition carry of canonical finite residue representatives -/

namespace Dubon2026

open scoped BigOperators

/-- The integer carry when the two actual canonical residue representatives are added. -/
def zmodAdditionCarry {n : ℕ} (a b : ZMod n) : ℕ := (a.val + b.val) / n

/-- The actual canonical representative and carry recover the original sum. -/
theorem zmodAdditionCarry_balance {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a + b).val + n * zmodAdditionCarry a b = a.val + b.val := by
  rw [ZMod.val_add]
  exact Nat.mod_add_div (a.val + b.val) n

/-- Associativity of original residue addition gives the exact carry cocycle identity. -/
theorem zmodAdditionCarry_assoc {n : ℕ} [NeZero n] (a b c : ZMod n) :
    zmodAdditionCarry (a + b) c + zmodAdditionCarry a b =
      zmodAdditionCarry b c + zmodAdditionCarry a (b + c) := by
  have hab := zmodAdditionCarry_balance a b
  have hbc := zmodAdditionCarry_balance b c
  have habc := zmodAdditionCarry_balance (a + b) c
  have habc' := zmodAdditionCarry_balance a (b + c)
  rw [add_assoc] at habc
  apply mul_left_cancel₀ (NeZero.ne n)
  nlinarith

/-- In a nontrivial finite cycle, exactly one carry occurs over a full generator period. -/
theorem zmodAdditionCarry_sum_one {n : ℕ} (hn : 1 < n) :
    ∑ i ∈ Finset.range n, zmodAdditionCarry (i : ZMod n) 1 = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨hn⟩
  have hlast : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (n - 1)]
  · rw [zmodAdditionCarry, ZMod.val_natCast_of_lt (by omega), ZMod.val_one]
    have h : n - 1 + 1 = n := by omega
    rw [h, Nat.div_self (by omega)]
  · intro i hi hne
    have hi' : i < n := Finset.mem_range.mp hi
    rw [zmodAdditionCarry, ZMod.val_natCast_of_lt hi', ZMod.val_one]
    exact Nat.div_eq_of_lt (by omega)
  · exact fun h => (h hlast).elim

end Dubon2026
