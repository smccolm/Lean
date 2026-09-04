import GafniTao.WooleyCriticalBase
import Mathlib.Data.Int.ModEq

/-!
# Finite monomial objects for Wooley's p-adic concentration theorem

This file specializes equations (3.5)--(3.7) of Wooley's nested efficient
congruencing paper to the coefficient-one monomial system actually needed by
the Vinogradov critical endpoint.  The variables still range over the literal
source interval `1, ..., Q`; the congruences use every degree `1, ..., k`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The coefficient-one solutions of Wooley's system (3.7), modulo `p^B`. -/
abbrev WooleyPadicSolution (s k Q p B : ℕ) :=
  {xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q //
    ∀ j : Fin k,
      Int.ModEq (p ^ B : ℤ)
        (fordVinogradovPowerVector s k Q xy.1 j)
        (fordVinogradovPowerVector s k Q xy.2 j)}

/-- The unnormalised coefficient-one form of `U^B_{s,k}`. -/
def wooleyPadicCount (s k Q p B : ℕ) : ℕ :=
  Nat.card (WooleyPadicSolution s k Q p B)

/-- An exact Vinogradov solution is, in particular, a solution modulo every
modulus. -/
def fordPowerSolutionToWooleyPadic
    (s k Q p B : ℕ) :
    FordPowerSolution s k Q → WooleyPadicSolution s k Q p B :=
  fun xy => ⟨xy.1, fun j => by
    rw [xy.2]⟩

theorem fordPowerSolutionToWooleyPadic_injective
    (s k Q p B : ℕ) :
    Function.Injective (fordPowerSolutionToWooleyPadic s k Q p B) := by
  intro x y hxy
  apply Subtype.ext
  simpa only [fordPowerSolutionToWooleyPadic] using
    congrArg Subtype.val hxy

/-- The exact integral Vinogradov count embeds into every modular count. -/
theorem fordVinogradovMomentNat_le_wooleyPadicCount
    (s k Q p B : ℕ) :
    fordVinogradovMomentNat s k Q ≤ wooleyPadicCount s k Q p B := by
  rw [← card_fordPowerSolution]
  exact Nat.card_le_card_of_injective _
    (fordPowerSolutionToWooleyPadic_injective s k Q p B)

theorem fordVinogradovPowerVector_le_top_degree
    {s k Q : ℕ} (hQ : 1 ≤ Q)
    (x : FordVinogradovTuple s Q) (j : Fin k) :
    fordVinogradovPowerVector s k Q x j ≤ (s * Q ^ k : ℕ) := by
  have hx := (fordVinogradovPowerVector_bounds x j).2
  have hj : (j : ℕ) + 1 ≤ k := j.isLt
  have hpow : Q ^ ((j : ℕ) + 1) ≤ Q ^ k :=
    Nat.pow_le_pow_right (by omega) hj
  have hx' : fordVinogradovPowerVector s k Q x j ≤
      ((s * Q ^ k : ℕ) : ℤ) := by
    push_cast
    exact hx.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hpow)
      (by positivity))
  exact_mod_cast hx'

/-- Once the modulus exceeds the entire possible degree-`k` displacement,
Wooley's congruence system is literally the integral Vinogradov system. -/
theorem wooleyPadicSolution_powerVector_eq
    {s k Q p B : ℕ} (hQ : 1 ≤ Q)
    (hmodulus : s * Q ^ k < p ^ B)
    (z : WooleyPadicSolution s k Q p B) :
    fordVinogradovPowerVector s k Q z.1.1 =
      fordVinogradovPowerVector s k Q z.1.2 := by
  funext j
  let a := fordVinogradovPowerVector s k Q z.1.1 j
  let b := fordVinogradovPowerVector s k Q z.1.2 j
  have haLower : (0 : ℤ) ≤ a := by
    dsimp [a]
    exact (by positivity : (0 : ℤ) ≤ s).trans
      (fordVinogradovPowerVector_bounds z.1.1 j).1
  have hbLower : (0 : ℤ) ≤ b := by
    dsimp [b]
    exact (by positivity : (0 : ℤ) ≤ s).trans
      (fordVinogradovPowerVector_bounds z.1.2 j).1
  have haUpper : a ≤ ((s * Q ^ k : ℕ) : ℤ) := by
    exact_mod_cast fordVinogradovPowerVector_le_top_degree hQ z.1.1 j
  have hbUpper : b ≤ ((s * Q ^ k : ℕ) : ℤ) := by
    exact_mod_cast fordVinogradovPowerVector_le_top_degree hQ z.1.2 j
  have hmodulusZ : ((s * Q ^ k : ℕ) : ℤ) < ((p ^ B : ℕ) : ℤ) := by
    exact_mod_cast hmodulus
  have habs : |b - a| < ((p ^ B : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : b - a = 0 :=
    Int.eq_zero_of_abs_lt_dvd (z.2 j).dvd habs
  dsimp [a, b] at hzero
  exact (sub_eq_zero.mp hzero).symm

def wooleyPadicToFordPowerSolution
    {s k Q p B : ℕ} (hQ : 1 ≤ Q)
    (hmodulus : s * Q ^ k < p ^ B) :
    WooleyPadicSolution s k Q p B → FordPowerSolution s k Q :=
  fun z => ⟨z.1, wooleyPadicSolution_powerVector_eq hQ hmodulus z⟩

/-- Exact count equality in the no-wrap range used in Wooley Section 12. -/
theorem wooleyPadicCount_eq_fordVinogradovMomentNat
    {s k Q p B : ℕ} (hQ : 1 ≤ Q)
    (hmodulus : s * Q ^ k < p ^ B) :
    wooleyPadicCount s k Q p B = fordVinogradovMomentNat s k Q := by
  rw [← card_fordPowerSolution]
  apply Nat.card_congr
  exact {
    toFun := wooleyPadicToFordPowerSolution hQ hmodulus
    invFun := fordPowerSolutionToWooleyPadic s k Q p B
    left_inv := fun z => Subtype.ext rfl
    right_inv := fun z => Subtype.ext rfl }

#print axioms fordVinogradovMomentNat_le_wooleyPadicCount
#print axioms fordVinogradovPowerVector_le_top_degree
#print axioms wooleyPadicSolution_powerVector_eq
#print axioms wooleyPadicCount_eq_fordVinogradovMomentNat

end

end GafniTao
