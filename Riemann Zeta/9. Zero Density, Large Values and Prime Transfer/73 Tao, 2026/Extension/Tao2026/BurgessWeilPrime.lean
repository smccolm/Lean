import Tao2026.BurgessWeilPrimeSquare

/-!
# Prime local boundary for the Burgess complete correlation

The prime-square estimate is elementary stationary phase and is closed in
`BurgessWeilPrimeSquare`.  This file normalizes the sole remaining local
input to a finite-field multiplicative-character estimate for two products
of linear factors with one tagged shift occurring uniquely.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- A complete quotient-character sum formed from two tagged blocks of
linear factors over `ZMod p`. -/
def primeLinearQuotientCorrelation
    (p r : ℕ) [NeZero p] (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) : ℂ :=
  ∑ x : ZMod p,
    χ (Finset.univ.prod (fun i : Fin r => x + b (Sum.inl i))) *
      χ⁻¹ (Finset.univ.prod (fun i : Fin r => x + b (Sum.inr i)))

/-- The exact algebraic-geometry input still needed at prime level.  It no
longer mentions integer lifts, conductors, cube-free factorization, or the
Burgess moment: a nontrivial multiplicative character and one uniquely
occurring tagged linear root are the complete hypotheses. -/
def TaoPrimeLinearQuotientWeilBound : Prop :=
  ∀ (p r : ℕ) [NeZero p]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r),
    p.Prime → 2 ≤ r → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    ‖primeLinearQuotientCorrelation p r χ b‖ ≤
      ((4 * r : ℕ) : ℝ) * Real.sqrt p

/-- The prime quotient-character estimate at the sole order used in Tao's
fourteenth-moment Burgess argument. -/
def TaoPrimeLinearQuotientWeilBoundRSeven : Prop :=
  ∀ (p : ℕ) [NeZero p]
    (χ : MulChar (ZMod p) ℂ)
    (b : Fin 7 ⊕ Fin 7 → ZMod p) (j : Fin 7 ⊕ Fin 7),
    p.Prime → χ ≠ 1 →
    (∀ i, b i = b j → i = j) →
    ‖primeLinearQuotientCorrelation p 7 χ b‖ ≤
      ((4 * 7 : ℕ) : ℝ) * Real.sqrt p

/-- The Burgess tuple shifts reduced modulo a prime. -/
def burgessPrimeTaggedShift
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r) : ZMod p :=
  ((((burgessTupleFlatten uv j).1 + 1 : ℕ)) : ZMod p)

/-- The existing Burgess complete correlation at prime level is literally
the normalized linear-quotient correlation. -/
theorem burgessCompleteCorrelation_eq_primeLinearQuotientCorrelation
    (p B r : ℕ) [NeZero p] (χ : DirichletCharacter ℂ p)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessCompleteCorrelation χ uv =
      primeLinearQuotientCorrelation p r χ
        (burgessPrimeTaggedShift p B r uv) := by
  unfold burgessCompleteCorrelation primeLinearQuotientCorrelation
  unfold burgessTupleNumerator burgessTupleDenominator
  unfold burgessPrimeTaggedShift burgessTupleFlatten
  rfl

/-- Coprimality of `A_j` with `p` says precisely that the selected tagged
shift remains unique after reduction modulo `p`. -/
theorem burgessPrimeTaggedShift_unique_of_coefficient_coprime
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    ∀ i, burgessPrimeTaggedShift p B r uv i =
        burgessPrimeTaggedShift p B r uv j → i = j := by
  intro i hi
  by_contra hij
  have hdiff := intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
    p B r hp uv j i hij hcop
  apply hdiff
  unfold burgessPrimeTaggedShift at hi
  rw [Int.cast_sub]
  unfold burgessTupleShiftInt
  push_cast
  simpa only [Nat.cast_add, Nat.cast_one] using sub_eq_zero.mpr hi

/-- A primitive character at a prime level is nontrivial. -/
theorem dirichletCharacter_ne_one_of_isPrimitive_prime
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p)
    (hχ : DirichletCharacter.IsPrimitive χ) : χ ≠ 1 := by
  intro hone
  subst χ
  apply hp.ne_one
  exact hχ.symm.trans DirichletCharacter.conductor_one

/-- The normalized finite-field Weil theorem implies the remaining primitive
prime coprime-coefficient predicate. -/
theorem TaoPrimeLinearQuotientWeilBound.toPrimeCoprimeCoefficient
    (hweil : TaoPrimeLinearQuotientWeilBound) :
    TaoPrimitivePrimeCoprimeCoefficientWeilBound := by
  intro p B r _ χ uv j hp hr hχ hAj hcop
  have hp' : (p ^ 1).Prime := by simpa only [pow_one] using hp
  rw [burgessCompleteCorrelation_eq_primeLinearQuotientCorrelation]
  simpa only [pow_one] using
    hweil (p ^ 1) r χ (burgessPrimeTaggedShift (p ^ 1) B r uv) j hp' hr
      (dirichletCharacter_ne_one_of_isPrimitive_prime (p ^ 1) hp' χ hχ)
      (burgessPrimeTaggedShift_unique_of_coefficient_coprime
        (p ^ 1) B r hp' uv j (by simpa only [pow_one] using hcop))

/-- Consequently this one finite-field theorem closes the full cube-free
composite complete-sum estimate, since the prime-square branch is proved. -/
theorem TaoPrimeLinearQuotientWeilBound.toComposite
    (hweil : TaoPrimeLinearQuotientWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toPrimeCoprimeCoefficient.toComposite

/-- The fixed prime quotient estimate gives the fixed prime
coprime-coefficient predicate. -/
theorem TaoPrimeLinearQuotientWeilBoundRSeven.toPrimeCoprimeCoefficient
    (hweil : TaoPrimeLinearQuotientWeilBoundRSeven) :
    TaoPrimitivePrimeCoprimeCoefficientWeilBoundRSeven := by
  intro p B _ χ uv j hp hχ hAj hcop
  have hp' : (p ^ 1).Prime := by simpa only [pow_one] using hp
  rw [burgessCompleteCorrelation_eq_primeLinearQuotientCorrelation]
  simpa only [pow_one] using
    hweil (p ^ 1) χ (burgessPrimeTaggedShift (p ^ 1) B 7 uv) j hp'
      (dirichletCharacter_ne_one_of_isPrimitive_prime (p ^ 1) hp' χ hχ)
      (burgessPrimeTaggedShift_unique_of_coefficient_coprime
        (p ^ 1) B 7 hp' uv j (by simpa only [pow_one] using hcop))

/-- The fixed prime quotient estimate closes exactly the complete-sum input
used by Tao's fourteenth moment. -/
theorem TaoPrimeLinearQuotientWeilBoundRSeven.toComposite
    (hweil : TaoPrimeLinearQuotientWeilBoundRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  (TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven.ofPrimeAndPrimeSquare
    hweil.toPrimeCoprimeCoefficient
    taoPrimitivePrimeSquareCoprimeCoefficientWeilBound).toComposite

end

end Tao2026
