import Tao2026.BurgessWeilPrimeKummerLegendreEigenpair

/-!
# Canonical root-multiset form of the higher Kummer source

A monic split polynomial is determined literally by its root multiset.
This file builds the corresponding product of monic linear factors and
records its roots, degree, multiplicities, splitness, and reduced-exponent
condition exactly.

The normalized four-or-more-root source is thereby replaced by finite root
and multiplicity data containing the marked roots zero and one.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeKummerRootMultisetPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) : Polynomial (ZMod p) :=
  (R.map fun r => X - C r).prod

theorem primeKummerRootMultisetPolynomial_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) : (primeKummerRootMultisetPolynomial R).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C R

theorem primeKummerRootMultisetPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) :
    (primeKummerRootMultisetPolynomial R).roots = R := by
  exact Polynomial.roots_multiset_prod_X_sub_C R

theorem primeKummerRootMultisetPolynomial_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) : (primeKummerRootMultisetPolynomial R).Splits := by
  apply Polynomial.Splits.multisetProd
  intro f hf
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
  exact Polynomial.Splits.X_sub_C r

theorem primeKummerRootMultisetPolynomial_natDegree
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) :
    (primeKummerRootMultisetPolynomial R).natDegree = R.card := by
  rw [(primeKummerRootMultisetPolynomial_splits R).natDegree_eq_card_roots,
    primeKummerRootMultisetPolynomial_roots]

theorem primeKummerRootMultisetPolynomial_rootMultiplicity
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p)) (r : ZMod p) :
    (primeKummerRootMultisetPolynomial R).rootMultiplicity r = R.count r := by
  rw [← Polynomial.count_roots, primeKummerRootMultisetPolynomial_roots]

theorem primeKummerRootMultisetPolynomial_reduced_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    IsPrimeKummerReducedExponentPolynomial χ
        (primeKummerRootMultisetPolynomial R) ↔
      ∀ r ∈ R.toFinset, R.count r < orderOf χ := by
  constructor
  · intro h r hr
    rw [← primeKummerRootMultisetPolynomial_rootMultiplicity R r]
    apply h
    rwa [primeKummerRootMultisetPolynomial_roots]
  · intro h r hr
    rw [primeKummerRootMultisetPolynomial_roots] at hr
    rw [primeKummerRootMultisetPolynomial_rootMultiplicity R r]
    exact h r hr

theorem eq_primeKummerRootMultisetPolynomial_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP : P.Splits) (hmonic : P.Monic) :
    P = primeKummerRootMultisetPolynomial P.roots := by
  exact hP.eq_prod_roots_of_monic hmonic

def TaoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ
          (primeKummerRootMultisetPolynomial R))

theorem taoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore_iff_rootMultiset :
    TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore ↔
      TaoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    have hroots := primeKummerRootMultisetPolynomial_roots R
    apply h p χ (primeKummerRootMultisetPolynomial R) hχ
      (primeKummerRootMultisetPolynomial_monic R)
      (primeKummerRootMultisetPolynomial_splits R)
      ((primeKummerRootMultisetPolynomial_reduced_iff χ R).mpr hreduced)
    · rw [hroots]
      exact Multiset.mem_toFinset.mpr hzero
    · rw [hroots]
      exact Multiset.mem_toFinset.mpr hone
    · rwa [hroots]
  · intro h p _ _ χ P hχ hmonic hP hreduced hzero hone hcard
    have hEq := eq_primeKummerRootMultisetPolynomial_roots P hP hmonic
    rw [hEq]
    apply h p χ P.roots hχ
    · exact Multiset.mem_toFinset.mp hzero
    · exact Multiset.mem_toFinset.mp hone
    · exact hcard
    · intro r hr
      rw [Polynomial.count_roots]
      exact hreduced r hr

def TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem : Prop :=
  TaoPrimePowerLegendreEigenpair ∧ TaoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore

theorem taoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem_iff_eigenpairOrRootMultiset :
    TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem ↔
      TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem := by
  rw [TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem,
    TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem, taoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemFourRootsOrMore_iff_rootMultiset]

theorem TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem.toFull
    (h : TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem) : TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem.toFull
    (taoPrimePowerLegendreEigenpairOrFourRootsFrobeniusSystem_iff_eigenpairOrRootMultiset.mpr h)

end
end Tao2026


