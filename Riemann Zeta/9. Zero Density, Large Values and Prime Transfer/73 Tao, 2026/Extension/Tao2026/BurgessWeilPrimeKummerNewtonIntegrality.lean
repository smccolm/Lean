import Tao2026.BurgessWeilPrimeKummerNewtonRecurrence
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Coefficient form of higher-root Newton integrality

For a monic split polynomial over `ℂ`, integrality of every root is equivalent
to integrality of every coefficient.  Since the Newton polynomial has known
degree, only its finite coefficient range is relevant.  This replaces the
remaining rootwise integrality clause by a finite predicate on the explicit
Newton coefficients.
-/

namespace Tao2026

open Polynomial

noncomputable section

theorem integral_roots_iff_integral_coefficients_of_monic_splits
    (P : Polynomial ℂ) (hmonic : P.Monic) (hsplits : P.Splits) :
    (∀ a ∈ P.roots, IsIntegral ℤ a) ↔
      ∀ i : ℕ, IsIntegral ℤ (P.coeff i) := by
  constructor
  · intro hroots i
    exact Polynomial.isIntegral_coeff_of_factors P
      (by rw [hmonic.leadingCoeff]; exact isIntegral_one) hsplits
      (fun a ha => hroots a ((Polynomial.mem_roots hmonic.ne_zero).mpr ha)) i
  · intro hcoeff a ha
    have hroot : P.IsRoot a :=
      (Polynomial.mem_roots hmonic.ne_zero).mp ha
    apply IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic
    · intro hdeg
      have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmonic hdeg
      rw [hP] at hroot
      simp [Polynomial.IsRoot] at hroot
    · rw [hroot]
      exact isIntegral_zero
    · exact hcoeff

/-- Integrality of precisely the nonzero-degree range of the explicit Newton
polynomial. -/
def PrimeRootMultisetNewtonCoefficientIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  ∀ i ∈ Finset.range (primeRootMultisetSpectralRank R + 1),
    IsIntegral ℤ ((primeRootMultisetNewtonPolynomial p χ R).coeff i)

theorem integral_canonicalEigenvalues_iff_newtonCoefficientIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      IsIntegral ℤ a) ↔
      PrimeRootMultisetNewtonCoefficientIntegrality p χ R := by
  unfold primeRootMultisetCanonicalEigenvalues
  unfold PrimeRootMultisetNewtonCoefficientIntegrality
  let P := primeRootMultisetNewtonPolynomial p χ R
  change (∀ a ∈ P.roots, IsIntegral ℤ a) ↔
    ∀ i ∈ Finset.range (primeRootMultisetSpectralRank R + 1),
      IsIntegral ℤ (P.coeff i)
  rw [integral_roots_iff_integral_coefficients_of_monic_splits P
    (primeRootMultisetNewtonPolynomial_monic p χ R) (IsAlgClosed.splits P)]
  constructor
  · intro h i hi
    exact h i
  · intro h i
    by_cases hi : i ≤ primeRootMultisetSpectralRank R
    · exact h i (by simpa [Nat.lt_succ_iff])
    · have hzero : P.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [primeRootMultisetNewtonPolynomial_natDegree]
        omega
      rw [hzero]
      exact isIntegral_zero

/-- The same finite integrality condition stated directly on the recursively
constructed elementary symmetric coefficients. -/
def PrimeRootMultisetNewtonElementaryIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  ∀ j ≤ primeRootMultisetSpectralRank R,
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R j)

theorem newtonCoefficientIntegrality_iff_elementaryIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    PrimeRootMultisetNewtonCoefficientIntegrality p χ R ↔
      PrimeRootMultisetNewtonElementaryIntegrality p χ R := by
  constructor
  · intro hcoeff j hj
    have h := hcoeff (primeRootMultisetSpectralRank R - j) (by simp)
    rw [primeRootMultisetNewtonPolynomial_coeff p χ R j hj] at h
    obtain heven | hodd := Nat.even_or_odd j
    · simpa [heven.neg_one_pow] using h
    · have hn := h.neg
      simpa [hodd.neg_one_pow] using hn
  · intro helem i hi
    have hi' : i ≤ primeRootMultisetSpectralRank R := by
      simpa [Nat.lt_succ_iff] using hi
    let j := primeRootMultisetSpectralRank R - i
    have hj : j ≤ primeRootMultisetSpectralRank R := Nat.sub_le _ _
    have hc := primeRootMultisetNewtonPolynomial_coeff p χ R j hj
    have hsub : primeRootMultisetSpectralRank R - j = i := by
      dsimp [j]
      omega
    rw [hsub] at hc
    rw [hc]
    exact (isIntegral_one.neg.pow j).mul (helem j hj)

/-- The characteristic residual with root integrality replaced by the finite
integrality of the explicit Newton coefficients. -/
def PrimeRootMultisetNewtonCoefficientCharacteristicConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  PrimeRootMultisetNewtonCoefficientIntegrality p χ R ∧
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      ‖a‖ ≤ Real.sqrt p) ∧
  PolynomialPowerSumRecurrence
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPowerSum p χ R)

theorem primeRootMultisetNewtonCharacteristicConditions_iff_coefficientConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    PrimeRootMultisetNewtonCharacteristicConditions p χ R ↔
      PrimeRootMultisetNewtonCoefficientCharacteristicConditions p χ R := by
  rw [PrimeRootMultisetNewtonCharacteristicConditions,
    PrimeRootMultisetNewtonCoefficientCharacteristicConditions,
    integral_canonicalEigenvalues_iff_newtonCoefficientIntegrality]

def TaoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetNewtonCoefficientCharacteristicConditions p χ R

theorem taoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore_iff_coefficientConditions :
    TaoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore ↔
      TaoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonCharacteristicConditions_iff_coefficientConditions.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonCharacteristicConditions_iff_coefficientConditions.mpr
      (h p χ R hχ hzero hone hcard hreduced)

end
end Tao2026
