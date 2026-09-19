import Tao2026.WeightedOrbitNewtonIntegrality
import Tao2026.BurgessWeilPrimeKummerLegendreLiteralWeil

/-!
# Unconditional all-degree Kummer Newton integrality

The degree-`m!` finite field contains every subfield needed for the first
`m` literal extension correlations. Its weighted Frobenius orbits satisfy
the general Euler-product theorem, so every reconstructed Newton elementary
coefficient is an algebraic integer. Consequently the canonical Newton
polynomial and its roots are integral without any residual hypothesis.

The final residual therefore consists only of literal all-extension Weil
bounds and the characteristic recurrences, in the Legendre and higher-root
branches. These remaining clauses are not proved in this file.
-/

namespace Tao2026
open Finset
open scoped BigOperators
noncomputable section

def primeFieldFrobeniusPerm (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n] :
    Equiv.Perm (primeFieldExtension p n) :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (primeFieldExtension p n)).toEquiv

theorem primeFieldFrobeniusPerm_pow_apply (p n d : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero n] (x : primeFieldExtension p n) :
    (primeFieldFrobeniusPerm p n ^ d) x =
      (FiniteField.Extension.frob (ZMod p) p n ^ d) x := by
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic
    (ZMod p) (primeFieldExtension p n) : primeFieldExtension p n → primeFieldExtension p n)^[d]) x = _
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp only [ZMod.card, FiniteField.Extension.frob_iterate_apply, Nat.card_zmod]

theorem primeFieldFrobeniusPerm_apply (p n : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero n] (x : primeFieldExtension p n) :
    primeFieldFrobeniusPerm p n x = FiniteField.Extension.frob (ZMod p) p n x := by
  simpa only [pow_one] using primeFieldFrobeniusPerm_pow_apply p n 1 x

theorem primeRootMultisetNewtonElementary_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (m : ℕ) :
    IsIntegral ℤ (primeRootMultisetNewtonElementary p χ R m) := by
  classical
  letI : NeZero m.factorial := ⟨Nat.factorial_ne_zero m⟩
  letI : Fintype (primeFieldExtension p m.factorial) := Fintype.ofFinite _
  apply finitePermutationWeight_newton_integral
    (primeFieldFrobeniusPerm p m.factorial)
    (primeFieldFrobeniusWeight p m.factorial · χ R)
    (fun d x => primeFieldFrobeniusWeight_integral p m.factorial d χ R x)
    (s := primeRootMultisetNewtonPowerSum p χ R) (m := m)
  · intro d x hx
    rw [primeFieldFrobeniusPerm_apply]
    exact primeFieldFrobeniusWeight_frob p m.factorial d χ R x
      (by simpa only [primeFieldFrobeniusPerm_pow_apply] using hx)
  · intro d k x hx
    exact primeFieldFrobeniusWeight_mul p m.factorial d k χ R x
      (by simpa only [primeFieldFrobeniusPerm_pow_apply] using hx)
  · intro d hd hdm
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [primeRootMultisetNewtonPowerSum]
    congr 1
    rw [primeRootMultisetExtensionCorrelation_eq_fixed_sum p m.factorial q
      (Nat.dvd_factorial (Nat.succ_pos q) hdm) χ R]
    simp only [primeFieldFrobeniusPerm_pow_apply, Nat.succ_eq_add_one]

theorem primeRootMultisetNewtonElementaryIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    PrimeRootMultisetNewtonElementaryIntegrality p χ R :=
  fun j _ => primeRootMultisetNewtonElementary_integral p χ R j

theorem primeRootMultisetNewtonCoefficientIntegrality
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    PrimeRootMultisetNewtonCoefficientIntegrality p χ R :=
  (newtonCoefficientIntegrality_iff_elementaryIntegrality p χ R).2
    (primeRootMultisetNewtonElementaryIntegrality p χ R)

theorem primeRootMultisetCanonicalEigenvalues_integral
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    ∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R, IsIntegral ℤ a :=
  (integral_canonicalEigenvalues_iff_newtonCoefficientIntegrality p χ R).2
    (primeRootMultisetNewtonCoefficientIntegrality p χ R)

def PrimeRootMultisetWeilRecurrenceConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  PrimeRootMultisetExtensionWeilBounds p χ R ∧
    PolynomialPowerSumRecurrence
      (primeRootMultisetNewtonPolynomial p χ R)
      (primeRootMultisetSpectralRank R)
      (primeRootMultisetNewtonPowerSum p χ R)

theorem primeRootMultisetNewtonLiteralConditions_iff_weilRecurrenceConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    PrimeRootMultisetNewtonLiteralConditions p χ R ↔
      PrimeRootMultisetWeilRecurrenceConditions p χ R :=
  ⟨fun h => h.2, fun h => ⟨primeRootMultisetNewtonCoefficientIntegrality p χ R, h⟩⟩

def TaoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetWeilRecurrenceConditions p χ R

theorem taoPrimeKummerNewtonLiteralConditionsFourRootsOrMore_iff_weilRecurrenceConditions :
    TaoPrimeKummerNewtonLiteralConditionsFourRootsOrMore ↔
      TaoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact (primeRootMultisetNewtonLiteralConditions_iff_weilRecurrenceConditions p χ R).1
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact (primeRootMultisetNewtonLiteralConditions_iff_weilRecurrenceConditions p χ R).2
      (h p χ R hχ hzero hone hcard hreduced)

/-- Only literal Weil bounds and characteristic recurrences remain. -/
def TaoPrimeLiteralWeilRecurrenceConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions_iff_weilRecurrenceConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions ↔
      TaoPrimeLiteralWeilRecurrenceConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions,
    TaoPrimeLiteralWeilRecurrenceConditions,
    taoPrimeKummerNewtonLiteralConditionsFourRootsOrMore_iff_weilRecurrenceConditions]

theorem TaoPrimeLiteralWeilRecurrenceConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions_iff_weilRecurrenceConditions.2 h)

end
end Tao2026
