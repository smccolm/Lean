import Tao2026.BurgessWeilPrimeKummerNewtonPolynomiality

/-!
# The literal Weil-only Kummer source

The general Newton recurrence specializes to the canonical Legendre quadratic.
Together with all-degree integrality this removes every algebraic recurrence
premise from the Kummer source. The all-extension Weil inequalities remain open.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

def primePowerLegendreRootMultiset
    {p : ℕ} [NeZero p] [Fact p.Prime] (m n k : ℕ) (t : ZMod p) :
    Multiset (ZMod p) :=
  Multiset.replicate m 0 + Multiset.replicate n 1 + Multiset.replicate k t

theorem primePowerLegendreRootMultiset_spectralRank
    {p : ℕ} [NeZero p] [Fact p.Prime] (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    primeRootMultisetSpectralRank (primePowerLegendreRootMultiset m n k t) = 2 := by
  have hroots : primePowerLegendreRootMultiset m n k t =
      (primeKummerLegendrePolynomial m n k t).roots :=
    (primeKummerLegendrePolynomial_roots m n k t).symm
  rw [primeRootMultisetSpectralRank, hroots,
    primeKummerLegendrePolynomial_roots_toFinset m n k t hm hn hk]
  simp [Ne.symm ht0, Ne.symm ht1]

theorem primePowerLegendreRootMultiset_count_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (m n k : ℕ) (t : ZMod p) (ht0 : t ≠ 0) :
    (primePowerLegendreRootMultiset m n k t).count 0 = m := by
  simp [primePowerLegendreRootMultiset, Multiset.count_replicate, ht0]

theorem primeRootMultisetExtensionCorrelation_legendre
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (q : ℕ) :
    primeRootMultisetExtensionCorrelation p χ (primePowerLegendreRootMultiset m n k t) q =
      primePowerLegendreExtensionCorrelation p χ m n k t q := by
  rw [← primeKummerExtensionCorrelation_eq_rootMultiset]
  exact primeKummerExtensionCorrelation_eq_powerLegendre p χ m n k t hm hn hk q

theorem primeRootMultisetNewtonPolynomial_legendre
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    primeRootMultisetNewtonPolynomial p χ (primePowerLegendreRootMultiset m n k t) =
      primePowerLegendreCharacteristicPolynomial p χ m n k t := by
  rw [primeRootMultisetNewtonPolynomial,
    primePowerLegendreRootMultiset_spectralRank m n k t hm hn hk ht0 ht1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    primeRootMultisetNewtonElementary,
    complexNewtonElementary_one, complexNewtonElementary_two,
    primeRootMultisetNewtonPowerSum]
  simp only [primeRootMultisetExtensionCorrelation_legendre p χ m n k t hm hn hk]
  simp [primePowerLegendreCharacteristicPolynomial, primePowerLegendreCharacteristicTrace,
    primePowerLegendreCharacteristicDeterminant, complexNewtonElementary]

theorem primePowerLegendreExtensionCorrelation_characteristic_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (hmred : m < orderOf χ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (q : ℕ) :
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q := by
  have hzero : (0 : ZMod p) ∈ primePowerLegendreRootMultiset m n k t := by
    simp [primePowerLegendreRootMultiset, Multiset.mem_replicate, hm.ne']
  have hcount : (primePowerLegendreRootMultiset m n k t).count 0 < orderOf χ := by
    rwa [primePowerLegendreRootMultiset_count_zero m n k t ht0]
  have hrec := primeRootMultisetNewtonPowerSum_characteristic_recurrence p χ
    (primePowerLegendreRootMultiset m n k t) 0 hzero hcount (q + 1)
  rw [primeRootMultisetNewtonPolynomial_legendre p χ m n k t hm hn hk ht0 ht1,
    primePowerLegendreRootMultiset_spectralRank m n k t hm hn hk ht0 ht1] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    primePowerLegendreCharacteristicPolynomial, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul, coeff_X, coeff_C] at hrec
  norm_num at hrec
  simp only [add_assoc, primeRootMultisetNewtonPowerSum,
    primeRootMultisetExtensionCorrelation_legendre p χ m n k t hm hn hk] at hrec
  linear_combination -hrec

theorem primePowerLegendreLiteralWeilRecurrenceConditions_iff_extensionWeilBounds
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (hmred : m < orderOf χ)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    PrimePowerLegendreLiteralWeilRecurrenceConditions p χ m n k t ↔
      PrimePowerLegendreExtensionWeilBounds p χ m n k t :=
  ⟨fun h => h.1, fun h => ⟨h,
    primePowerLegendreExtensionCorrelation_characteristic_recurrence
      p χ m n k t hm hn hk hmred ht0 ht1⟩⟩

def TaoPrimePowerLegendreLiteralWeilConditions : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        PrimePowerLegendreExtensionWeilBounds p χ m n k t

theorem taoPrimePowerLegendreLiteralWeilRecurrenceConditions_iff_weilConditions :
    TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ↔
      TaoPrimePowerLegendreLiteralWeilConditions := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hdeg
    exact (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hdeg).1
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hdeg
    exact (primePowerLegendreLiteralWeilRecurrenceConditions_iff_extensionWeilBounds
      p χ m n k t hm hn hk hmred ht0 ht1).2
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hdeg)

def TaoPrimeKummerLiteralWeilConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetExtensionWeilBounds p χ R

theorem taoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore_iff_weilConditions :
    TaoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore ↔
      TaoPrimeKummerLiteralWeilConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact (h p χ R hχ hzero hone hcard hreduced).1
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact ⟨h p χ R hχ hzero hone hcard hreduced,
      primeRootMultisetNewtonPowerSum_characteristic_recurrence p χ R 0 hzero
        (hreduced 0 (Multiset.mem_toFinset.mpr hzero))⟩

/-- The remaining Kummer source consists only of literal all-extension Weil bounds. -/
def TaoPrimeLiteralWeilConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilConditions ∧
    TaoPrimeKummerLiteralWeilConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceConditions_iff_weilConditions :
    TaoPrimeLiteralWeilRecurrenceConditions ↔ TaoPrimeLiteralWeilConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceConditions, TaoPrimeLiteralWeilConditions,
    taoPrimePowerLegendreLiteralWeilRecurrenceConditions_iff_weilConditions,
    taoPrimeKummerWeilRecurrenceConditionsFourRootsOrMore_iff_weilConditions]

theorem TaoPrimeLiteralWeilConditions.toFull (h : TaoPrimeLiteralWeilConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  (taoPrimeLiteralWeilRecurrenceConditions_iff_weilConditions.2 h).toFull

end
end Tao2026
