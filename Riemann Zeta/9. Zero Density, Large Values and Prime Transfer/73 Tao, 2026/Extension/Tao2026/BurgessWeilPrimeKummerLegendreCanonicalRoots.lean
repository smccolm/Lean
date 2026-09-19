import Tao2026.BurgessWeilPrimeKummerLegendreCanonical

/-!
# Canonical roots and the exact remaining Legendre criterion

The explicit Legendre characteristic polynomial always splits over `ℂ` and
has exactly two roots counted with multiplicity.  Their sum and product are
the correlation-determined trace and determinant.

This file removes the abstract spectral existential from the remaining
Legendre source.  A spectrum exists exactly when this fixed root multiset is
integral, has the weight-one bound, and the explicit extension correlations
satisfy the fixed quadratic recurrence.  The reverse implication proves all
power traces by two-step induction from the first two correlations.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The canonical unordered roots of the explicit Legendre characteristic
polynomial. -/
def primePowerLegendreCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Multiset ℂ :=
  (primePowerLegendreCharacteristicPolynomial p χ m n k t).roots

theorem primePowerLegendreCharacteristicPolynomial_isMonicOfDegree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCharacteristicPolynomial p χ m n k t).IsMonicOfDegree 2 := by
  unfold primePowerLegendreCharacteristicPolynomial
  exact isMonicOfDegree_sub_add_two _ _

theorem primePowerLegendreCharacteristicPolynomial_monic
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCharacteristicPolynomial p χ m n k t).Monic :=
  (primePowerLegendreCharacteristicPolynomial_isMonicOfDegree
    p χ m n k t).monic

theorem primePowerLegendreCharacteristicPolynomial_natDegree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCharacteristicPolynomial p χ m n k t).natDegree = 2 :=
  (primePowerLegendreCharacteristicPolynomial_isMonicOfDegree
    p χ m n k t).natDegree_eq

theorem primePowerLegendreCharacteristicPolynomial_splits
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCharacteristicPolynomial p χ m n k t).Splits :=
  IsAlgClosed.splits _

theorem card_primePowerLegendreCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCanonicalEigenvalues p χ m n k t).card = 2 := by
  unfold primePowerLegendreCanonicalEigenvalues
  rw [← (primePowerLegendreCharacteristicPolynomial_splits
      p χ m n k t).natDegree_eq_card_roots,
    primePowerLegendreCharacteristicPolynomial_natDegree]

theorem sum_primePowerLegendreCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCanonicalEigenvalues p χ m n k t).sum =
      primePowerLegendreCharacteristicTrace p χ m n k t := by
  have h := (primePowerLegendreCharacteristicPolynomial_splits
    p χ m n k t).nextCoeff_eq_neg_sum_roots_of_monic
      (primePowerLegendreCharacteristicPolynomial_monic p χ m n k t)
  unfold primePowerLegendreCanonicalEigenvalues
  rw [show (primePowerLegendreCharacteristicPolynomial p χ m n k t).nextCoeff =
      -primePowerLegendreCharacteristicTrace p χ m n k t by
    rw [nextCoeff_of_natDegree_pos (by
      rw [primePowerLegendreCharacteristicPolynomial_natDegree]
      omega), primePowerLegendreCharacteristicPolynomial_natDegree]
    unfold primePowerLegendreCharacteristicPolynomial
    simp] at h
  exact (neg_inj.mp h).symm

theorem prod_primePowerLegendreCanonicalEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (primePowerLegendreCanonicalEigenvalues p χ m n k t).prod =
      primePowerLegendreCharacteristicDeterminant p χ m n k t := by
  have h := (primePowerLegendreCharacteristicPolynomial_splits
    p χ m n k t).coeff_zero_eq_prod_roots_of_monic
      (primePowerLegendreCharacteristicPolynomial_monic p χ m n k t)
  unfold primePowerLegendreCanonicalEigenvalues
  rw [show (primePowerLegendreCharacteristicPolynomial p χ m n k t).coeff 0 =
      primePowerLegendreCharacteristicDeterminant p χ m n k t by
    unfold primePowerLegendreCharacteristicPolynomial
    simp] at h
  rw [primePowerLegendreCharacteristicPolynomial_natDegree] at h
  norm_num at h
  exact h.symm

/-- The exact concrete conditions still needed on the fixed canonical roots
and the explicit extension-correlation sequence. -/
def PrimePowerLegendreCanonicalConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Prop :=
  (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
      IsIntegral ℤ a) ∧
  (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
      ‖a‖ ≤ Real.sqrt p) ∧
  ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q

theorem nonempty_primePowerLegendreSpectrum_iff_canonicalConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreSpectrum p χ m n k t) ↔
      PrimePowerLegendreCanonicalConditions p χ m n k t := by
  constructor
  · rintro ⟨s⟩
    have heq : primePowerLegendreCanonicalEigenvalues p χ m n k t =
        s.eigenvalues := by
      unfold primePowerLegendreCanonicalEigenvalues
      exact primePowerLegendreCharacteristicPolynomial_roots s
    refine ⟨?_, ?_, s.trace_recurrence_characteristic⟩
    · intro a ha
      exact s.integral a (heq ▸ ha)
    · intro a ha
      exact s.weight_le a (heq ▸ ha)
  · rintro ⟨hintegral, hweight, hrecurrence⟩
    let roots := primePowerLegendreCanonicalEigenvalues p χ m n k t
    have hcard : roots.card = 2 :=
      card_primePowerLegendreCanonicalEigenvalues p χ m n k t
    have hsum : roots.sum =
        primePowerLegendreCharacteristicTrace p χ m n k t :=
      sum_primePowerLegendreCanonicalEigenvalues p χ m n k t
    have hprod : roots.prod =
        primePowerLegendreCharacteristicDeterminant p χ m n k t :=
      prod_primePowerLegendreCanonicalEigenvalues p χ m n k t
    obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
    refine ⟨{
      eigenvalues := roots
      card_eq := hcard
      integral := hintegral
      weight_le := hweight
      trace_eq := ?_ }⟩
    intro q
    rw [hab] at hsum hprod ⊢
    simp at hsum hprod ⊢
    induction q using Nat.twoStepInduction with
    | zero =>
        simp only [Nat.zero_add, pow_one]
        rw [primePowerLegendreCharacteristicTrace] at hsum
        linear_combination hsum
    | one =>
        norm_num only [Nat.reduceAdd]
        rw [primePowerLegendreCharacteristicTrace] at hsum
        have hcorr0 :
            primePowerLegendreExtensionCorrelation p χ m n k t 0 =
              -(a + b) := by
          linear_combination hsum
        rw [primePowerLegendreCharacteristicDeterminant] at hprod
        rw [hcorr0] at hprod
        field_simp at hprod
        have hcorr1 :
            primePowerLegendreExtensionCorrelation p χ m n k t 1 =
              2 * (a * b) - (a + b) ^ 2 := by
          have hprod' :
              primePowerLegendreExtensionCorrelation p χ m n k t 1 +
                  (a + b) ^ 2 = a * b * 2 := by
            rw [add_comm]
            exact hprod.symm
          calc
            _ = a * b * 2 - (a + b) ^ 2 :=
              eq_sub_of_add_eq hprod'
            _ = 2 * (a * b) - (a + b) ^ 2 := by ring
        rw [hcorr1]
        ring
    | more q ihq ihq1 =>
        rw [← hsum, ← hprod] at hrecurrence
        rw [hrecurrence q, ihq, ihq1]
        simp only [pow_succ]
        ring

/-- The source-level canonical Legendre criterion. -/
def TaoPrimePowerLegendreCanonicalConditions : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        PrimePowerLegendreCanonicalConditions p χ m n k t

theorem taoPrimePowerLegendreSpectrum_iff_canonicalConditions :
    TaoPrimePowerLegendreSpectrum ↔
      TaoPrimePowerLegendreCanonicalConditions := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact nonempty_primePowerLegendreSpectrum_iff_canonicalConditions.mp
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact nonempty_primePowerLegendreSpectrum_iff_canonicalConditions.mpr
      (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

/-- The complete residual source with the Legendre branch stated only through
its fixed canonical roots and recurrence. -/
def TaoPrimeCanonicalLegendreAndRootMultisetSpectra : Prop :=
  TaoPrimePowerLegendreCanonicalConditions ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeExplicitLegendreAndRootMultisetSpectra_iff_canonical :
    TaoPrimeExplicitLegendreAndRootMultisetSpectra ↔
      TaoPrimeCanonicalLegendreAndRootMultisetSpectra := by
  rw [TaoPrimeExplicitLegendreAndRootMultisetSpectra,
    TaoPrimeCanonicalLegendreAndRootMultisetSpectra,
    taoPrimePowerLegendreSpectrum_iff_canonicalConditions]

theorem TaoPrimeCanonicalLegendreAndRootMultisetSpectra.toFull
    (h : TaoPrimeCanonicalLegendreAndRootMultisetSpectra) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeExplicitLegendreAndRootMultisetSpectra.toFull
    (taoPrimeExplicitLegendreAndRootMultisetSpectra_iff_canonical.mpr h)

end
end Tao2026
