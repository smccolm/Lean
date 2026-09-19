import Tao2026.BurgessWeilPrimeKummerLegendreDeterminantIntegral
import Tao2026.BurgessWeilPrimeKummerNewtonLiteralWeil

/-!
# Literal Weil bounds for the canonical Legendre sequence

Under the already explicit quadratic recurrence, the canonical root bound is
equivalent to the sharp Weil bound on every literal extension correlation.
The reverse direction is an elementary spectral-radius argument: a uniform
bound on every positive power sum of two complex numbers bounds each number.

This removes the canonical roots from the remaining Legendre source entirely.
The residual is now stated only as a sharp bound and recurrence for the
finite-field correlations themselves.  The canonical roots are also recorded
as unconditionally algebraic integral after the determinant theorem.
-/

namespace Tao2026

open Finset Complex Polynomial Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

private theorem norm_le_of_powerSum_bound
    (a b : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ n : ℕ, 0 < n → ‖a ^ n + b ^ n‖ ≤ 2 * R ^ n) :
    ‖a‖ ≤ R := by
  by_cases hR0 : R = 0
  · subst R
    have h1 := h 1 (by omega)
    have h2 := h 2 (by omega)
    norm_num at h1 h2
    have hab : a + b = 0 := h1
    have hab2 : a ^ 2 + b ^ 2 = 0 := h2
    have ha : a = 0 := by
      have hb : b = -a := eq_neg_of_add_eq_zero_right hab
      rw [hb] at hab2
      have ha2 : a * a = 0 := by
        simpa [pow_two] using (show a ^ 2 = 0 by linear_combination hab2 / 2)
      exact mul_self_eq_zero.mp ha2
    simp [ha]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    have hpow (n : ℕ) (hn : 0 < n) : ‖a‖ ^ n ≤ 3 * R ^ n := by
      have hs := h n hn
      have hs2 := h (2 * n) (by omega)
      have hdiffsq :
          ‖a ^ n - b ^ n‖ ^ 2 ≤ 8 * (R ^ n) ^ 2 := by
        rw [← norm_pow]
        calc
          ‖(a ^ n - b ^ n) ^ 2‖ =
              ‖2 * (a ^ (2 * n) + b ^ (2 * n)) -
                (a ^ n + b ^ n) ^ 2‖ := by
            congr 1
            ring
          _ ≤ ‖(2 : ℂ) * (a ^ (2 * n) + b ^ (2 * n))‖ +
                ‖(a ^ n + b ^ n) ^ 2‖ := norm_sub_le _ _
          _ = 2 * ‖a ^ (2 * n) + b ^ (2 * n)‖ +
                ‖a ^ n + b ^ n‖ ^ 2 := by norm_num [norm_mul, norm_pow]
          _ ≤ 2 * (2 * R ^ (2 * n)) + (2 * R ^ n) ^ 2 := by
            gcongr
          _ = 8 * (R ^ n) ^ 2 := by ring
      have hdiff : ‖a ^ n - b ^ n‖ ≤ 3 * R ^ n := by
        have hnonneg : 0 ≤ 3 * R ^ n := mul_nonneg (by norm_num) (pow_nonneg hR _)
        apply (sq_le_sq₀ (norm_nonneg _) hnonneg).mp
        calc
          ‖a ^ n - b ^ n‖ ^ 2 ≤ 8 * (R ^ n) ^ 2 := hdiffsq
          _ ≤ (3 * R ^ n) ^ 2 := by nlinarith [sq_nonneg (R ^ n)]
      have htwo : 2 * ‖a ^ n‖ ≤ 5 * R ^ n := by
        calc
          2 * ‖a ^ n‖ = ‖(2 : ℂ) * a ^ n‖ := by norm_num [norm_mul]
          _ = ‖(a ^ n + b ^ n) + (a ^ n - b ^ n)‖ := by ring_nf
          _ ≤ ‖a ^ n + b ^ n‖ + ‖a ^ n - b ^ n‖ := norm_add_le _ _
          _ ≤ 2 * R ^ n + 3 * R ^ n := add_le_add hs hdiff
          _ = 5 * R ^ n := by ring
      rw [norm_pow] at htwo
      nlinarith [pow_nonneg hR n]
    by_contra haR
    have hratio : 1 < ‖a‖ / R := (one_lt_div hRpos).2 (lt_of_not_ge haR)
    have ht : Tendsto (fun n : ℕ => (‖a‖ / R) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hratio
    have hev : ∀ᶠ n : ℕ in atTop, 4 ≤ (‖a‖ / R) ^ n :=
      (Filter.tendsto_atTop.1 ht 4)
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
    obtain ⟨n, hn4, hnpos⟩ := (hev.and hpos).exists
    have hn := hpow n hnpos
    have hRn : 0 < R ^ n := pow_pos hRpos _
    have hratioBound : (‖a‖ / R) ^ n ≤ 3 := by
      rw [div_pow]
      exact (div_le_iff₀ hRn).2 (by simpa [mul_comm] using hn)
    linarith

/-- Two complex numbers lie in the closed radius-`R` disk exactly when all
their positive power sums have the corresponding exponential bound. -/
theorem complexPair_norm_le_iff_powerSum_bound
    (a b : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (‖a‖ ≤ R ∧ ‖b‖ ≤ R) ↔
      ∀ n : ℕ, 0 < n → ‖a ^ n + b ^ n‖ ≤ 2 * R ^ n := by
  constructor
  · rintro ⟨ha, hb⟩ n hn
    calc
      ‖a ^ n + b ^ n‖ ≤ ‖a ^ n‖ + ‖b ^ n‖ := norm_add_le _ _
      _ ≤ R ^ n + R ^ n := by
        rw [norm_pow, norm_pow]
        exact add_le_add
          (pow_le_pow_left₀ (norm_nonneg _) ha n)
          (pow_le_pow_left₀ (norm_nonneg _) hb n)
      _ = 2 * R ^ n := by ring
  · intro h
    exact ⟨norm_le_of_powerSum_bound a b R hR h,
      norm_le_of_powerSum_bound b a R hR (fun n hn => by
        simpa [add_comm] using h n hn)⟩

/-- The explicit recurrence forces every literal correlation to be the
negative power sum of the two canonical roots. -/
theorem primePowerLegendreCanonical_powerSum_eq_of_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hrecurrence : ∀ q : ℕ,
      primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
        primePowerLegendreCharacteristicTrace p χ m n k t *
            primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
          primePowerLegendreCharacteristicDeterminant p χ m n k t *
            primePowerLegendreExtensionCorrelation p χ m n k t q) :
    ∀ q : ℕ,
      primePowerLegendreExtensionCorrelation p χ m n k t q =
        -((primePowerLegendreCanonicalEigenvalues p χ m n k t).map
          (fun a => a ^ (q + 1))).sum := by
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
  intro q
  change primePowerLegendreExtensionCorrelation p χ m n k t q =
    -(roots.map (fun a => a ^ (q + 1))).sum
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
          _ = a * b * 2 - (a + b) ^ 2 := eq_sub_of_add_eq hprod'
          _ = 2 * (a * b) - (a + b) ^ 2 := by ring
      rw [hcorr1]
      ring
  | more q ihq ihq1 =>
      rw [← hsum, ← hprod] at hrecurrence
      rw [hrecurrence q, ihq, ihq1]
      simp only [pow_succ]
      ring

/-- The sharp weight-one bound stated directly for every literal extension
correlation. -/
def PrimePowerLegendreExtensionWeilBounds
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Prop :=
  ∀ q : ℕ,
    ‖primePowerLegendreExtensionCorrelation p χ m n k t q‖ ≤
      2 * Real.sqrt p ^ (q + 1)

theorem primePowerLegendreCanonicalWeight_iff_extensionWeilBounds_of_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p)
    (hrecurrence : ∀ q : ℕ,
      primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
        primePowerLegendreCharacteristicTrace p χ m n k t *
            primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
          primePowerLegendreCharacteristicDeterminant p χ m n k t *
            primePowerLegendreExtensionCorrelation p χ m n k t q) :
    (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
        ‖a‖ ≤ Real.sqrt p) ↔
      PrimePowerLegendreExtensionWeilBounds p χ m n k t := by
  let roots := primePowerLegendreCanonicalEigenvalues p χ m n k t
  have hcard : roots.card = 2 :=
    card_primePowerLegendreCanonicalEigenvalues p χ m n k t
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have htrace := primePowerLegendreCanonical_powerSum_eq_of_recurrence
    p χ m n k t hrecurrence
  constructor
  · intro hweight q
    have ha : ‖a‖ ≤ Real.sqrt p := by
      apply hweight a
      change a ∈ roots
      rw [hab]
      simp
    have hb : ‖b‖ ≤ Real.sqrt p := by
      apply hweight b
      change b ∈ roots
      rw [hab]
      simp
    have hpowers := (complexPair_norm_le_iff_powerSum_bound a b
      (Real.sqrt p) (Real.sqrt_nonneg p)).mp ⟨ha, hb⟩ (q + 1) (by omega)
    rw [htrace q, norm_neg]
    change ‖(roots.map (fun z => z ^ (q + 1))).sum‖ ≤ _
    rw [hab]
    simpa using hpowers
  · intro hbounds
    have hpowers : ∀ d : ℕ, 0 < d →
        ‖a ^ d + b ^ d‖ ≤ 2 * Real.sqrt p ^ d := by
      intro d hd
      have ht := htrace (d - 1)
      have hbnd := hbounds (d - 1)
      have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
      change primePowerLegendreExtensionCorrelation p χ m n k t (d - 1) =
        -(roots.map (fun z => z ^ (d - 1 + 1))).sum at ht
      rw [hab, hdsub] at ht
      rw [ht, norm_neg, hdsub] at hbnd
      simpa using hbnd
    have hpair := (complexPair_norm_le_iff_powerSum_bound a b
      (Real.sqrt p) (Real.sqrt_nonneg p)).mpr hpowers
    intro z hz
    change z ∈ roots at hz
    rw [hab] at hz
    have hz' : z = a ∨ z = b := by simpa using hz
    exact hz'.elim (fun hza => hza ▸ hpair.1) (fun hzb => hzb ▸ hpair.2)

/-- Both canonical roots are unconditionally algebraic integers. -/
theorem integral_primePowerLegendreCanonicalEigenvalues_unconditional
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    ∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
      IsIntegral ℤ a := by
  exact (integral_primePowerLegendreCanonicalEigenvalues_iff_characteristicDeterminant
    p χ m n k t).mpr
      (primePowerLegendreCharacteristicDeterminant_integral_unconditional
        p χ m n k t)

/-- The exact remaining three-root conditions, stated solely in terms of the
literal extension correlations. -/
def PrimePowerLegendreLiteralWeilRecurrenceConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Prop :=
  PrimePowerLegendreExtensionWeilBounds p χ m n k t ∧
  ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q

theorem primePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    PrimePowerLegendreCanonicalWeightRecurrenceConditions p χ m n k t ↔
      PrimePowerLegendreLiteralWeilRecurrenceConditions p χ m n k t := by
  constructor
  · rintro ⟨hweight, hrecurrence⟩
    exact ⟨(primePowerLegendreCanonicalWeight_iff_extensionWeilBounds_of_recurrence
      p χ m n k t hrecurrence).mp hweight, hrecurrence⟩
  · rintro ⟨hweil, hrecurrence⟩
    exact ⟨(primePowerLegendreCanonicalWeight_iff_extensionWeilBounds_of_recurrence
      p χ m n k t hrecurrence).mpr hweil, hrecurrence⟩

theorem nonempty_primePowerLegendreSpectrum_iff_literalWeilRecurrence
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreSpectrum p χ m n k t) ↔
      PrimePowerLegendreLiteralWeilRecurrenceConditions p χ m n k t := by
  rw [nonempty_primePowerLegendreSpectrum_iff_canonicalWeightRecurrence,
    primePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence]

def TaoPrimePowerLegendreLiteralWeilRecurrenceConditions : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        PrimePowerLegendreLiteralWeilRecurrenceConditions p χ m n k t

theorem taoPrimePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence :
    TaoPrimePowerLegendreCanonicalWeightRecurrenceConditions ↔
      TaoPrimePowerLegendreLiteralWeilRecurrenceConditions := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence
      p χ m n k t).mp
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence
      p χ m n k t).mpr
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

theorem taoPrimePowerLegendreSpectrum_iff_literalWeilRecurrence :
    TaoPrimePowerLegendreSpectrum ↔
      TaoPrimePowerLegendreLiteralWeilRecurrenceConditions := by
  rw [taoPrimePowerLegendreSpectrum_iff_canonicalWeightRecurrence,
    taoPrimePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence]

def TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra_iff_literalWeilRecurrence :
    TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra := by
  rw [TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra,
    TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra,
    taoPrimePowerLegendreCanonicalWeightRecurrenceConditions_iff_literalWeilRecurrence]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra.toFull
    (taoPrimeCanonicalWeightRecurrenceLegendreAndRootMultisetSpectra_iff_literalWeilRecurrence.mpr h)

/-- The final residual with the higher-root datum stated canonically as
unique existence. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerUniqueRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra_iff_unique :
    TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra,
    TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum,
    taoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore_iff_unique]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndUniqueRootMultisetSpectrum) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra_iff_unique.mpr h)

/-- The complete residual with both branches stated using fixed literal data:
the Legendre correlation bounds/recurrence and the higher-root Newton
polynomial conditions. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra_iff_newtonConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra,
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions,
    taoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore_iff_newtonConditions]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndRootMultisetSpectra_iff_newtonConditions.mpr h)

/-- The higher-root all-extension trace identities reduced to their finite
initial segment and the characteristic recurrence of the Newton polynomial. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerNewtonRecurrenceConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions_iff_recurrenceConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions,
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions,
    taoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore_iff_recurrenceConditions]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetRecurrenceConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions_iff_recurrenceConditions.mpr h)

/-- The sharpened residual after the finite initial Newton identities are
proved automatically: the higher-root trace input is only its literal
characteristic recurrence. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions_iff_characteristicConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions,
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions,
    taoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore_iff_characteristicConditions]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndNewtonRootMultisetConditions_iff_characteristicConditions.mpr h)

/-- The higher-root integrality clause stated as a finite condition on the
coefficients of the explicit Newton polynomial. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions_iff_coefficientConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions,
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions,
    taoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore_iff_coefficientConditions]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndNewtonCharacteristicConditions_iff_coefficientConditions.mpr h)

/-- Both weight clauses are now literal all-extension Weil bounds; the only
higher-root algebraic clauses are finite Newton-coefficient integrality and
the characteristic recurrence. -/
def TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions : Prop :=
  TaoPrimePowerLegendreLiteralWeilRecurrenceConditions ∧
    TaoPrimeKummerNewtonLiteralConditionsFourRootsOrMore

theorem taoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions_iff_literalConditions :
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions ↔
      TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions := by
  rw [TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions,
    TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions,
    taoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore_iff_literalConditions]

theorem TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions.toFull
    (h : TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonLiteralConditions) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions.toFull
    (taoPrimeLiteralWeilRecurrenceLegendreAndNewtonCoefficientConditions_iff_literalConditions.mpr h)

end
end Tao2026
