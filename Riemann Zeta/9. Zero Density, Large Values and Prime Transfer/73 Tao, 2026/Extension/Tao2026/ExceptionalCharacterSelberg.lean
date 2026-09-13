import Tao2026.SelbergPrimeWeights

/-!
# Selberg-weight specialization of the exceptional-character BHM step

This file connects the concrete prime Selberg weight to the finite weighted
Gram formalism.  It removes the artificial zero coordinate, proves the exact
finite divisor expansion of a weighted correlation, and derives the diagonal
bound required in Tao's Lemma 5.1.  The remaining off-diagonal input is thereby
reduced to ordinary character sums on multiples of each supported divisor.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The Selberg divisor weight with the unused zero coordinate set to zero. -/
def taoSelbergBHMWeight (R : ℕ) (hR : 1 ≤ R) (n : ℕ) : ℝ :=
  if n = 0 then 0 else taoSelbergDivisorWeight R hR n

theorem taoSelbergBHMWeight_nonneg
    (R : ℕ) (hR : 1 ≤ R) (n : ℕ) :
    0 ≤ taoSelbergBHMWeight R hR n := by
  unfold taoSelbergBHMWeight
  split_ifs
  · exact le_rfl
  · exact taoSelbergDivisorWeight_nonneg R hR n

theorem taoSelbergBHMWeight_eq_one_on_dyadicPrimeBand
    {R Z : ℕ} (hR : 1 ≤ R) (hRZ : R < Z) :
    ∀ p ∈ taoDyadicPrimeBand Z, taoSelbergBHMWeight R hR p = 1 := by
  intro p hp
  have hpPrime := (mem_taoDyadicPrimeBand.mp hp).1
  simp [taoSelbergBHMWeight, hpPrime.ne_zero,
    taoSelbergDivisorWeight_eq_one_on_dyadicPrimeBand hR hRZ p hp]

/-- Removing zero identifies a range sum with the positive interval ending at
`N-1`. -/
theorem sum_range_taoSelbergBHMWeight_mul_eq_Ioc
    (R N : ℕ) (hR : 1 ≤ R) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range N, (taoSelbergBHMWeight R hR n : ℂ) * f n) =
      ∑ n ∈ Finset.Ioc 0 (N - 1),
        (taoSelbergDivisorWeight R hR n : ℂ) * f n := by
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro n hn
    rw [mem_Ioc] at hn
    rw [mem_range]
    omega
  · intro n hn
    have hnRange := mem_range.mp (mem_sdiff.mp hn).1
    have hnNotIoc := (mem_sdiff.mp hn).2
    have hnZero : n = 0 := by
      by_contra hn0
      apply hnNotIoc
      exact mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, by omega⟩
    simp [taoSelbergBHMWeight, hnZero]
  · intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Ioc.mp hn).1
    simp [taoSelbergBHMWeight, hn0]

/-- Real-valued version of the zero-coordinate removal identity. -/
theorem sum_range_taoSelbergBHMWeight_eq_Ioc
    (R N : ℕ) (hR : 1 ≤ R) :
    (∑ n ∈ Finset.range N, taoSelbergBHMWeight R hR n) =
      ∑ n ∈ Finset.Ioc 0 (N - 1), taoSelbergDivisorWeight R hR n := by
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro n hn
    rw [mem_Ioc] at hn
    rw [mem_range]
    omega
  · intro n hn
    have hnRange := mem_range.mp (mem_sdiff.mp hn).1
    have hnNotIoc := (mem_sdiff.mp hn).2
    have hnZero : n = 0 := by
      by_contra hn0
      apply hnNotIoc
      exact mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, by omega⟩
    simp [taoSelbergBHMWeight, hnZero]
  · intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Ioc.mp hn).1
    simp [taoSelbergBHMWeight, hn0]

/-- Positive multiples of `d` up to `X` are the image of the positive prefix
up to `X/d`. -/
theorem Ioc_filter_dvd_eq_image_mul
    (d X : ℕ) (hd : d ≠ 0) :
    Finset.filter (fun n ↦ d ∣ n) (Finset.Ioc 0 X) =
      Finset.image (fun m ↦ m * d) (Finset.Ioc 0 (X / d)) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨h0n, hnX⟩, hdn⟩
    have hdivPos : 0 < n / d := by
      simpa using Nat.div_lt_div_of_lt_of_dvd hdn h0n
    exact ⟨n / d, ⟨hdivPos, Nat.div_le_div_right hnX⟩,
      Nat.div_mul_cancel hdn⟩
  · rintro ⟨m, ⟨hmPos, hmBound⟩, rfl⟩
    have hmPos' : 0 / d < m := by simpa using hmPos
    exact ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).mp hmPos',
      Nat.mul_le_of_le_div d m X hmBound⟩, Nat.dvd_mul_left d m⟩

/-- Exact reindexing of a divisor-restricted correlation as an ordinary
prefix sum. -/
theorem sum_Ioc_ite_dvd_eq_sum_mul
    (d X : ℕ) (hd : d ≠ 0) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 X, if d ∣ n then f n else 0) =
      ∑ m ∈ Finset.Ioc 0 (X / d), f (m * d) := by
  rw [← sum_filter, Ioc_filter_dvd_eq_image_mul d X hd, Finset.sum_image]
  intro m hm m' hm' heq
  exact mul_left_injective₀ hd heq

/-- Exact divisor expansion of a complex correlation against the concrete
Selberg weight. -/
theorem sum_Ioc_taoSelbergDivisorWeight_mul_eq_divisorSum
    (R X : ℕ) (hR : 1 ≤ R) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 X,
        (taoSelbergDivisorWeight R hR n : ℂ) * f n) =
      ∑ d ∈ (primorial R).divisors,
        (taoSelbergSieveCoefficient R hR d : ℂ) *
          ∑ n ∈ Finset.Ioc 0 X, if d ∣ n then f n else 0 := by
  simp_rw [taoSelbergDivisorWeight_eq_sum_primorialDivisors]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- A uniform bound for every supported divisor correlation gives the expected
coefficient-`ℓ¹` off-diagonal estimate. -/
theorem norm_sum_Ioc_taoSelbergDivisorWeight_mul_le
    (R X : ℕ) (hR : 1 ≤ R) (f : ℕ → ℂ) (E : ℝ)
    (hE : 0 ≤ E)
    (hcorr : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ n ∈ Finset.Ioc 0 X, if d ∣ n then f n else 0‖ ≤ E) :
    ‖∑ n ∈ Finset.Ioc 0 X,
        (taoSelbergDivisorWeight R hR n : ℂ) * f n‖ ≤
      ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
  rw [sum_Ioc_taoSelbergDivisorWeight_mul_eq_divisorSum]
  calc
    ‖∑ d ∈ (primorial R).divisors,
        (taoSelbergSieveCoefficient R hR d : ℂ) *
          ∑ n ∈ Finset.Ioc 0 X, if d ∣ n then f n else 0‖ ≤
        ∑ d ∈ (primorial R).divisors,
          ‖(taoSelbergSieveCoefficient R hR d : ℂ) *
            ∑ n ∈ Finset.Ioc 0 X, if d ∣ n then f n else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (primorial R).divisors,
        (if (d : ℝ) ≤ R then |taoSelbergSieveCoefficient R hR d| else 0) * E := by
      apply sum_le_sum
      intro d hd
      by_cases hdLevel : (d : ℝ) ≤ R
      · rw [if_pos hdLevel, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hcorr d hd hdLevel) (abs_nonneg _)
      · rw [if_neg hdLevel]
        have hRd : R < d := by exact_mod_cast (lt_of_not_ge hdLevel)
        rw [taoSelbergSieveCoefficient_eq_zero_of_level_lt R hR d hRd]
        simp
    _ = (∑ d ∈ (primorial R).divisors,
          if (d : ℝ) ≤ R then |taoSelbergSieveCoefficient R hR d| else 0) * E := by
      rw [Finset.sum_mul]
    _ ≤ ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
      exact mul_le_mul_of_nonneg_right
        (sum_abs_taoSelbergSieveCoefficient_le R hR) hE

/-- Prefix-sum version of the Selberg off-diagonal estimate. -/
theorem norm_sum_Ioc_taoSelbergDivisorWeight_mul_le_of_prefix
    (R X : ℕ) (hR : 1 ≤ R) (f : ℕ → ℂ) (E : ℝ)
    (hE : 0 ≤ E)
    (hprefix : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ m ∈ Finset.Ioc 0 (X / d), f (m * d)‖ ≤ E) :
    ‖∑ n ∈ Finset.Ioc 0 X,
        (taoSelbergDivisorWeight R hR n : ℂ) * f n‖ ≤
      ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
  apply norm_sum_Ioc_taoSelbergDivisorWeight_mul_le R X hR f E hE
  intro d hd hdLevel
  have hd0 : d ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Sieve.primorial_squarefree R).ne_zero
      (Nat.dvd_of_mem_divisors hd)
  rw [sum_Ioc_ite_dvd_eq_sum_mul d X hd0 f]
  exact hprefix d hd hdLevel

/-- Exact reduction of a Selberg-weighted character Gram entry to a positive
interval correlation. -/
theorem finiteWeightedGram_conj_character_eq_selbergCorrelation
    {κ : Type*} [DecidableEq κ]
    (R N : ℕ) (hR : 1 ≤ R) (χ : κ → ℕ → ℂ) (j k : κ) :
    finiteWeightedGram (Finset.range N) (taoSelbergBHMWeight R hR)
        (fun a n ↦ conj (χ a n)) j k =
      ∑ n ∈ Finset.Ioc 0 (N - 1),
        (taoSelbergDivisorWeight R hR n : ℂ) *
          (χ j n * conj (χ k n)) := by
  unfold finiteWeightedGram finiteWeightedPairing
  simp only [starRingEnd_self_apply]
  calc
    (∑ n ∈ Finset.range N,
        (taoSelbergBHMWeight R hR n : ℂ) * χ j n * conj (χ k n)) =
        ∑ n ∈ Finset.range N,
          (taoSelbergBHMWeight R hR n : ℂ) *
            (χ j n * conj (χ k n)) := by
      apply sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ Finset.Ioc 0 (N - 1),
        (taoSelbergDivisorWeight R hR n : ℂ) *
          (χ j n * conj (χ k n)) :=
      sum_range_taoSelbergBHMWeight_mul_eq_Ioc R N hR _

/-- The concrete Selberg weight supplies the diagonal Gram bound directly
from its explicit mass estimate. -/
theorem norm_selbergWeightedGram_self_le
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 < R) (χ : κ → ℕ → ℂ) (j : κ)
    (hχ : ∀ n, ‖χ j n‖ ≤ 1) :
    ‖finiteWeightedGram (Finset.range (2 * Z))
        (taoSelbergBHMWeight R hR.le)
        (fun a n ↦ conj (χ a n)) j j‖ ≤
      ((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3 := by
  calc
    ‖finiteWeightedGram (Finset.range (2 * Z))
        (taoSelbergBHMWeight R hR.le)
        (fun a n ↦ conj (χ a n)) j j‖ ≤
        ∑ n ∈ Finset.range (2 * Z), taoSelbergBHMWeight R hR.le n := by
      apply norm_finiteWeightedGram_self_le_mass
      · intro n hn
        exact taoSelbergBHMWeight_nonneg R hR.le n
      · intro n hn
        simpa using hχ n
    _ ≤ ∑ n ∈ Finset.Ioc 0 (2 * Z),
        taoSelbergDivisorWeight R hR.le n := by
      rw [sum_range_taoSelbergBHMWeight_eq_Ioc]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [mem_Ioc] at hn ⊢
        omega
      · intro n hnIoc hnFilter
        exact taoSelbergDivisorWeight_nonneg R hR.le n
    _ ≤ ((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3 :=
      sum_taoSelbergDivisorWeight_Ioc_le R (2 * Z) hR

/-- The only input needed to bound an off-diagonal Selberg-weighted Gram entry
is a uniform bound for the ordinary divisor-restricted correlations. -/
theorem norm_selbergWeightedGram_le_of_divisorCorrelations
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 ≤ R) (χ : κ → ℕ → ℂ) (j k : κ) (E : ℝ)
    (hE : 0 ≤ E)
    (hcorr : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ n ∈ Finset.Ioc 0 (2 * Z - 1),
          if d ∣ n then χ j n * conj (χ k n) else 0‖ ≤ E) :
    ‖finiteWeightedGram (Finset.range (2 * Z))
        (taoSelbergBHMWeight R hR)
        (fun a n ↦ conj (χ a n)) j k‖ ≤
      ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
  rw [finiteWeightedGram_conj_character_eq_selbergCorrelation]
  exact norm_sum_Ioc_taoSelbergDivisorWeight_mul_le R (2 * Z - 1)
    hR (fun n ↦ χ j n * conj (χ k n)) E hE hcorr

/-- Ordinary-prefix formulation of the off-diagonal Gram estimate, ready for
a Burgess character-sum bound after multiplicativity removes the factor `d`. -/
theorem norm_selbergWeightedGram_le_of_prefixCorrelations
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 ≤ R) (χ : κ → ℕ → ℂ) (j k : κ) (E : ℝ)
    (hE : 0 ≤ E)
    (hprefix : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
          χ j (m * d) * conj (χ k (m * d))‖ ≤ E) :
    ‖finiteWeightedGram (Finset.range (2 * Z))
        (taoSelbergBHMWeight R hR)
        (fun a n ↦ conj (χ a n)) j k‖ ≤
      ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
  rw [finiteWeightedGram_conj_character_eq_selbergCorrelation]
  exact norm_sum_Ioc_taoSelbergDivisorWeight_mul_le_of_prefix
    R (2 * Z - 1) hR (fun n ↦ χ j n * conj (χ k n)) E hE hprefix

/-- For pointwise multiplicative, norm-one sequences, it suffices to bound the
unshifted prefix correlation.  The value at the extracted divisor contributes
a scalar of norm at most one. -/
theorem norm_selbergWeightedGram_le_of_baseCorrelations
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 ≤ R) (χ : κ → ℕ → ℂ) (j k : κ) (E : ℝ)
    (hE : 0 ≤ E)
    (hnormj : ∀ n, ‖χ j n‖ ≤ 1)
    (hnormk : ∀ n, ‖χ k n‖ ≤ 1)
    (hmulj : ∀ m d, χ j (m * d) = χ j m * χ j d)
    (hmulk : ∀ m d, χ k (m * d) = χ k m * χ k d)
    (hbase : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
          χ j m * conj (χ k m)‖ ≤ E) :
    ‖finiteWeightedGram (Finset.range (2 * Z))
        (taoSelbergBHMWeight R hR)
        (fun a n ↦ conj (χ a n)) j k‖ ≤
      ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
  apply norm_selbergWeightedGram_le_of_prefixCorrelations
    R Z hR χ j k E hE
  intro d hd hdLevel
  have hscalar : ‖χ j d * conj (χ k d)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ (hnormj d) (norm_nonneg _) (hnormk d)
  calc
    ‖∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
        χ j (m * d) * conj (χ k (m * d))‖ =
        ‖(χ j d * conj (χ k d)) *
          ∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
            χ j m * conj (χ k m)‖ := by
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [hmulj, hmulk, map_mul]
      ring
    _ ≤ 1 * E := by
      rw [norm_mul]
      exact mul_le_mul hscalar (hbase d hd hdLevel) (norm_nonneg _) (by norm_num)
    _ = E := one_mul E

/-- Source-shaped normalized BHM estimate with the concrete Selberg weight.
Everything except the divisor-restricted off-diagonal character-sum bound is
now discharged explicitly. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_selberg
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 < R) (hRZ : R < Z)
    (W : Finset κ) (χ : κ → ℕ → ℂ) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hχ : ∀ j ∈ W, ∀ n, ‖χ j n‖ ≤ 1)
    (hcorr : ∀ j ∈ W, ∀ k ∈ W, k ≠ j →
      ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
        ‖∑ n ∈ Finset.Ioc 0 (2 * Z - 1),
            if d ∣ n then χ j n * conj (χ k n) else 0‖ ≤ E) :
    ∑ j ∈ W, ‖finiteNormalizedPrimeBandSum Z (χ j)‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hR
  have hD :
      0 ≤ ((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3 := by
    positivity
  have hOff :
      0 ≤ ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
    positivity
  apply sum_finiteNormalizedPrimeBandSum_sq_le_diagonal_add_offDiagonal_div
    Z W (taoSelbergBHMWeight R hR.le) χ
      (((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3)
      (((R : ℝ) * (1 + Real.log R) ^ 3) * E)
      hZ
  · intro n hn
    exact taoSelbergBHMWeight_nonneg R hR.le n
  · exact taoSelbergBHMWeight_eq_one_on_dyadicPrimeBand hR.le hRZ
  · exact hD
  · exact hOff
  · intro j hj
    exact norm_selbergWeightedGram_self_le R Z hR χ j (hχ j hj)
  · intro j hj k hk hkj
    exact norm_selbergWeightedGram_le_of_divisorCorrelations
      R Z hR.le χ j k E hE (hcorr j hj k hk hkj)

/-- Final reduction to unshifted prefix correlations.  This is the exact
finite interface at which the Burgess estimate enters Tao's Lemma 5.1. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_selberg_of_baseCorrelations
    {κ : Type*} [DecidableEq κ]
    (R Z : ℕ) (hR : 1 < R) (hRZ : R < Z)
    (W : Finset κ) (χ : κ → ℕ → ℂ) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hχ : ∀ j ∈ W, ∀ n, ‖χ j n‖ ≤ 1)
    (hmul : ∀ j ∈ W, ∀ m d, χ j (m * d) = χ j m * χ j d)
    (hbase : ∀ j ∈ W, ∀ k ∈ W, k ≠ j →
      ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
        ‖∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
            χ j m * conj (χ k m)‖ ≤ E) :
    ∑ j ∈ W, ‖finiteNormalizedPrimeBandSum Z (χ j)‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hR
  have hD :
      0 ≤ ((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3 := by
    positivity
  have hOff :
      0 ≤ ((R : ℝ) * (1 + Real.log R) ^ 3) * E := by
    positivity
  apply sum_finiteNormalizedPrimeBandSum_sq_le_diagonal_add_offDiagonal_div
    Z W (taoSelbergBHMWeight R hR.le) χ
      (((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3)
      (((R : ℝ) * (1 + Real.log R) ^ 3) * E)
      hZ
  · intro n hn
    exact taoSelbergBHMWeight_nonneg R hR.le n
  · exact taoSelbergBHMWeight_eq_one_on_dyadicPrimeBand hR.le hRZ
  · exact hD
  · exact hOff
  · intro j hj
    exact norm_selbergWeightedGram_self_le R Z hR χ j (hχ j hj)
  · intro j hj k hk hkj
    exact norm_selbergWeightedGram_le_of_baseCorrelations
      R Z hR.le χ j k E hE (hχ j hj) (hχ k hk)
        (hmul j hj) (hmul k hk) (hbase j hj k hk hkj)

end

end Tao2026
