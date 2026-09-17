import Tao2026.LowFrequencyPNT
import Tao2026.PrimeSourceBlock

/-!
# Prime-power removal in the low-frequency normalization

The low-frequency PNT branch naturally produces the weight `Λ(n) / log n`.
On primes this weight is exactly one.  This module separates the higher prime
powers, bounds them by the frozen local prime-power estimate, and reaches the
literal unweighted prime reciprocal-phase sum.
-/

open Complex Finset Filter Set
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace Tao2026

noncomputable section

/-- Higher-prime-power tail after dividing the Mangoldt weight by `log n`. -/
def primePowerTailLogWeightedReciprocalPhaseSum
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ s.filter (fun n => ¬n.Prime),
    standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
      Real.log n

/-- Exact prime/higher-prime-power split in the `Λ / log` normalization. -/
theorem mangoldtLogWeightedReciprocalPhaseSum_eq_prime_add_tail
    (a b : ℕ) (N M : ℝ) (j : ℕ) :
    mangoldtLogWeightedReciprocalPhaseSum N M j a b =
      primeReciprocalPhaseSum a b N M j +
        primePowerTailLogWeightedReciprocalPhaseSum
          (Finset.Ico a b) N M j := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ico a b) Nat.Prime
    (fun n => standardAdditiveCharacter (reciprocalPhase N M j n) *
      (Λ n : ℂ) / Real.log n)
  unfold mangoldtLogWeightedReciprocalPhaseSum
    primePowerTailLogWeightedReciprocalPhaseSum
  rw [primeReciprocalPhaseSum_eq_filter]
  calc
    (∑ n ∈ Finset.Ico a b,
        standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
          Real.log n) =
        (∑ n ∈ (Finset.Ico a b).filter Nat.Prime,
          standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
            Real.log n) +
        ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime),
          standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
            Real.log n := hsplit.symm
    _ = (∑ n ∈ (Finset.Ico a b).filter Nat.Prime,
          standardAdditiveCharacter (reciprocalPhase N M j n)) +
        ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime),
          standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
            Real.log n := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have hnPrime : n.Prime := (Finset.mem_filter.mp hn).2
      have hnTwo : 2 ≤ n := hnPrime.two_le
      have hlog : Real.log (n : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
      rw [ArithmeticFunction.vonMangoldt_apply_prime hnPrime]
      apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hlog)).2
      ring

/-- With zero phase, the ordinary prime-power tail has norm exactly equal to
the non-prime Mangoldt mass. -/
theorem norm_primePowerTailReciprocalPhaseSum_zero_eq
    (s : Finset ℕ) (j : ℕ) :
    ‖primePowerTailReciprocalPhaseSum s 0 0 j‖ =
      ∑ n ∈ s.filter (fun n => ¬n.Prime), Λ n := by
  have hsum : primePowerTailReciprocalPhaseSum s 0 0 j =
      ((∑ n ∈ s.filter (fun n => ¬n.Prime), Λ n : ℝ) : ℂ) := by
    unfold primePowerTailReciprocalPhaseSum
    push_cast
    apply Finset.sum_congr rfl
    intro n _hn
    simp [reciprocalPhase, standardAdditiveCharacter]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
      ArithmeticFunction.vonMangoldt_nonneg)]

/-- Dividing by `log n` costs at most the left-endpoint inverse logarithm in
the higher-prime-power tail. -/
theorem norm_primePowerTailLogWeightedReciprocalPhaseSum_le
    {a b : ℕ} (ha : 2 ≤ a) (N M : ℝ) (j : ℕ) :
    ‖primePowerTailLogWeightedReciprocalPhaseSum
        (Finset.Ico a b) N M j‖ ≤
      (Real.log a)⁻¹ *
        ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime), Λ n := by
  rw [primePowerTailLogWeightedReciprocalPhaseSum]
  calc
    ‖∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime),
        standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
          Real.log n‖ ≤
        ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime),
          ‖standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
            Real.log n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime),
        (Real.log a)⁻¹ * Λ n := by
      apply Finset.sum_le_sum
      intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
      have hnTwo : 2 ≤ n := ha.trans han
      have halog : 0 < Real.log (a : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < a by omega))
      have hnlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlogle : Real.log (a : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < a by omega))
          (by exact_mod_cast han)
      have hinv : (Real.log (n : ℝ))⁻¹ ≤
          (Real.log (a : ℝ))⁻¹ := inv_anti₀ halog hlogle
      have hnorm :
          ‖standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
              Real.log n‖ = (Real.log n)⁻¹ * Λ n := by
        rw [norm_div, norm_mul, norm_standardAdditiveCharacter, one_mul,
          Complex.norm_real, Complex.norm_real]
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          abs_of_pos hnlog, div_eq_mul_inv]
        ring
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hinv
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (Real.log a)⁻¹ *
        ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime), Λ n := by
      rw [Finset.mul_sum]

/-- The `Λ / log` higher-prime-power tail retains every prescribed
logarithmic saving on dyadic intervals. -/
theorem eventually_norm_primePowerTailLogWeightedReciprocalPhaseSum_le_logSaving
    (T : ℝ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N M : ℝ) (j : ℕ),
      P ≤ a → a ≤ b → b ≤ 2 * P →
      ‖primePowerTailLogWeightedReciprocalPhaseSum
          (Finset.Ico a b) N M j‖ ≤
        (P : ℝ) * (Real.log P) ^ (-T) := by
  have htail := eventually_norm_primePowerTailReciprocalPhaseSum_Ico_le_logSaving T
  filter_upwards [htail, eventually_ge_atTop (3 : ℕ)] with P htailP hP3
  intro a b N M j hPa hab hbP
  have ha : 2 ≤ a := by omega
  have hmass := norm_primePowerTailReciprocalPhaseSum_zero_eq
    (Finset.Ico a b) j
  have hweighted := norm_primePowerTailLogWeightedReciprocalPhaseSum_le
    (b := b) ha N M j
  have hlogaOne : (1 : ℝ) ≤ Real.log a := by
    have hlogThree : (1 : ℝ) < Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    have hlogle : Real.log (3 : ℝ) ≤ Real.log (a : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (hP3.trans hPa))
    linarith
  have hinv : (Real.log (a : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hlogaOne
  calc
    ‖primePowerTailLogWeightedReciprocalPhaseSum
        (Finset.Ico a b) N M j‖ ≤
        (Real.log a)⁻¹ *
          ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime), Λ n :=
      hweighted
    _ ≤ ∑ n ∈ (Finset.Ico a b).filter (fun n => ¬n.Prime), Λ n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv
        (Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = ‖primePowerTailReciprocalPhaseSum (Finset.Ico a b) 0 0 j‖ := hmass.symm
    _ ≤ (P : ℝ) * (Real.log P) ^ (-T) :=
      htailP a b 0 0 j hPa hab hbP

/-- Removing higher prime powers transfers a Mangoldt/log-to-integral bound
to the literal unweighted prime sum. -/
theorem norm_primeReciprocalPhaseSum_sub_integral_le_mangoldtLog_add_tail
    (a b : ℕ) (N M : ℝ) (j : ℕ) :
    ‖primeReciprocalPhaseSum a b N M j -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
      ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ +
      ‖primePowerTailLogWeightedReciprocalPhaseSum
        (Finset.Ico a b) N M j‖ := by
  have hsplit := mangoldtLogWeightedReciprocalPhaseSum_eq_prime_add_tail
    a b N M j
  rw [show primeReciprocalPhaseSum a b N M j -
      (∫ t in (a : ℝ)..(b : ℝ),
        standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t) =
      (mangoldtLogWeightedReciprocalPhaseSum N M j a b -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t) -
        primePowerTailLogWeightedReciprocalPhaseSum
          (Finset.Ico a b) N M j by rw [hsplit]; ring]
  exact norm_sub_le _ _

/-- Literal low-frequency prime-minus-integral consequence of the global
quantitative PNT contract.  The final summand is the higher-prime-power tail,
already reduced to an arbitrary logarithmic saving. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_primeReciprocalPhaseSum_sub_integral_le
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    {j : ℕ} (hj : 1 ≤ j) (A : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop, ∀ (N M : ℝ) (a b : ℕ),
      P ≤ a → a < b → b ≤ 2 * P →
      ‖primeReciprocalPhaseSum a b N M j -
          ∫ t in (a : ℝ)..(b : ℝ),
            standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
        (1 / Real.log P +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ A) +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2) +
          P * (Real.log P) ^ (-T) := by
  obtain ⟨C, hC, hmangoldt⟩ :=
    hPNT.eventually_mangoldtLogWeighted_sub_integral_le hj A
  refine ⟨C, hC, ?_⟩
  have htail :=
    eventually_norm_primePowerTailLogWeightedReciprocalPhaseSum_le_logSaving T
  filter_upwards [hmangoldt, htail] with P hmangoldtP htailP
  intro N M a b hPa hab hbP
  calc
    ‖primeReciprocalPhaseSum a b N M j -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
        ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
          ∫ t in (a : ℝ)..(b : ℝ),
            standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ +
        ‖primePowerTailLogWeightedReciprocalPhaseSum
          (Finset.Ico a b) N M j‖ :=
      norm_primeReciprocalPhaseSum_sub_integral_le_mangoldtLog_add_tail
        a b N M j
    _ ≤ ((1 / Real.log P +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ A) +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) +
          P * (Real.log P) ^ (-T) :=
      add_le_add (hmangoldtP N M a b hPa hab hbP)
        (htailP a b N M j hPa hab.le hbP)

end

end Tao2026
