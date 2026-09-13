import Tao2026.BadIntervalLargePrimeExceptionalPartition

/-!
# Dyadic first-moment block summation

This module turns the exact exceptional partition into the finite dyadic
first-moment estimate used in Proposition 6.7.  It records the precise
identification of a source half-open prime band with the general anti-sieve
range, bounds the reciprocal-totient main term, and retains separate uniform
majorants for the improved and exceptional errors.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

theorem taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand
    {R : ℕ} (hR : 0 < R) :
    taoLargeAntiSievePrimeRange (R - 1) (2 * R - 1) =
      taoDyadicPrimeBand R := by
  ext p
  simp only [mem_taoLargeAntiSievePrimeRange, mem_taoDyadicPrimeBand]
  constructor <;> rintro ⟨hp, h₁, h₂⟩ <;> refine ⟨hp, ?_, ?_⟩ <;> omega

theorem one_div_totient_le_two_div_dyadicStart
    {R p : ℕ} (hR : 2 ≤ R) (hp : Nat.Prime p) (hRp : R ≤ p) :
    1 / (p.totient : ℝ) ≤ 2 / (R : ℝ) := by
  rw [Nat.totient_prime hp]
  have hposNat : 0 < p - 1 := by omega
  have hpos : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hposNat
  have hRpos : (0 : ℝ) < R := by positivity
  apply (div_le_div_iff₀ hpos hRpos).2
  norm_num
  exact_mod_cast (by omega : R ≤ 2 * (p - 1))

theorem sum_dyadicPrimeBand_one_div_totient_le
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) ≤
      ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ)) := by
  have hsum := Finset.sum_le_card_nsmul (taoDyadicPrimeBand R)
    (fun p => 1 / (p.totient : ℝ)) (2 / (R : ℝ)) (by
      intro p hp
      have hpData := mem_taoDyadicPrimeBand.mp hp
      exact one_div_totient_le_two_div_dyadicStart hR hpData.1 hpData.2.1)
  simpa [nsmul_eq_mul] using hsum

/-- PNT upper envelope complementary to the lower envelope used to normalize
the prime-tuple coordinate laws. -/
theorem eventually_card_taoDyadicPrimeBand_le_two_mul_div_log :
    ∀ᶠ R : ℕ in atTop,
      ((taoDyadicPrimeBand R).card : ℝ) ≤
        2 * ((R : ℝ) / Real.log R) := by
  let g : ℕ → ℝ := fun R => (R : ℝ) / Real.log R
  rcases card_taoDyadicPrimeBand_asymptotic.exists_eq_mul with ⟨φ, hφ, heq⟩
  have hφUpper : ∀ᶠ R : ℕ in atTop, φ R < (2 : ℝ) :=
    hφ.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [heq, hφUpper, eventually_ge_atTop (2 : ℕ)] with R hEq hφR hR
  have hg : 0 ≤ g R := by
    dsimp [g]
    positivity
  calc
    ((taoDyadicPrimeBand R).card : ℝ) = φ R * g R := hEq
    _ ≤ 2 * g R := mul_le_mul_of_nonneg_right hφR.le hg
    _ = 2 * ((R : ℝ) / Real.log R) := rfl

theorem eventually_sum_dyadicPrimeBand_one_div_totient_le_four_div_log :
    ∀ᶠ R : ℕ in atTop,
      (∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) ≤
        4 / Real.log R := by
  filter_upwards [eventually_card_taoDyadicPrimeBand_le_two_mul_div_log,
    eventually_ge_atTop (2 : ℕ)] with R hcard hR
  have hsum := sum_dyadicPrimeBand_one_div_totient_le hR
  have hRpos : (0 : ℝ) < R := by positivity
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  calc
    (∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) ≤
        ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ)) := hsum
    _ ≤ (2 * ((R : ℝ) / Real.log R)) * (2 / (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 / Real.log R := by field_simp; ring

theorem card_taoLargeAntiSieveIndices_filter_second_dyadic
    (R H : ℕ) (hR : 0 < R) (E : Finset ℕ) :
    ((taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H).filter
      (fun a => a.2 ∈ E)).card =
      (H - 1) * ((taoDyadicPrimeBand R).filter (fun p => p ∈ E)).card := by
  have hrange := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hR
  have heq :
      ((Finset.Ico 1 H).product (taoDyadicPrimeBand R)).filter
          (fun a => a.2 ∈ E) =
        (Finset.Ico 1 H).product
          ((taoDyadicPrimeBand R).filter (fun p => p ∈ E)) := by
    ext a
    simp [and_assoc]
  rw [taoLargeAntiSieveIndices, hrange, heq]
  simp

private theorem sum_taoLargeDyadicIndex_majorant_eq
    (R H : ℕ) (hR : 0 < R) (Eset : Finset ℕ)
    (f : ℕ → ℝ) (A B : ℝ) :
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      (f a.2 + A + if a.2 ∈ Eset then B else 0)) =
      (H - 1 : ℕ) *
        ((∑ p ∈ taoDyadicPrimeBand R, f p) +
          ((taoDyadicPrimeBand R).card : ℝ) * A +
          (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B) := by
  have hrange := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hR
  rw [taoLargeAntiSieveIndices, hrange]
  rw [show (∑ a ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand R),
      (f a.2 + A + if a.2 ∈ Eset then B else 0)) =
      ∑ l ∈ Finset.Ico 1 H, ∑ p ∈ taoDyadicPrimeBand R,
        (f p + A + if p ∈ Eset then B else 0) by
    exact Finset.sum_product _ _ _]
  simp only [Finset.sum_add_distrib]
  simp
  have hinter : taoDyadicPrimeBand R ∩ Eset =
      (taoDyadicPrimeBand R).filter (fun p => p ∈ Eset) := by ext; simp
  rw [hinter]
  ring

/-- Exact finite dyadic first-moment estimate.  `A` bounds every improved
error, `B` bounds every exceptional probability, and `K` bounds the number of
exceptional primes in the dyadic block. -/
theorem sum_taoLargePrimeProbability_dyadicBlock_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (R H m' : ℕ) (hR : 2 ≤ R) (hH : H ≤ R - 1)
    (hm : ∀ p ∈ taoDyadicPrimeBand R, Nat.Coprime m' p)
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hImproved : ∀ p ∈ taoDyadicPrimeBand R,
      taoLargePrimeImprovedError P p ≤ A)
    (hExceptionalCard :
      (((taoDyadicPrimeBand R).filter fun p =>
        p ∈ taoLargePrimeExceptionalConductorsFor (taoDyadicPrimeBand R) P).card : ℝ) ≤ K)
    (hExceptional : ∀ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      a.2 ∈ taoLargePrimeExceptionalConductorsFor (taoDyadicPrimeBand R) P →
      taoLargePrimeProbability P hP m' a ≤ B) :
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      taoLargePrimeProbability P hP m' a) ≤
      (H - 1 : ℕ) *
        (((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B) := by
  have hRpos : 0 < R := by omega
  have hrange := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hRpos
  let Eset := taoLargePrimeExceptionalConductorsFor (taoDyadicPrimeBand R) P
  have hpart := sum_taoLargePrimeProbability_le_exceptionalPartition
    P hP (R - 1) (2 * R - 1) H m' hH
      (by simpa only [hrange] using hm)
      (fun _ => B) (by
        intro a ha haE
        exact hExceptional a ha (by simpa only [hrange, Eset] using haE))
  have hpointwise :
      (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        if a.2 ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange (R - 1) (2 * R - 1)) P then B
        else 1 / (a.2.totient : ℝ) + taoLargePrimeImprovedError P a.2) ≤
      ∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        (1 / (a.2.totient : ℝ) + A + if a.2 ∈ Eset then B else 0) := by
    apply Finset.sum_le_sum
    intro a ha
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have haBand : a.2 ∈ taoDyadicPrimeBand R := by
      rw [← hrange]
      exact mem_taoLargeAntiSievePrimeRange.mpr
        ⟨haData.2.2.1, haData.2.2.2.1, haData.2.2.2.2⟩
    have herr := hImproved a.2 haBand
    have heq :
        (a.2 ∈ taoLargePrimeExceptionalConductorsFor
          (taoLargeAntiSievePrimeRange (R - 1) (2 * R - 1)) P) ↔
        a.2 ∈ Eset := by rw [hrange]
    by_cases haE : a.2 ∈ Eset
    · rw [if_pos (heq.mpr haE), if_pos haE]
      have hmain : 0 ≤ 1 / (a.2.totient : ℝ) := by positivity
      nlinarith
    · rw [if_neg (fun h => haE (heq.mp h)), if_neg haE, add_zero]
      linarith
  have hmajorant := sum_taoLargeDyadicIndex_majorant_eq R H hRpos Eset
    (fun p => 1 / (p.totient : ℝ)) A B
  have hmain := sum_dyadicPrimeBand_one_div_totient_le hR
  have hcardNonneg : 0 ≤ ((taoDyadicPrimeBand R).card : ℝ) := by positivity
  have hExc :
      (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B ≤ K * B :=
    mul_le_mul_of_nonneg_right (by simpa only [Eset] using hExceptionalCard) hB
  calc
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        taoLargePrimeProbability P hP m' a) ≤ _ := hpart
    _ ≤ ∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        (1 / (a.2.totient : ℝ) + A + if a.2 ∈ Eset then B else 0) := hpointwise
    _ = (H - 1 : ℕ) *
        ((∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) +
          ((taoDyadicPrimeBand R).card : ℝ) * A +
          (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B) := hmajorant
    _ ≤ (H - 1 : ℕ) *
        (((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) +
              ((taoDyadicPrimeBand R).card : ℝ) * A +
              (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B ≤
            ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ)) +
              ((taoDyadicPrimeBand R).card : ℝ) * A + K * B := by
          exact add_le_add (add_le_add hmain (le_refl _)) hExc
        _ = ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B := by
          ring

end

end Tao2026
