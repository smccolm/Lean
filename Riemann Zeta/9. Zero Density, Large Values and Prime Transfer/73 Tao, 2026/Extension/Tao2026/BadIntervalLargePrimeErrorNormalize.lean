import Tao2026.BadIntervalLargePrimeExceptionalPairCard

/-!
# Finite normalization of the large-prime error terms

This module exposes the three coordinate aggregates hidden in the improved
one- and two-prime errors, and bounds the literal errors uniformly on dyadic
modulus bands.  It is the algebraic interface between the character estimates
and the source-scale asymptotic comparisons in Propositions 6.7 and 6.8.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Principal-character collision mass over all tuple coordinates. -/
def taoPrimeTupleBandReciprocalSum (P : Fin 1001 → ℕ) : ℝ :=
  ∑ j : Fin 1001, ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹

/-- Unexceptional nonprincipal eighth-power scale mass. -/
def taoPrimeTupleEighthPowerSum (P : Fin 1001 → ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.erase (0 : Fin 1001), (P j : ℝ) ^ (-(8 : ℝ))

/-- Change-level collision mass in the product-modulus estimate. -/
def taoPrimeTupleChangeLevelCollisionSum (P : Fin 1001 → ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
    (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^ (1000 : ℕ)

theorem taoPrimeTupleBandReciprocalSum_nonneg (P : Fin 1001 → ℕ) :
    0 ≤ taoPrimeTupleBandReciprocalSum P := by
  unfold taoPrimeTupleBandReciprocalSum
  positivity

theorem taoPrimeTupleEighthPowerSum_nonneg (P : Fin 1001 → ℕ) :
    0 ≤ taoPrimeTupleEighthPowerSum P := by
  unfold taoPrimeTupleEighthPowerSum
  positivity

theorem taoPrimeTupleChangeLevelCollisionSum_nonneg (P : Fin 1001 → ℕ) :
    0 ≤ taoPrimeTupleChangeLevelCollisionSum P := by
  unfold taoPrimeTupleChangeLevelCollisionSum
  positivity

theorem natCast_div_totient_le_two_of_prime
    {p : ℕ} (hp : Nat.Prime p) :
    (p : ℝ) / (p.totient : ℝ) ≤ 2 := by
  rw [Nat.totient_prime hp]
  have hpos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  rw [div_le_iff₀ hpos]
  have hpTwo := hp.two_le
  exact_mod_cast (by omega : p ≤ 2 * (p - 1))

theorem one_div_totient_mul_le_four_div_dyadicStarts
    {R S p q : ℕ} (hR : 2 ≤ R) (hS : 2 ≤ S)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpR : p ∈ taoDyadicPrimeBand R)
    (hqS : q ∈ taoDyadicPrimeBand S) :
    1 / ((p * q).totient : ℝ) ≤ 4 / ((R : ℝ) * (S : ℝ)) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hpBound := one_div_totient_le_two_div_dyadicStart
    hR hp (mem_taoDyadicPrimeBand.mp hpR).2.1
  have hqBound := one_div_totient_le_two_div_dyadicStart
    hS hq (mem_taoDyadicPrimeBand.mp hqS).2.1
  rw [Nat.totient_mul hcop]
  push_cast
  rw [show 1 / ((p.totient : ℝ) * (q.totient : ℝ)) =
      (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) by ring]
  calc
    (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) ≤
        (2 / (R : ℝ)) * (2 / (S : ℝ)) := by
      exact mul_le_mul hpBound hqBound (by positivity) (by positivity)
    _ = 4 / ((R : ℝ) * (S : ℝ)) := by ring

theorem natCast_mul_div_totient_mul_le_four
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ) ≤ 4 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hpBound := natCast_div_totient_le_two_of_prime hp
  have hqBound := natCast_div_totient_le_two_of_prime hq
  rw [Nat.totient_mul hcop]
  push_cast
  rw [show ((p : ℝ) * (q : ℝ)) /
      ((p.totient : ℝ) * (q.totient : ℝ)) =
      ((p : ℝ) / (p.totient : ℝ)) *
        ((q : ℝ) / (q.totient : ℝ)) by ring]
  calc
    ((p : ℝ) / (p.totient : ℝ)) *
        ((q : ℝ) / (q.totient : ℝ)) ≤ 2 * 2 :=
      mul_le_mul hpBound hqBound
        (by positivity : 0 ≤ (q : ℝ) / (q.totient : ℝ)) (by norm_num)
    _ = 4 := by norm_num

/-- Uniform one-prime error after replacing the two coordinate aggregates by
majorants `U` and `V`. -/
theorem taoLargePrimeImprovedError_le_aggregate
    (P : Fin 1001 → ℕ) {R p : ℕ} (hR : 2 ≤ R)
    (hp : p ∈ taoDyadicPrimeBand R) (U V : ℝ)
    (hU : taoPrimeTupleBandReciprocalSum P ≤ U)
    (hV : taoPrimeTupleEighthPowerSum P ≤ V) :
    taoLargePrimeImprovedError P p ≤ 2 / (R : ℝ) * U + V := by
  have hpData := mem_taoDyadicPrimeBand.mp hp
  have htotient : (0 : ℝ) < (p.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hpData.1.pos
  have hphi := one_div_totient_le_two_div_dyadicStart
    hR hpData.1 hpData.2.1
  rw [taoLargePrimeImprovedError]
  change (p.totient : ℝ)⁻¹ *
      (taoPrimeTupleBandReciprocalSum P +
        (p.totient : ℝ) * taoPrimeTupleEighthPowerSum P) ≤ _
  rw [mul_add]
  have hcancel : (p.totient : ℝ)⁻¹ *
      ((p.totient : ℝ) * taoPrimeTupleEighthPowerSum P) =
      taoPrimeTupleEighthPowerSum P := by
    field_simp
  rw [hcancel]
  exact add_le_add
    (mul_le_mul (by simpa only [one_div] using hphi) hU
      (taoPrimeTupleBandReciprocalSum_nonneg P)
      (by positivity)) hV

/-- Uniform two-prime joint error after replacing its three coordinate
aggregates by `U`, `V`, and `W`. -/
theorem taoLargePrimeJointImprovedError_le_aggregate
    (P : Fin 1001 → ℕ) {R S p q : ℕ} (hR : 2 ≤ R) (hS : 2 ≤ S)
    (hp : p ∈ taoDyadicPrimeBand R) (hq : q ∈ taoDyadicPrimeBand S)
    (hpq : p ≠ q) (U V W : ℝ)
    (hU : taoPrimeTupleBandReciprocalSum P ≤ U)
    (hV : taoPrimeTupleEighthPowerSum P ≤ V)
    (hW : taoPrimeTupleChangeLevelCollisionSum P ≤ W) :
    taoLargePrimeJointImprovedError P p q ≤
      (4 / ((R : ℝ) * (S : ℝ))) * (2 * U) +
        (2 : ℝ) ^ 999 * (4 * V + W) := by
  have hpData := mem_taoDyadicPrimeBand.mp hp
  have hqData := mem_taoDyadicPrimeBand.mp hq
  have hcop : Nat.Coprime p q :=
    (Nat.coprime_primes hpData.1 hqData.1).2 hpq
  have htotient : (0 : ℝ) < ((p * q).totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hpData.1.pos hqData.1.pos)
  have hinv := one_div_totient_mul_le_four_div_dyadicStarts
    hR hS hpData.1 hqData.1 hpq hp hq
  have hratio := natCast_mul_div_totient_mul_le_four
    hpData.1 hqData.1 hpq
  rw [taoLargePrimeJointImprovedError]
  change ((p * q).totient : ℝ)⁻¹ *
      (2 * taoPrimeTupleBandReciprocalSum P +
        (2 : ℝ) ^ 999 *
          (((p * q : ℕ) : ℝ) * taoPrimeTupleEighthPowerSum P +
            ((p * q).totient : ℝ) *
              taoPrimeTupleChangeLevelCollisionSum P)) ≤ _
  have hrewrite : ((p * q).totient : ℝ)⁻¹ *
      (2 * taoPrimeTupleBandReciprocalSum P +
        (2 : ℝ) ^ 999 *
          (((p * q : ℕ) : ℝ) * taoPrimeTupleEighthPowerSum P +
            ((p * q).totient : ℝ) *
              taoPrimeTupleChangeLevelCollisionSum P)) =
      ((p * q).totient : ℝ)⁻¹ *
          (2 * taoPrimeTupleBandReciprocalSum P) +
        (2 : ℝ) ^ 999 *
          ((((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ)) *
              taoPrimeTupleEighthPowerSum P +
            taoPrimeTupleChangeLevelCollisionSum P) := by
    field_simp
  rw [hrewrite]
  have htwice : 2 * taoPrimeTupleBandReciprocalSum P ≤ 2 * U := by
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  have hfirst : ((p * q).totient : ℝ)⁻¹ *
      (2 * taoPrimeTupleBandReciprocalSum P) ≤
      (4 / ((R : ℝ) * (S : ℝ))) * (2 * U) := by
    have htwiceNonneg : 0 ≤ 2 * taoPrimeTupleBandReciprocalSum P :=
      mul_nonneg (by norm_num) (taoPrimeTupleBandReciprocalSum_nonneg P)
    have hfactorNonneg : 0 ≤ 4 / ((R : ℝ) * (S : ℝ)) := by
      positivity
    exact mul_le_mul (by simpa only [one_div] using hinv) htwice
      htwiceNonneg hfactorNonneg
  have hratioTerm :
      (((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ)) *
          taoPrimeTupleEighthPowerSum P ≤
        4 * V := by
    exact mul_le_mul hratio hV (taoPrimeTupleEighthPowerSum_nonneg P)
      (by norm_num)
  have hsecond : (2 : ℝ) ^ 999 *
      ((((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ)) *
          taoPrimeTupleEighthPowerSum P +
        taoPrimeTupleChangeLevelCollisionSum P) ≤
      (2 : ℝ) ^ 999 * (4 * V + W) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add hratioTerm hW) (by positivity)
  exact add_le_add hfirst hsecond

/-- The covariance error inherits dyadic uniform bounds from the joint and
marginal errors, with no hidden constants. -/
theorem taoLargePrimeCovarianceImprovedError_le_of_uniform
    (P : Fin 1001 → ℕ) {R S p q : ℕ} (hR : 2 ≤ R) (hS : 2 ≤ S)
    (hp : p ∈ taoDyadicPrimeBand R) (hq : q ∈ taoDyadicPrimeBand S)
    (E₁ E₂ J : ℝ) (hE₁ : 0 ≤ E₁)
    (hpError : taoLargePrimeImprovedError P p ≤ E₁)
    (hqError : taoLargePrimeImprovedError P q ≤ E₂)
    (hJoint : taoLargePrimeJointImprovedError P p q ≤ J) :
    taoLargePrimeCovarianceImprovedError P p q ≤
      J + (2 / (R : ℝ)) * E₂ + (2 / (S : ℝ)) * E₁ + E₁ * E₂ := by
  have hpData := mem_taoDyadicPrimeBand.mp hp
  have hqData := mem_taoDyadicPrimeBand.mp hq
  have hpInv := one_div_totient_le_two_div_dyadicStart
    hR hpData.1 hpData.2.1
  have hqInv := one_div_totient_le_two_div_dyadicStart
    hS hqData.1 hqData.2.1
  have hpErrorNonneg : 0 ≤ taoLargePrimeImprovedError P p := by
    unfold taoLargePrimeImprovedError
    positivity
  have hqErrorNonneg : 0 ≤ taoLargePrimeImprovedError P q := by
    unfold taoLargePrimeImprovedError
    positivity
  have hpTerm : (1 / (p.totient : ℝ)) *
      taoLargePrimeImprovedError P q ≤ (2 / (R : ℝ)) * E₂ :=
    mul_le_mul hpInv hqError hqErrorNonneg (by positivity)
  have hqTerm : (1 / (q.totient : ℝ)) *
      taoLargePrimeImprovedError P p ≤ (2 / (S : ℝ)) * E₁ :=
    mul_le_mul hqInv hpError hpErrorNonneg (by positivity)
  have hproduct : taoLargePrimeImprovedError P p *
      taoLargePrimeImprovedError P q ≤ E₁ * E₂ :=
    mul_le_mul hpError hqError hqErrorNonneg hE₁
  unfold taoLargePrimeCovarianceImprovedError
  exact add_le_add (add_le_add (add_le_add hJoint hpTerm) hqTerm) hproduct

end

end Tao2026
