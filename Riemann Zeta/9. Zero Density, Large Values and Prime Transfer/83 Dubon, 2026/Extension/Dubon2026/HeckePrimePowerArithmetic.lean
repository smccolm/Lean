/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

The finite prime-power calculation adapts FourierHecke.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198,
generalized to a completely multiplicative weight, including zero bad-prime weights.
-/
import Dubon2026.HeckeDivisorConvolution

/-! # Prime-power recurrence for the genuine Hecke coefficient transform -/

namespace Dubon2026

open Finset

noncomputable section

private theorem sum_divisors_primePower (w : ℕ →* ℂ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (s n : ℕ) :
    (∑ d ∈ (p ^ s).divisors, w d * c (n / (d * d))) =
      ∑ j ∈ range (s + 1), w (p ^ j) * c (n / (p ^ j * p ^ j)) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

private theorem primePower_range_factor (w : ℕ →* ℂ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (s m r : ℕ) :
    (∑ j ∈ range (s + 1), w (p ^ (j + 1)) *
      c (m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1)))) =
      w p * ∑ j ∈ range (s + 1), w (p ^ j) * c (m * p ^ r / (p ^ j * p ^ j)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show p ^ (j + 1) = p * p ^ j from pow_succ' p j, map_mul, mul_assoc]
  congr 2
  rw [show p * p ^ j * (p * p ^ j) = p * p * (p ^ j * p ^ j) by ring,
    show m * p ^ (r + 2) = p * p * (m * p ^ r) by ring]
  exact congrArg c (Nat.mul_div_mul_left _ _ (Nat.mul_pos hp.pos hp.pos))

private theorem weightedDivisor_primePower_dvd (w : ℕ →* ℂ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (r m : ℕ) (hdvd : p ∣ m) :
    weightedDivisorTransform w (p ^ (r + 1)) c (p * m) +
      w p * weightedDivisorTransform w (p ^ (r + 1)) c (m / p) -
      w p * weightedDivisorTransform w (p ^ r) c m =
        weightedDivisorTransform w (p ^ (r + 2)) c m := by
  have gcd_pm : (p * m).gcd (p ^ (r + 1)) = p * m.gcd (p ^ r) := by
    conv_lhs => rw [pow_succ, mul_comm (p ^ r) p]
    exact Nat.gcd_mul_left p m (p ^ r)
  have gcd_is_ppow : ∀ a v : ℕ, ∃ s, a.gcd (p ^ v) = p ^ s := fun a v =>
    let ⟨s, _, hs⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right a (p ^ v)); ⟨s, hs⟩
  have gcd_m2 : m.gcd (p ^ (r + 2)) = p * (m / p).gcd (p ^ (r + 1)) := by
    conv_lhs => rw [show m = p * (m / p) from (Nat.mul_div_cancel' hdvd).symm,
      show p ^ (r + 2) = p * p ^ (r + 1) by ring]
    exact Nat.gcd_mul_left p (m / p) (p ^ (r + 1))
  obtain ⟨s₁, hs₁⟩ := gcd_is_ppow m r
  obtain ⟨s₂, hs₂⟩ := gcd_is_ppow (m / p) (r + 1)
  unfold weightedDivisorTransform
  rw [gcd_pm, hs₁, gcd_m2, hs₂,
    show p * p ^ s₁ = p ^ (s₁ + 1) from (pow_succ' p s₁).symm,
    show p * p ^ s₂ = p ^ (s₂ + 1) from (pow_succ' p s₂).symm,
    sum_divisors_primePower w hp c (s₁ + 1) (p * m * p ^ (r + 1)),
    sum_divisors_primePower w hp c s₂ (m / p * p ^ (r + 1)),
    sum_divisors_primePower w hp c s₁ (m * p ^ r),
    sum_divisors_primePower w hp c (s₂ + 1) (m * p ^ (r + 2)),
    Finset.sum_range_succ' (fun j => w (p ^ j) * c (p * m * p ^ (r + 1) / (p ^ j * p ^ j))),
    Finset.sum_range_succ' (fun j => w (p ^ j) * c (m * p ^ (r + 2) / (p ^ j * p ^ j)))]
  simp only [pow_zero, map_one, one_mul, Nat.div_one]
  rw [show p * m * p ^ (r + 1) = m * p ^ (r + 2) by ring]
  have h_mp_prod : m / p * p ^ (r + 1) = m * p ^ r := by
    rw [show p ^ (r + 1) = p * p ^ r by ring, ← mul_assoc, Nat.div_mul_cancel hdvd]
  rw [primePower_range_factor w hp c s₁ m r, primePower_range_factor w hp c s₂ m r, h_mp_prod]
  ring

private theorem weightedDivisor_primePower_not_dvd (w : ℕ →* ℂ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (r m : ℕ) (hdvd : ¬p ∣ m) :
    weightedDivisorTransform w (p ^ (r + 1)) c (p * m) -
      w p * weightedDivisorTransform w (p ^ r) c m =
        weightedDivisorTransform w (p ^ (r + 2)) c m := by
  have gcd_pm : (p * m).gcd (p ^ (r + 1)) = p * m.gcd (p ^ r) := by
    conv_lhs => rw [pow_succ, mul_comm (p ^ r) p]
    exact Nat.gcd_mul_left p m (p ^ r)
  have gcd_m : ∀ v, m.gcd (p ^ v) = 1 := fun v => Nat.Prime.coprime_pow_of_not_dvd hp hdvd
  have gcd_pm_eq : (p * m).gcd (p ^ (r + 1)) = p := by rw [gcd_pm, gcd_m r, mul_one]
  unfold weightedDivisorTransform
  rw [gcd_m (r + 2), Nat.divisors_one, Finset.sum_singleton,
    gcd_m r, Nat.divisors_one, Finset.sum_singleton,
    gcd_pm_eq, hp.divisors, Finset.sum_insert (by simp; exact Ne.symm hp.one_lt.ne')]
  simp only [Finset.sum_singleton, map_one, one_mul, Nat.div_one]
  rw [show p * m * p ^ (r + 1) / (p * p) = m * p ^ r by
      rw [show p * m * p ^ (r + 1) = p * p * (m * p ^ r) by ring]
      exact Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos hp.pos),
    show p * m * p ^ (r + 1) = m * p ^ (r + 2) by ring]
  ring

/-- The prime-power Hecke recurrence holds for every multiplicative weight, including zero. -/
theorem weightedDivisorTransform_primePower (w : ℕ →* ℂ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (r m : ℕ) :
    weightedDivisorTransform w (p ^ (r + 1)) c (p * m) +
      w p * (if p ∣ m then weightedDivisorTransform w (p ^ (r + 1)) c (m / p) else 0) -
      w p * weightedDivisorTransform w (p ^ r) c m =
        weightedDivisorTransform w (p ^ (r + 2)) c m := by
  by_cases hdvd : p ∣ m
  · rw [if_pos hdvd]
    exact weightedDivisor_primePower_dvd w hp c r m hdvd
  · rw [if_neg hdvd, mul_zero, add_zero]
    exact weightedDivisor_primePower_not_dvd w hp c r m hdvd

/-- The actual classical transforms satisfy the recurrence at good and bad primes alike. -/
theorem classicalHeckeCoefficient_primePower (Q : ℕ) (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (c : ℕ → ℂ) (r m : ℕ) :
    classicalHeckeCoefficient Q k p (classicalHeckeCoefficient Q k (p ^ (r + 1)) c) m -
      heckeDivisorWeight Q k p * classicalHeckeCoefficient Q k (p ^ r) c m =
        classicalHeckeCoefficient Q k (p ^ (r + 2)) c m := by
  rw [classicalHeckeCoefficient_prime Q k hp]
  simp_rw [classicalHeckeCoefficient_eq_weighted Q k (pow_ne_zero _ hp.ne_zero)]
  have hw : (if Nat.Coprime p Q ∧ p ∣ m then (p : ℂ) ^ (k - 1) *
      weightedDivisorTransform (heckeDivisorWeight Q k) (p ^ (r + 1)) c (m / p) else 0) =
      heckeDivisorWeight Q k p * (if p ∣ m then
        weightedDivisorTransform (heckeDivisorWeight Q k) (p ^ (r + 1)) c (m / p) else 0) := by
    by_cases hc : Nat.Coprime p Q <;> by_cases hd : p ∣ m <;> simp [heckeDivisorWeight, hc, hd]
  rw [hw]
  exact weightedDivisorTransform_primePower _ hp c r m

end
end Dubon2026
