import Tao2026.FundamentalSieveWeights
import Mathlib.NumberTheory.Primorial
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Concrete Selberg upper-bound weights for the prime sieve

This file instantiates the proved Selberg-sieve machinery at the density
`ν(d)=1/d`.  The resulting coefficients are an unconditional alternative to
the `{−1,0,1}` Rosser weights in Tao's Lemma 5.4: they have level support,
coefficient one at `d=1`, and an upper-Möbius (hence nonnegative divisor-sum)
property.  Their real-valued coefficient bound is recorded separately; no
claim that they take only the values `{−1,0,1}` is made.
-/

namespace Tao2026

open Finset
open scoped ArithmeticFunction ArithmeticFunction.omega BigOperators

noncomputable section

/-- A dummy sieve problem whose Selberg coefficients depend only on the level
and on the prime density `ν(d)=1/d`. -/
def taoPrimeSelbergSieve (R : ℕ) (hR : 1 ≤ R) : SelbergSieve where
  support := ∅
  prodPrimes := primorial R
  prodPrimes_squarefree := Sieve.primorial_squarefree R
  weights := fun _ ↦ 0
  weights_nonneg := fun _ ↦ le_rfl
  totalMass := 0
  nu := (ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp [hp.ne_zero]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  level := R
  one_le_level := by exact_mod_cast hR

/-- The concrete Selberg upper-bound coefficient at level `R`. -/
def taoSelbergSieveCoefficient (R : ℕ) (hR : 1 ≤ R) : ℕ → ℝ :=
  SelbergSieve.selbergMuPlus (taoPrimeSelbergSieve R hR)

/-- The Selberg coefficient is supported on the requested level. -/
theorem taoSelbergSieveCoefficient_eq_zero_of_level_lt
    (R : ℕ) (hR : 1 ≤ R) (d : ℕ) (hd : R < d) :
    taoSelbergSieveCoefficient R hR d = 0 := by
  apply (taoPrimeSelbergSieve R hR).selbergμPlus_eq_zero
  change ¬(d : ℝ) ≤ (R : ℝ)
  exact_mod_cast (not_le.mpr hd)

/-- A nonzero Selberg coefficient is supported on the primorial as well as on
the numerical level. -/
theorem taoSelbergSieveCoefficient_eq_zero_of_not_dvd_primorial
    (R : ℕ) (hR : 1 ≤ R) (d : ℕ) (hd : ¬d ∣ primorial R) :
    taoSelbergSieveCoefficient R hR d = 0 := by
  let s := taoPrimeSelbergSieve R hR
  unfold taoSelbergSieveCoefficient SelbergSieve.selbergMuPlus
  rw [SelbergSieve.lambdaSquared]
  apply sum_eq_zero
  intro d₁ hd₁
  apply sum_eq_zero
  intro d₂ hd₂
  split_ifs with heq
  · by_cases hd₁P : d₁ ∣ primorial R
    · have hd₂P : ¬d₂ ∣ primorial R := by
        intro hd₂P
        apply hd
        rw [heq]
        exact Nat.lcm_dvd hd₁P hd₂P
      change
        SelbergSieve.selbergWeights s d₁ *
            SelbergSieve.selbergWeights s d₂ = 0
      rw [s.selbergWeights_eq_zero_of_not_dvd hd₂P, mul_zero]
    · change
        SelbergSieve.selbergWeights s d₁ *
            SelbergSieve.selbergWeights s d₂ = 0
      rw [s.selbergWeights_eq_zero_of_not_dvd hd₁P, zero_mul]
  · rfl

/-- The coefficient at one is exactly one. -/
theorem taoSelbergSieveCoefficient_one (R : ℕ) (hR : 1 ≤ R) :
    taoSelbergSieveCoefficient R hR 1 = 1 := by
  unfold taoSelbergSieveCoefficient SelbergSieve.selbergMuPlus
  rw [SelbergSieve.lambdaSquared]
  simp [(taoPrimeSelbergSieve R hR).weight_one_of_selberg]

/-- These coefficients satisfy the upper-Möbius inequality on every natural
number. -/
theorem taoSelbergSieveCoefficient_isUpperMoebius
    (R : ℕ) (hR : 1 ≤ R) :
    BoundingSieve.IsUpperMoebius (taoSelbergSieveCoefficient R hR) := by
  exact (taoPrimeSelbergSieve R hR).selbergUbSieve.hμPlus

/-- The natural divisor-sum weight attached directly to the Selberg upper
coefficients.  Taking divisors of the gcd includes precisely the divisors
supported on the sieve primorial, including when `n=0`. -/
def taoSelbergDivisorWeight (R : ℕ) (hR : 1 ≤ R) (n : ℕ) : ℝ :=
  ∑ d ∈ (Nat.gcd (primorial R) n).divisors,
    taoSelbergSieveCoefficient R hR d

/-- The concrete Selberg divisor-sum weight is nonnegative everywhere. -/
theorem taoSelbergDivisorWeight_nonneg
    (R : ℕ) (hR : 1 ≤ R) (n : ℕ) :
    0 ≤ taoSelbergDivisorWeight R hR n := by
  have hupper := taoSelbergSieveCoefficient_isUpperMoebius R hR
    (Nat.gcd (primorial R) n)
  unfold taoSelbergDivisorWeight
  by_cases hgcd : Nat.gcd (primorial R) n = 1
  · rw [if_pos hgcd] at hupper
    exact zero_le_one.trans hupper
  · simpa [hgcd] using hupper

/-- The gcd formulation is the finite divisor sum over the sieve primorial. -/
theorem taoSelbergDivisorWeight_eq_sum_primorialDivisors
    (R : ℕ) (hR : 1 ≤ R) (n : ℕ) :
    taoSelbergDivisorWeight R hR n =
      ∑ d ∈ (primorial R).divisors,
        if d ∣ n then taoSelbergSieveCoefficient R hR d else 0 := by
  have hP0 : primorial R ≠ 0 := (Sieve.primorial_squarefree R).ne_zero
  have hgcd0 : Nat.gcd (primorial R) n ≠ 0 := Nat.gcd_ne_zero_left hP0
  unfold taoSelbergDivisorWeight
  rw [← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hdgcd, _⟩
    have hd := Nat.dvd_gcd_iff.mp hdgcd
    exact ⟨⟨hd.1, hP0⟩, hd.2⟩
  · rintro ⟨⟨hdP, _⟩, hdn⟩
    exact ⟨Nat.dvd_gcd hdP hdn, hgcd0⟩

/-- Above the sieve level the concrete Selberg divisor-sum weight is exactly
one on primes. -/
theorem taoSelbergDivisorWeight_prime_eq_one
    (R : ℕ) (hR : 1 ≤ R) {p : ℕ} (hp : Nat.Prime p) (hRp : R < p) :
    taoSelbergDivisorWeight R hR p = 1 := by
  have hnot : ¬p ∣ primorial R := by
    rw [Sieve.prime_dvd_primorial_iff R p hp]
    exact not_le.mpr hRp
  have hcop : Nat.Coprime (primorial R) p :=
    (hp.coprime_iff_not_dvd.mpr hnot).symm
  unfold taoSelbergDivisorWeight
  rw [hcop.gcd_eq_one]
  simp [taoSelbergSieveCoefficient_one R hR]

/-- Dyadic-prime specialization used by the weighted BHM argument. -/
theorem taoSelbergDivisorWeight_eq_one_on_dyadicPrimeBand
    {R Z : ℕ} (hR : 1 ≤ R) (hRZ : R < Z) :
    ∀ p ∈ taoDyadicPrimeBand Z, taoSelbergDivisorWeight R hR p = 1 := by
  intro p hp
  have hpData := mem_taoDyadicPrimeBand.mp hp
  exact taoSelbergDivisorWeight_prime_eq_one R hR hpData.1
    (hRZ.trans_le hpData.2.1)

/-- Exact mass expansion for the concrete Selberg divisor weight. -/
theorem sum_taoSelbergDivisorWeight_Ioc_eq
    (R X : ℕ) (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR n) =
      ∑ d ∈ (primorial R).divisors,
        (X / d : ℕ) * taoSelbergSieveCoefficient R hR d := by
  simp_rw [taoSelbergDivisorWeight_eq_sum_primorialDivisors]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  calc
    (∑ n ∈ Finset.Ioc 0 X,
        if d ∣ n then taoSelbergSieveCoefficient R hR d else 0) =
        ∑ n ∈ (Finset.Ioc 0 X).filter (fun n ↦ d ∣ n),
          taoSelbergSieveCoefficient R hR d := by
      rw [Finset.sum_filter]
    _ = ((Finset.Ioc 0 X).filter (fun n ↦ d ∣ n)).card *
          taoSelbergSieveCoefficient R hR d := by simp
    _ = (X / d : ℕ) * taoSelbergSieveCoefficient R hR d := by
      rw [Nat.Ioc_filter_dvd_card_eq_div]

/-- The standard Selberg bound on the size of each upper coefficient. -/
theorem abs_taoSelbergSieveCoefficient_le_three_pow_omega
    (R : ℕ) (hR : 1 ≤ R) (d : ℕ) :
    |taoSelbergSieveCoefficient R hR d| ≤ (3 : ℝ) ^ ω d := by
  by_cases hdP : d ∣ primorial R
  · apply (taoPrimeSelbergSieve R hR).selberg_bound_muPlus
    exact Nat.mem_divisors.mpr
      ⟨hdP, (Sieve.primorial_squarefree R).ne_zero⟩
  · rw [taoSelbergSieveCoefficient_eq_zero_of_not_dvd_primorial R hR d hdP,
      abs_zero]
    positivity

/-- The density of the concrete prime sieve is exactly `1/d` away from zero. -/
theorem taoPrimeSelbergSieve_nu_apply
    (R : ℕ) (hR : 1 ≤ R) (d : ℕ) (hd : d ≠ 0) :
    (taoPrimeSelbergSieve R hR).nu d = 1 / (d : ℝ) := by
  simp [taoPrimeSelbergSieve, ArithmeticFunction.pdiv_apply, hd]

/-- The coefficient main sum in the native Selberg-sieve representation. -/
def taoSelbergCoefficientMainSum (R : ℕ) (hR : 1 ≤ R) : ℝ :=
  BoundingSieve.mainSum
    (s := (taoPrimeSelbergSieve R hR).toBoundingSieve)
    (taoSelbergSieveCoefficient R hR)

/-- Diagonalization evaluates the native coefficient main sum as the inverse
of the Selberg bounding sum. -/
theorem taoSelbergCoefficientMainSum_eq_inv
    (R : ℕ) (hR : 1 ≤ R) :
    taoSelbergCoefficientMainSum R hR =
      (taoPrimeSelbergSieve R hR).selbergBoundingSum⁻¹ := by
  exact (taoPrimeSelbergSieve R hR).selberg_bound_simple_mainSum

/-- The native Selberg main sum is literally the reciprocal-weighted sum over
the primorial divisors. -/
theorem taoSelbergCoefficientMainSum_eq_sum_div
    (R : ℕ) (hR : 1 ≤ R) :
    taoSelbergCoefficientMainSum R hR =
      ∑ d ∈ (primorial R).divisors,
        taoSelbergSieveCoefficient R hR d / d := by
  unfold taoSelbergCoefficientMainSum BoundingSieve.mainSum
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Sieve.primorial_squarefree R).ne_zero
      (Nat.dvd_of_mem_divisors hd)
  rw [taoPrimeSelbergSieve_nu_apply R hR d hd0]
  ring

/-- The `ℓ¹` mass of the concrete Selberg coefficients has the standard
polylogarithmic overhead. -/
theorem sum_abs_taoSelbergSieveCoefficient_le
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ d ∈ (primorial R).divisors,
        if (d : ℝ) ≤ R then |taoSelbergSieveCoefficient R hR d| else 0) ≤
      (R : ℝ) * (1 + Real.log R) ^ 3 := by
  calc
    (∑ d ∈ (primorial R).divisors,
        if (d : ℝ) ≤ R then |taoSelbergSieveCoefficient R hR d| else 0) ≤
        ∑ d ∈ (primorial R).divisors,
          if (d : ℝ) ≤ R then (3 : ℝ) ^ ω d else 0 := by
      apply sum_le_sum
      intro d hd
      split_ifs
      · exact abs_taoSelbergSieveCoefficient_le_three_pow_omega R hR d
      · exact le_rfl
    _ ≤ (R : ℝ) * (1 + Real.log R) ^ 3 := by
      exact Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow
        (R : ℝ) (by exact_mod_cast hR) (Sieve.primorial_squarefree R)

/-- For the density `1/d`, the Selberg bounding sum is at least
`log R / 2`. -/
theorem taoPrimeSelbergBoundingSum_ge_log_half
    (R : ℕ) (hR : 1 ≤ R) :
    Real.log R / 2 ≤ (taoPrimeSelbergSieve R hR).selbergBoundingSum := by
  have h := Sieve.boundingSum_ge_log (taoPrimeSelbergSieve R hR) rfl
    (fun p hp hpR ↦ by
      change (p : ℝ) ≤ (R : ℝ) at hpR
      change p ∣ primorial R
      rw [Sieve.prime_dvd_primorial_iff R p hp]
      exact_mod_cast hpR)
  simpa [taoPrimeSelbergSieve] using h

/-- The native Selberg coefficient main sum has the required logarithmic
upper bound, with explicit constant two. -/
theorem taoSelbergCoefficientMainSum_le_two_div_log
    (R : ℕ) (hR : 1 < R) :
    taoSelbergCoefficientMainSum R hR.le ≤ 2 / Real.log R := by
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hR
  have hhalf : 0 < Real.log (R : ℝ) / 2 := div_pos hlog (by norm_num)
  have hS := taoPrimeSelbergBoundingSum_ge_log_half R hR.le
  have hSpos : 0 < (taoPrimeSelbergSieve R hR.le).selbergBoundingSum :=
    hhalf.trans_le hS
  rw [taoSelbergCoefficientMainSum_eq_inv]
  calc
    (taoPrimeSelbergSieve R hR.le).selbergBoundingSum⁻¹ ≤
        (Real.log (R : ℝ) / 2)⁻¹ :=
      (inv_le_inv₀ hSpos hhalf).2 hS
    _ = 2 / Real.log R := by field_simp

/-- Replacing the exact floor multiplicities by `X/d` costs at most the
standard Selberg coefficient `ℓ¹` bound. -/
theorem abs_sum_taoSelbergDivisorWeight_sub_main_le
    (R X : ℕ) (hR : 1 ≤ R) :
    |(∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR n) -
        (X : ℝ) * taoSelbergCoefficientMainSum R hR| ≤
      (R : ℝ) * (1 + Real.log R) ^ 3 := by
  rw [sum_taoSelbergDivisorWeight_Ioc_eq,
    taoSelbergCoefficientMainSum_eq_sum_div, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ (primorial R).divisors,
        (((X / d : ℕ) : ℝ) * taoSelbergSieveCoefficient R hR d -
          (X : ℝ) * (taoSelbergSieveCoefficient R hR d / (d : ℝ)))| ≤
        ∑ d ∈ (primorial R).divisors,
          |(((X / d : ℕ) : ℝ) * taoSelbergSieveCoefficient R hR d -
            (X : ℝ) * (taoSelbergSieveCoefficient R hR d / (d : ℝ)))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (primorial R).divisors,
        if (d : ℝ) ≤ R then |taoSelbergSieveCoefficient R hR d| else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdLevel : (d : ℝ) ≤ R
      · rw [if_pos hdLevel]
        have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
        convert abs_floorCoefficient_sub_main_le X d
          (taoSelbergSieveCoefficient R hR) hdPos using 1
        ring_nf
      · rw [if_neg hdLevel]
        have hRd : R < d := by exact_mod_cast (lt_of_not_ge hdLevel)
        rw [taoSelbergSieveCoefficient_eq_zero_of_level_lt R hR d hRd]
        simp
    _ ≤ (R : ℝ) * (1 + Real.log R) ^ 3 :=
      sum_abs_taoSelbergSieveCoefficient_le R hR

/-- Fully explicit diagonal mass estimate supplied by the concrete Selberg
weights.  The polylogarithmic error replaces Tao's sharper `O(R)` Rosser-weight
error and is still negligible for the later power-separated choice of level. -/
theorem sum_taoSelbergDivisorWeight_Ioc_le
    (R X : ℕ) (hR : 1 < R) :
    (∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR.le n) ≤
      (X : ℝ) * (2 / Real.log R) +
        (R : ℝ) * (1 + Real.log R) ^ 3 := by
  have herr := abs_sum_taoSelbergDivisorWeight_sub_main_le R X hR.le
  have hupper :
      (∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR.le n) ≤
        (X : ℝ) * taoSelbergCoefficientMainSum R hR.le +
          (R : ℝ) * (1 + Real.log R) ^ 3 := by
    have hdiff :
        (∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR.le n) -
            (X : ℝ) * taoSelbergCoefficientMainSum R hR.le ≤
          (R : ℝ) * (1 + Real.log R) ^ 3 :=
      (le_abs_self _).trans herr
    linarith
  calc
    (∑ n ∈ Finset.Ioc 0 X, taoSelbergDivisorWeight R hR.le n) ≤
        (X : ℝ) * taoSelbergCoefficientMainSum R hR.le +
          (R : ℝ) * (1 + Real.log R) ^ 3 := hupper
    _ ≤ (X : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3 := by
      gcongr
      exact taoSelbergCoefficientMainSum_le_two_div_log R hR

end

end Tao2026
