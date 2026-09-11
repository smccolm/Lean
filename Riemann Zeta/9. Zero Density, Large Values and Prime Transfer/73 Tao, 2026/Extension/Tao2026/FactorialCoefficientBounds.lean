import Tao2026.FactorialFibers
import Mathlib.Data.Nat.Choose.Factorization
import PrimeNumberTheoremAnd.Consequences

/-!
# The coefficient bound for type-`F₃` intervals

This file proves Tao's Lemma 4.1 (`abound`).  The elementary conclusion
`H < N` is supplied by `FactorialFibers`.  For the quantitative conclusion,
every prime in `(a/2,a]` occurs exactly once in `a!`, hence occurs in the
interval product.  Taking logarithms and using the pinned prime number
theorem gives one uniform constant in `a ≤ C H log N`, including the finite
exceptional range.
-/

namespace Tao2026

open Filter Asymptotics
open scoped BigOperators Chebyshev

/-- The primes in the upper half of `[1,a]` used in Tao's proof of `abound`. -/
def factorialUpperHalfPrimes (a : ℕ) : Finset ℕ :=
  (Finset.Ioc (a / 2) a).filter Nat.Prime

/-- A prime in `(a/2,a]` occurs exactly once in `a!`. -/
theorem factorization_factorial_eq_one_of_half_lt {a p : ℕ}
    (hp : p.Prime) (hhalf : a / 2 < p) (hpa : p ≤ a) :
    a.factorial.factorization p = 1 := by
  have haLtTwoP : a < 2 * p := by
    simpa [mul_comm] using
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hhalf
  have haLtPSq : a < p ^ 2 := by
    have hpTwo : 2 ≤ p := hp.two_le
    nlinarith
  have hlog : Nat.log p a < 2 :=
    Nat.log_lt_of_lt_pow (by omega) haLtPSq
  rw [Nat.factorization_factorial hp hlog]
  norm_num [Finset.sum_Ico_eq_sub]
  exact Nat.div_eq_of_lt_le (by simpa using hpa)
    (by simpa [mul_comm] using haLtTwoP)

/-- Every upper-half prime of the smaller factorial index divides the
corresponding type-`F₃` interval product. -/
theorem upperHalfPrime_dvd_consecutiveProduct {N H a p : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hpMem : p ∈ factorialUpperHalfPrimes a) :
    p ∣ consecutiveProduct N H := by
  have hpData := Finset.mem_filter.mp hpMem
  have hpBounds := Finset.mem_Ioc.mp hpData.1
  have hfacOne : a.factorial.factorization p = 1 :=
    factorization_factorial_eq_one_of_half_lt
      hpData.2 hpBounds.1 hpBounds.2
  have hpDvdFactorial : p ∣ a.factorial :=
    hpData.2.dvd_factorial.mpr hpBounds.2
  have hpMemFactorial : p ∈ a.factorial.primeFactors :=
    hpData.2.mem_primeFactors hpDvdFactorial (Nat.factorial_ne_zero a)
  have hpMemFactorialComponent :
      p ∈ (squarefreeComponent a.factorial).primeFactors :=
    mem_primeFactors_squarefreeComponent_iff.mpr
      ⟨hpMemFactorial, by simp [hfacOne]⟩
  have hpMemProductComponent :
      p ∈ (squarefreeComponent (consecutiveProduct N H)).primeFactors := by
    rw [haData.2.2]
    exact hpMemFactorialComponent
  exact Nat.dvd_of_mem_primeFactors
    (mem_primeFactors_squarefreeComponent_iff.mp hpMemProductComponent).1

/-- The product of all primes in `(a/2,a]` divides the type-`F₃` interval
product. -/
theorem prod_factorialUpperHalfPrimes_dvd_consecutiveProduct
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial) :
    ∏ p ∈ factorialUpperHalfPrimes a, p ∣ consecutiveProduct N H := by
  have hsubset : factorialUpperHalfPrimes a ⊆
      (consecutiveProduct N H).primeFactors := by
    intro p hpMem
    have hp := (Finset.mem_filter.mp hpMem).2
    exact hp.mem_primeFactors
      (upperHalfPrime_dvd_consecutiveProduct haData hpMem)
      (consecutiveProduct_ne_zero N H)
  exact (Finset.prod_dvd_prod_of_subset
    (factorialUpperHalfPrimes a)
    (consecutiveProduct N H).primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd (consecutiveProduct N H))

/-- Logarithmic form of the upper-half-prime divisibility statement. -/
theorem sum_log_factorialUpperHalfPrimes_le_log_consecutiveProduct
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial) :
    ∑ p ∈ factorialUpperHalfPrimes a, Real.log p ≤
      Real.log (consecutiveProduct N H) := by
  have hprodDvd :=
    prod_factorialUpperHalfPrimes_dvd_consecutiveProduct haData
  have hprodPos : 0 < ∏ p ∈ factorialUpperHalfPrimes a, p := by
    exact Finset.prod_pos fun p hpMem ↦
      (Finset.mem_filter.mp hpMem).2.pos
  have hprodLe : ∏ p ∈ factorialUpperHalfPrimes a, p ≤
      consecutiveProduct N H :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero (consecutiveProduct_ne_zero N H)) hprodDvd
  have hlog :
      Real.log ((∏ p ∈ factorialUpperHalfPrimes a, p : ℕ) : ℝ) ≤
        Real.log (consecutiveProduct N H : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprodPos) (by exact_mod_cast hprodLe)
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · exact hlog
  · intro p hpMem
    exact_mod_cast (Finset.mem_filter.mp hpMem).2.ne_zero

/-- The logarithm of an interval product is at most its length times the
logarithm of its right endpoint. -/
theorem log_consecutiveProduct_le {N H : ℕ} (hHN : H < N) :
    Real.log (consecutiveProduct N H) ≤
      (H : ℝ) * Real.log (N + H) := by
  rw [consecutiveProduct, Nat.cast_prod, Real.log_prod]
  · calc
      ∑ n ∈ consecutiveInterval N H, Real.log n ≤
          ∑ n ∈ consecutiveInterval N H, Real.log (N + H) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnBounds : N < n ∧ n ≤ N + H := by
          simpa only [consecutiveInterval, Finset.mem_Ioc] using hn
        exact Real.log_le_log
          (by exact_mod_cast (by omega : 0 < n))
          (by exact_mod_cast hnBounds.2)
      _ = (H : ℝ) * Real.log (N + H) := by
        simp [consecutiveInterval]
  · intro n hn
    have hnBounds : N < n ∧ n ≤ N + H := by
      simpa only [consecutiveInterval, Finset.mem_Ioc] using hn
    exact_mod_cast (by omega : n ≠ 0)

/-- The upper-half prime logarithm sum is exactly a Chebyshev-theta
difference, with the natural-number floor `a/2`. -/
theorem sum_log_factorialUpperHalfPrimes_eq_theta_sub (a : ℕ) :
    ∑ p ∈ factorialUpperHalfPrimes a, Real.log p =
      Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hsubset :
      (Finset.Icc 0 (a / 2)).filter Nat.Prime ⊆
        (Finset.Icc 0 a).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.div_le_self a 2)⟩, hp.2⟩
  have hsets : factorialUpperHalfPrimes a =
      (Finset.Icc 0 a).filter Nat.Prime \
        (Finset.Icc 0 (a / 2)).filter Nat.Prime := by
    ext p
    simp only [factorialUpperHalfPrimes, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hhalf, hpa⟩, hp⟩
      refine ⟨⟨⟨Nat.zero_le p, hpa⟩, hp⟩, ?_⟩
      rintro ⟨⟨_, hpHalf⟩, _⟩
      exact (Nat.not_le_of_lt hhalf) hpHalf
    · rintro ⟨⟨⟨_, hpa⟩, hp⟩, hnot⟩
      refine ⟨⟨?_, hpa⟩, hp⟩
      by_contra hhalf
      exact hnot ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hhalf⟩, hp⟩
  rw [hsets]
  linarith [Finset.sum_sdiff hsubset (f := fun p : ℕ ↦ Real.log p)]

/-- Tao's exact finite logarithmic inequality before applying the prime
number theorem. -/
theorem factorialUpperHalfTheta_le {N H a : ℕ}
    (hf3 : IsFactorialThreeInterval N H)
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial) :
    Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) ≤
      (H : ℝ) * Real.log (N + H) := by
  rw [← sum_log_factorialUpperHalfPrimes_eq_theta_sub]
  exact
    (sum_log_factorialUpperHalfPrimes_le_log_consecutiveProduct haData).trans
      (log_consecutiveProduct_le hf3.length_lt_start)

/-- Epsilon form of the pinned Chebyshev prime number theorem. -/
theorem eventually_abs_chebyshev_theta_error_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ epsilon * x := by
  have h := Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
  rw [Asymptotics.isLittleO_iff] at h
  have h' := h hepsilon
  filter_upwards [h', eventually_gt_atTop (0 : ℝ)] with x hx xpos
  simpa [Real.norm_eq_abs, abs_of_pos hepsilon, abs_of_pos xpos, mul_comm]
    using hx

/-- The PNT lower bound for the Chebyshev mass of the natural interval
`(⌊a/2⌋,a]`, with an explicit positive fraction sufficient for `abound`. -/
theorem eventually_nat_factorialUpperHalfTheta_lower :
    ∀ᶠ a : ℕ in atTop,
      (a : ℝ) / 4 ≤
        Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) := by
  have herr :=
    eventually_abs_chebyshev_theta_error_le (1 / 10) (by norm_num)
  have herrA : ∀ᶠ a : ℕ in atTop,
      |Chebyshev.theta a - a| ≤ (1 / 10 : ℝ) * a :=
    tendsto_natCast_atTop_atTop.eventually herr
  have hhalfTendsto :
      Tendsto (fun a : ℕ ↦ ((a / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have herrHalf : ∀ᶠ a : ℕ in atTop,
      |Chebyshev.theta ((a / 2 : ℕ) : ℝ) - (a / 2 : ℕ)| ≤
        (1 / 10 : ℝ) * (a / 2 : ℕ) :=
    hhalfTendsto.eventually herr
  filter_upwards [herrA, herrHalf] with a ha hhalf
  rw [abs_le] at ha hhalf
  have hcastHalf : ((a / 2 : ℕ) : ℝ) ≤ (a : ℝ) / 2 := Nat.cast_div_le
  nlinarith

/-- Since `H<N`, the endpoint logarithm costs at most two copies of
`log N`. -/
theorem log_endpoint_le_two_mul_log_start {N H : ℕ}
    (hH : 1 ≤ H) (hHN : H < N) :
    Real.log (N + H) ≤ 2 * Real.log N := by
  have hNtwo : 2 ≤ N := by omega
  have hsumPos : (0 : ℝ) < N + H := by positivity
  have hsumLe : (N + H : ℕ) ≤ 2 * N := by omega
  have hlogTwoLe : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNtwo)
  calc
    Real.log (N + H) ≤ Real.log (2 * N) :=
      Real.log_le_log hsumPos (by exact_mod_cast hsumLe)
    _ = Real.log 2 + Real.log N := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast (by omega : N ≠ 0))]
    _ ≤ 2 * Real.log N := by linarith

/-- Exact proposition-valued contract for Tao's Lemma 4.1 (`abound`). -/
def TaoLemma41Conclusion : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {N H a : ℕ}, 1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      H < N ∧ (a : ℝ) ≤ C * H * Real.log N

/-- Tao's complete Lemma 4.1: every type-`F₃` interval has `H<N`, and the
smaller factorial index satisfies `a ≪ H log N` with one uniform constant.
The finite PNT-exceptional range is absorbed into the same constant. -/
theorem taoLemma41 : TaoLemma41Conclusion := by
  obtain ⟨A, hA⟩ :=
    eventually_atTop.1 eventually_nat_factorialUpperHalfTheta_lower
  let C : ℝ := max 8 ((A : ℝ) / Real.log 2)
  refine ⟨C, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_left _ _)
  intro N H a hH ha haN hcomponent
  have hf3 : IsFactorialThreeInterval N H :=
    ⟨hH, a, ha, haN, hcomponent⟩
  have hHN : H < N := hf3.length_lt_start
  refine ⟨hHN, ?_⟩
  have hNtwo : 2 ≤ N := by omega
  have hlogN : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast hNtwo)
  have hscaleNonneg : 0 ≤ (H : ℝ) * Real.log N := by positivity
  by_cases haLarge : A ≤ a
  · have hlower := hA a haLarge
    have hupper :=
      factorialUpperHalfTheta_le hf3 ⟨ha, haN, hcomponent⟩
    have hlog := log_endpoint_le_two_mul_log_start hH hHN
    have htheta :
        Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) ≤
          2 * (H : ℝ) * Real.log N := by
      calc
        Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) ≤
            (H : ℝ) * Real.log (N + H) := hupper
        _ ≤ (H : ℝ) * (2 * Real.log N) := by gcongr
        _ = 2 * (H : ℝ) * Real.log N := by ring
    calc
      (a : ℝ) ≤ 8 * (H : ℝ) * Real.log N := by nlinarith
      _ ≤ C * (H : ℝ) * Real.log N := by
        have hC : (8 : ℝ) ≤ C := le_max_left _ _
        nlinarith
  · have haA : (a : ℝ) ≤ A := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge haLarge))
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogTwoLe : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hNtwo)
    have hbase : Real.log 2 ≤ (H : ℝ) * Real.log N := by
      have hHcast : (1 : ℝ) ≤ H := by exact_mod_cast hH
      nlinarith
    have hAupper :
        (A : ℝ) ≤ ((A : ℝ) / Real.log 2) *
          ((H : ℝ) * Real.log N) := by
      calc
        (A : ℝ) = ((A : ℝ) / Real.log 2) * Real.log 2 := by
          field_simp
        _ ≤ ((A : ℝ) / Real.log 2) *
            ((H : ℝ) * Real.log N) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
    calc
      (a : ℝ) ≤ (A : ℝ) := haA
      _ ≤ ((A : ℝ) / Real.log 2) *
          ((H : ℝ) * Real.log N) := hAupper
      _ ≤ C * ((H : ℝ) * Real.log N) := by
        gcongr
        exact le_max_right _ _
      _ = C * (H : ℝ) * Real.log N := by ring

/-- A deterministic positive uniform constant from the proved Lemma 4.1. -/
noncomputable def taoLemma41Constant : ℝ := Classical.choose taoLemma41

theorem taoLemma41Constant_pos : 0 < taoLemma41Constant :=
  (Classical.choose_spec taoLemma41).1

/-- Source-ready specialization of Lemma 4.1 using its chosen uniform
constant. -/
theorem taoLemma41_chosenConstant
    {N H a : ℕ} (hH : 1 ≤ H) (ha : 1 ≤ a) (haN : a < N)
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial) :
    H < N ∧
      (a : ℝ) ≤ taoLemma41Constant * H * Real.log N :=
  (Classical.choose_spec taoLemma41).2 hH ha haN hcomponent

end Tao2026
