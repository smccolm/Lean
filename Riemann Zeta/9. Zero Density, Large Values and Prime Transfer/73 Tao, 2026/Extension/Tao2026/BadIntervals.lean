import Tao2026.FactorialExtraction
import Tao2026.FactorialLargeSieve
import Tao2026.SmoothNumbers
import Tao2026.VeryBadIntervals

/-!
# Basic estimates for bad intervals

This module formalizes the arithmetic content of Tao's Lemma 6.1.  An
admissible interval is a non-singleton bad interval meeting the dyadic window
`[x/2,x]`.  The largest prime factor of its product occurs to exponent at
least two in one interval element, while every interval element is smooth at
that prime.

The only named source input retained below is the Sylvester--Schur theorem,
already isolated as `SylvesterSchurConclusion` in `VeryBadIntervals`.
-/

namespace Tao2026

open scoped BigOperators

/-- Source-faithful finite version of an admissible interval in Section 6.
The witness formulation avoids any coercion ambiguity in “intersects
`[x/2,x]`”. -/
def IsAdmissibleBadInterval (x N H : ℕ) : Prop :=
  2 ≤ H ∧ IsBadInterval N H ∧
    ∃ n ∈ consecutiveInterval N H, x / 2 ≤ n ∧ n ≤ x

/-- The prime named in `IsBadInterval` really is prime and retains the square
divisibility supplied by the definition. -/
theorem IsBadInterval.exists_largestPrimeData {N H : ℕ}
    (hbad : IsBadInterval N H) :
    ∃ p : ℕ, p.Prime ∧
      largestPrimeFactor (consecutiveProduct N H) = some p ∧
      p ^ 2 ∣ consecutiveProduct N H := by
  obtain ⟨p, hpMax, hpSq⟩ := hbad.2
  exact ⟨p, Nat.prime_of_mem_primeFactors
    (largestPrimeFactor_eq_some_iff.mp hpMax).1, hpMax, hpSq⟩

/-- A non-singleton bad interval cannot be longer than its starting point.
This is the first assertion in Tao's Lemma 6.1 and is unconditional: Bertrand
produces a prime in the upper half of the product range, and maximality moves
the resulting one-occurrence contradiction to the bad interval's largest
prime factor. -/
theorem IsBadInterval.length_le_start {N H : ℕ} (hH : 2 ≤ H)
    (hbad : IsBadInterval N H) : H ≤ N := by
  by_contra hnot
  have hNltH : N < H := by omega
  have hsumTwo : 2 ≤ N + H := by omega
  obtain ⟨q, hq, hqLower, hqUpper⟩ := taoProposition23i hsumTwo
  have hNltq : N < q := by omega
  have hsumLtq : N + H < 2 * q := by omega
  obtain ⟨hqDvd, _⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hq hNltq hqUpper hsumLtq
  obtain ⟨p, hp, hpMax, hpSq⟩ := hbad.exists_largestPrimeData
  have hqLeP : q ≤ p :=
    (largestPrimeFactor_eq_some_iff.mp hpMax).2 q
      (hq.mem_primeFactors hqDvd (consecutiveProduct_ne_zero N H))
  have hpDvd : p ∣ consecutiveProduct N H := dvd_trans (dvd_pow_self p (by omega)) hpSq
  obtain ⟨k, hk, hpk⟩ :=
    exists_mem_consecutiveInterval_of_prime_dvd_product hp hpDvd
  have hkBounds := Finset.mem_Ioc.mp hk
  have hNltp : N < p := hNltq.trans_le hqLeP
  have hpUpper : p ≤ N + H := by
    exact (Nat.le_of_dvd (by omega) hpk).trans hkBounds.2
  have hsumLtp : N + H < 2 * p :=
    hsumLtq.trans_le (Nat.mul_le_mul_left 2 hqLeP)
  exact (prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLtp).2 hpSq

/-- Under Sylvester--Schur, the largest prime factor of a non-singleton bad
interval exceeds the interval length.  The equality case `H=N` follows
directly from Bertrand on `[H,2H]`. -/
theorem IsBadInterval.length_lt_largestPrime_of_sylvesterSchur
    (hSS : SylvesterSchurConclusion) {N H p : ℕ} (hH : 2 ≤ H)
    (hbad : IsBadInterval N H)
    (hpMax : largestPrimeFactor (consecutiveProduct N H) = some p) :
    H < p := by
  have hHleN := hbad.length_le_start hH
  have hpLargest := largestPrimeFactor_eq_some_iff.mp hpMax
  rcases hHleN.eq_or_lt with hEq | hHltN
  · subst N
    obtain ⟨q, hq, hqLower, hqUpper⟩ := taoProposition23i (by omega : 2 ≤ H + H)
    have hHltq : H < q := by omega
    have hsumLt : H + H < 2 * q := by omega
    have hqDvd := (prime_dvd_consecutiveProduct_exactly_once
      (N := H) (H := H) hq hHltq hqUpper hsumLt).1
    exact hHltq.trans_le (hpLargest.2 q
      (hq.mem_primeFactors hqDvd (consecutiveProduct_ne_zero H H)))
  · obtain ⟨q, hq, hHltq, hqDvd⟩ := hSS hbad.length_pos hHltN
    exact hHltq.trans_le (hpLargest.2 q
      (hq.mem_primeFactors hqDvd (consecutiveProduct_ne_zero N H)))

/-- Once the largest prime exceeds the interval length, all of its square
valuation is concentrated in one interval element.  The remaining cofactor
is smooth at that prime. -/
theorem exists_intervalElement_eq_largestPrime_sq_mul_smooth
    {N H p : ℕ} (hHltp : H < p) (hp : p.Prime)
    (hpMax : largestPrimeFactor (consecutiveProduct N H) = some p)
    (hpSq : p ^ 2 ∣ consecutiveProduct N H) :
    ∃ k ∈ consecutiveInterval N H, ∃ m : ℕ,
      IsSmooth m p ∧ k = p ^ 2 * m := by
  have hpDvd : p ∣ consecutiveProduct N H :=
    dvd_trans (dvd_pow_self p (by omega)) hpSq
  obtain ⟨k, hk, hpk⟩ :=
    exists_mem_consecutiveInterval_of_prime_dvd_product hp hpDvd
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hfacEq := factorization_consecutiveProduct_eq_of_mem_prime_dvd
    hk hp hHltp hpk
  have hfacTwo : 2 ≤ k.factorization p := by
    rw [← hfacEq]
    exact (hp.pow_dvd_iff_le_factorization (consecutiveProduct_ne_zero N H)).mp hpSq
  have hpSqK : p ^ 2 ∣ k :=
    (hp.pow_dvd_iff_le_factorization hkPos.ne').mpr hfacTwo
  obtain ⟨m, hm⟩ := hpSqK
  refine ⟨k, hk, m, ?_, hm⟩
  rw [isSmooth_iff]
  constructor
  · intro hm0
    apply hkPos.ne'
    rw [hm, hm0]
    simp
  · intro q hq hqm
    have hqk : q ∣ k := by
      rw [hm]
      exact dvd_mul_of_dvd_right hqm (p ^ 2)
    have hqProduct : q ∣ consecutiveProduct N H := by
      rw [consecutiveProduct]
      exact dvd_trans hqk (Finset.dvd_prod_of_mem id hk)
    exact (largestPrimeFactor_eq_some_iff.mp hpMax).2 q
      (hq.mem_primeFactors hqProduct (consecutiveProduct_ne_zero N H))

/-- Every element of an interval is smooth at the largest prime factor of
the interval product. -/
theorem intervalElement_isSmooth_largestPrime {N H p k : ℕ}
    (hpMax : largestPrimeFactor (consecutiveProduct N H) = some p)
    (hk : k ∈ consecutiveInterval N H) : IsSmooth k p := by
  rw [isSmooth_iff]
  constructor
  · have := (Finset.mem_Ioc.mp hk).1
    omega
  · intro q hq hqk
    have hqProduct : q ∣ consecutiveProduct N H := by
      rw [consecutiveProduct]
      exact dvd_trans hqk (Finset.dvd_prod_of_mem id hk)
    exact (largestPrimeFactor_eq_some_iff.mp hpMax).2 q
      (hq.mem_primeFactors hqProduct (consecutiveProduct_ne_zero N H))

/-- Every element of a non-singleton bad interval is composite.  This useful
consequence of Lemma 6.1 is unconditional: if an interval element were prime,
maximality would put the bad interval's squared largest prime above `N`; its
occurrence in `[N+1,N+H]` would then be unique, a contradiction. -/
theorem IsBadInterval.not_prime_of_mem {N H j : ℕ} (hH : 2 ≤ H)
    (hbad : IsBadInterval N H) (hj : j ∈ consecutiveInterval N H) :
    ¬j.Prime := by
  intro hjPrime
  have hHleN := hbad.length_le_start hH
  obtain ⟨p, hp, hpMax, hpSq⟩ := hbad.exists_largestPrimeData
  have hjDvdProduct : j ∣ consecutiveProduct N H := by
    rw [consecutiveProduct]
    exact Finset.dvd_prod_of_mem id hj
  have hjLeP : j ≤ p :=
    (largestPrimeFactor_eq_some_iff.mp hpMax).2 j
      (hjPrime.mem_primeFactors hjDvdProduct (consecutiveProduct_ne_zero N H))
  have hpDvd : p ∣ consecutiveProduct N H :=
    dvd_trans (dvd_pow_self p (by omega)) hpSq
  obtain ⟨k, hk, hpk⟩ :=
    exists_mem_consecutiveInterval_of_prime_dvd_product hp hpDvd
  have hjBounds := Finset.mem_Ioc.mp hj
  have hkBounds := Finset.mem_Ioc.mp hk
  have hNltp : N < p := hjBounds.1.trans_le hjLeP
  have hpUpper : p ≤ N + H :=
    (Nat.le_of_dvd (by omega) hpk).trans hkBounds.2
  have hsumLt : N + H < 2 * p := by omega
  exact (prime_dvd_consecutiveProduct_exactly_once
    hp hNltp hpUpper hsumLt).2 hpSq

/-- Exact natural-number comparability furnished by the dyadic intersection
in an admissible interval: `N < x ≤ 4N+1`.  The final `+1` is the literal
rounding loss from natural-number division in the endpoint `x/2`. -/
theorem IsAdmissibleBadInterval.start_bounds {x N H : ℕ}
    (hadm : IsAdmissibleBadInterval x N H) : N < x ∧ x ≤ 4 * N + 1 := by
  obtain ⟨hH, hbad, n, hn, hxHalf, hnx⟩ := hadm
  have hHleN := hbad.length_le_start hH
  have hnBounds := Finset.mem_Ioc.mp hn
  constructor
  · exact hnBounds.1.trans_le hnx
  · have hdivLt : x / 2 < n + 1 := by omega
    have hxLt : x < (n + 1) * 2 :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp hdivLt
    omega

/-- Tao's Lemma 6.1 arithmetic package.  It records the exact finite bounds
behind `N \asymp x`, the large squared prime factor, its smooth cofactor, and
the smoothness of every element of the admissible interval. -/
theorem IsAdmissibleBadInterval.basic_estimates_of_sylvesterSchur
    (hSS : SylvesterSchurConclusion) {x N H : ℕ}
    (hadm : IsAdmissibleBadInterval x N H) :
    H ≤ N ∧ N < x ∧ x ≤ 4 * N + 1 ∧
      ∃ p k m : ℕ, p.Prime ∧ H < p ∧
        largestPrimeFactor (consecutiveProduct N H) = some p ∧
        k ∈ consecutiveInterval N H ∧ IsSmooth m p ∧
        k = p ^ 2 * m ∧ p ^ 2 * m ≤ 2 * x ∧
        (∀ j ∈ consecutiveInterval N H, IsSmooth j p) ∧
        ∀ j ∈ consecutiveInterval N H, ¬j.Prime := by
  obtain ⟨hNltx, hxLe⟩ := IsAdmissibleBadInterval.start_bounds hadm
  obtain ⟨hH, hbad, _⟩ := hadm
  have hHleN := hbad.length_le_start hH
  obtain ⟨p, hp, hpMax, hpSq⟩ := hbad.exists_largestPrimeData
  have hHltp := hbad.length_lt_largestPrime_of_sylvesterSchur
    hSS hH hpMax
  obtain ⟨k, hk, m, hmSmooth, hkm⟩ :=
    exists_intervalElement_eq_largestPrime_sq_mul_smooth
      hHltp hp hpMax hpSq
  refine ⟨hHleN, hNltx, hxLe, p, k, m, hp, hHltp, hpMax,
    hk, hmSmooth, hkm, ?_, ?_, ?_⟩
  · rw [← hkm]
    have hkUpper := (Finset.mem_Ioc.mp hk).2
    omega
  · intro j hj
    exact intervalElement_isSmooth_largestPrime hpMax hj
  · intro j hj
    exact hbad.not_prime_of_mem hH hj

end Tao2026
