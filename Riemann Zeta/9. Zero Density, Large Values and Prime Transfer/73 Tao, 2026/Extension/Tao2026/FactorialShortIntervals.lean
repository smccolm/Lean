import Tao2026.FactorialCoefficientBounds
import Tao2026.PowerfulExtraction

/-!
# Arithmetic preparation for short type-`F₃` intervals

This file formalizes the common arithmetic spine of Tao's Lemma 4.2 (`hf3`).
Above the source scale `P = H log² N`, Lemma 4.1 excludes divisibility of the
smaller factorial.  Equality of squarefree components then forces even
valuation in the interval product.  Since such a prime exceeds `H`, it can
divide only one interval element, and must divide that element twice.  In the
large-`P` case this is impossible because `p² > N+H`.
-/

namespace Tao2026

open Filter

/-- Outside the prime support of `a!`, equality of squarefree components
forces an even valuation in the interval product. -/
theorem factorization_consecutiveProduct_even_of_not_dvd_factorial
    {N H a p : ℕ}
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial)
    (hp : p.Prime) (hpNotDvdFactorial : ¬p ∣ a.factorial) :
    Even ((consecutiveProduct N H).factorization p) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨r, hr⟩ := hodd
  have hfacPos : 1 ≤ (consecutiveProduct N H).factorization p := by omega
  have hpDvdProduct : p ∣ consecutiveProduct N H :=
    (hp.dvd_iff_one_le_factorization
      (consecutiveProduct_ne_zero N H)).mpr hfacPos
  have hpMemProduct : p ∈ (consecutiveProduct N H).primeFactors :=
    hp.mem_primeFactors hpDvdProduct (consecutiveProduct_ne_zero N H)
  have hpMemProductComponent :
      p ∈ (squarefreeComponent (consecutiveProduct N H)).primeFactors :=
    mem_primeFactors_squarefreeComponent_iff.mpr
      ⟨hpMemProduct, ⟨r, hr⟩⟩
  have hpMemFactorialComponent :
      p ∈ (squarefreeComponent a.factorial).primeFactors := by
    rw [← hcomponent]
    exact hpMemProductComponent
  exact hpNotDvdFactorial (Nat.dvd_of_mem_primeFactors
    (mem_primeFactors_squarefreeComponent_iff.mp hpMemFactorialComponent).1)

/-- Consequently, any such prime divisor occurs at least twice in the full
interval product. -/
theorem prime_sq_dvd_consecutiveProduct_of_factorialThree
    {N H a p : ℕ}
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial)
    (hp : p.Prime) (hpNotDvdFactorial : ¬p ∣ a.factorial)
    (hpDvdProduct : p ∣ consecutiveProduct N H) :
    p ^ 2 ∣ consecutiveProduct N H := by
  have heven :=
    factorization_consecutiveProduct_even_of_not_dvd_factorial
      hcomponent hp hpNotDvdFactorial
  have hfacPos : 1 ≤ (consecutiveProduct N H).factorization p :=
    (hp.dvd_iff_one_le_factorization
      (consecutiveProduct_ne_zero N H)).mp hpDvdProduct
  rcases heven with ⟨r, hr⟩
  have hfacTwo : 2 ≤ (consecutiveProduct N H).factorization p := by omega
  exact (hp.pow_dvd_iff_le_factorization
    (consecutiveProduct_ne_zero N H)).mpr hfacTwo

/-- When `p>H`, the even valuation is concentrated in the unique interval
element divisible by `p`. -/
theorem prime_sq_dvd_intervalElement_of_factorialThree
    {N H a k p : ℕ}
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial)
    (hk : k ∈ consecutiveInterval N H) (hp : p.Prime)
    (hHltp : H < p) (hpk : p ∣ k)
    (hpNotDvdFactorial : ¬p ∣ a.factorial) : p ^ 2 ∣ k := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hproductFac :
      (consecutiveProduct N H).factorization p = k.factorization p := by
    rw [consecutiveProduct, Nat.factorization_prod_apply]
    · apply Finset.sum_eq_single k
      · intro j hj hjne
        have hjPos : 0 < j := by
          have := (Finset.mem_Ioc.mp hj).1
          omega
        have hpjNot : ¬p ∣ j := by
          intro hpj
          exact hjne (eq_of_mem_consecutiveInterval_of_prime_dvd
            hj hk hHltp hpj hpk)
        rw [hp.dvd_iff_one_le_factorization hjPos.ne'] at hpjNot
        omega
      · exact fun h => (h hk).elim
    · intro j hj
      have := (Finset.mem_Ioc.mp hj).1
      omega
  have hpProduct : p ∣ consecutiveProduct N H := by
    rw [consecutiveProduct]
    exact dvd_trans hpk (Finset.dvd_prod_of_mem id hk)
  have hpSqProduct : p ^ 2 ∣ consecutiveProduct N H :=
    prime_sq_dvd_consecutiveProduct_of_factorialThree
      hcomponent hp hpNotDvdFactorial hpProduct
  have htwoProduct : 2 ≤ (consecutiveProduct N H).factorization p :=
    (hp.pow_dvd_iff_le_factorization
      (consecutiveProduct_ne_zero N H)).mp hpSqProduct
  have htwoK : 2 ≤ k.factorization p := by
    rwa [hproductFac] at htwoProduct
  exact (hp.pow_dvd_iff_le_factorization hkPos.ne').mpr htwoK

/-- If additionally `p²>N+H`, the prime cannot divide the interval product
at all. -/
theorem prime_not_dvd_consecutiveProduct_of_factorialThree
    {N H a p : ℕ}
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial)
    (hp : p.Prime) (haLtp : a < p) (hHLtp : H < p)
    (hendpoint : N + H < p ^ 2) :
    ¬p ∣ consecutiveProduct N H := by
  intro hpProduct
  change p ∣ (consecutiveInterval N H).prod id at hpProduct
  obtain ⟨k, hk, hpk⟩ :=
    (hp.prime.dvd_finsetProd_iff id).mp hpProduct
  have hpNotDvdFactorial : ¬p ∣ a.factorial := by
    rw [hp.dvd_factorial, not_le]
    exact haLtp
  have hpSqK : p ^ 2 ∣ k :=
    prime_sq_dvd_intervalElement_of_factorialThree
      hcomponent hk hp hHLtp hpk hpNotDvdFactorial
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hpSqLeK : p ^ 2 ≤ k := Nat.le_of_dvd hkPos hpSqK
  have hkLe : k ≤ N + H := (Finset.mem_Ioc.mp hk).2
  omega

/-- Tao's source scale `P = H log² N` for Lemma 4.2. -/
noncomputable def factorialPrimeScale (N H : ℕ) : ℝ :=
  (H : ℝ) * (Real.log N) ^ 2

/-- Lemma 4.1 puts every witnessing factorial index strictly below `P`,
uniformly for all sufficiently large starts. -/
theorem eventually_factorialThreeCoefficient_lt_primeScale :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      (a : ℝ) < factorialPrimeScale N H := by
  obtain ⟨C, hC, hbound⟩ := taoLemma41
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop C)
  have hNlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  filter_upwards [hlog, hNlarge] with
    N hClog hN H a hH ha haN hcomponent
  simp only [Function.comp_apply] at hClog
  have habound := (hbound hH ha haN hcomponent).2
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogPos : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast hN)
  have hClogSq : C * Real.log N < (Real.log N) ^ 2 := by nlinarith
  have hscaled := mul_lt_mul_of_pos_left hClogSq hHpos
  rw [factorialPrimeScale]
  calc
    (a : ℝ) ≤ (H : ℝ) * (C * Real.log N) := by nlinarith
    _ < (H : ℝ) * (Real.log N) ^ 2 := hscaled

theorem eventually_one_lt_log_nat :
    ∀ᶠ N : ℕ in atTop, 1 < Real.log N :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop 1)

/-- Eventually, every prime above `P` lies above both `a` and `H`. -/
theorem eventually_factorialPrimeScale_lt_prime :
    ∀ᶠ N : ℕ in atTop, ∀ {H a p : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      factorialPrimeScale N H < p →
      a < p ∧ H < p := by
  filter_upwards [eventually_factorialThreeCoefficient_lt_primeScale,
    eventually_one_lt_log_nat] with
    N haScale hlog H a p hH ha haN hcomponent hPp
  have haP := haScale hH ha haN hcomponent
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHP : (H : ℝ) < factorialPrimeScale N H := by
    have hlogSq : (1 : ℝ) < (Real.log N) ^ 2 := by nlinarith
    rw [factorialPrimeScale]
    calc
      (H : ℝ) = (H : ℝ) * 1 := by ring
      _ < (H : ℝ) * (Real.log N) ^ 2 :=
        mul_lt_mul_of_pos_left hlogSq hHpos
  have haLtpReal : (a : ℝ) < p := lt_trans haP hPp
  have hHLtpReal : (H : ℝ) < p := lt_trans hHP hPp
  constructor
  · exact_mod_cast haLtpReal
  · exact_mod_cast hHLtpReal

/-- The exact arithmetic conclusion in Tao's large-`P` branch: if
`√(2N)<P<p`, then the prime does not divide the type-`F₃` interval product.
The statement is uniform after a single eventual threshold in `N`. -/
theorem eventually_not_prime_dvd_factorialThree_of_large_scale :
    ∀ᶠ N : ℕ in atTop, ∀ {H a p : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      p.Prime →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      factorialPrimeScale N H < p →
      ¬p ∣ consecutiveProduct N H := by
  filter_upwards [eventually_factorialPrimeScale_lt_prime] with
    N hscale H a p hH ha haN hcomponent hp hPbig hPp
  obtain ⟨haLtp, hHLtp⟩ := hscale hH ha haN hcomponent hPp
  have hHN := (IsFactorialThreeInterval.length_lt_start
    ⟨hH, a, ha, haN, hcomponent⟩)
  have hendpointReal : (N + H : ℕ) < p ^ 2 := by
    have htwoN : (N + H : ℝ) < 2 * N := by
      exact_mod_cast (by omega : N + H < 2 * N)
    have hsqrtSq : (Real.sqrt (2 * (N : ℝ))) ^ 2 = 2 * N := by
      rw [Real.sq_sqrt]
      positivity
    have hPSq : 2 * (N : ℝ) < (factorialPrimeScale N H) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (2 * (N : ℝ))]
    have hpSq : (factorialPrimeScale N H) ^ 2 < (p : ℝ) ^ 2 := by
      have hPnonneg : 0 ≤ factorialPrimeScale N H := by
        rw [factorialPrimeScale]
        positivity
      nlinarith
    exact_mod_cast (lt_trans htwoN (lt_trans hPSq hpSq))
  exact prime_not_dvd_consecutiveProduct_of_factorialThree
    hcomponent hp haLtp hHLtp hendpointReal

end Tao2026
