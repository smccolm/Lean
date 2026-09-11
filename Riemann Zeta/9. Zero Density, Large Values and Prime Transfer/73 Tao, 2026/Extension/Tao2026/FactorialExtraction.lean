import Tao2026.FactorialCoefficientBounds
import Tao2026.CoefficientBounds
import Tao2026.CoefficientSelection
import Tao2026.PowerfulExtraction
import Tao2026.PowerfulLimit

/-!
# Square-relation extraction for type-`F₃` intervals

This file begins Tao's Lemma 4.3.  Each interval element is split into its
canonical squarefree component and a square.  Equality with the squarefree
component of `a!`, together with uniqueness of a multiple of a prime larger
than the interval length, shows that every prime in the coefficient is at
most `max a H`.  Two consecutive positions then give the exact nonzero-shift
square relation used in Section 4.
-/

namespace Tao2026

noncomputable section

/-- If `p > H` divides an interval element, that element accounts for the
entire `p`-adic valuation of the interval product. -/
theorem factorization_consecutiveProduct_eq_of_mem_prime_dvd
    {N H k p : ℕ} (hk : k ∈ consecutiveInterval N H)
    (hp : p.Prime) (hHltp : H < p) (hpk : p ∣ k) :
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

/-- The squarefree coefficient of an element in a type-`F₃` interval is
supported on primes at most `max a H`, where `a!` is the factorial appearing
in the definition of the interval. -/
theorem prime_dvd_squarefreeComponent_le_max_of_factorialThree
    {N H a k p : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hk : k ∈ consecutiveInterval N H) (hp : p.Prime)
    (hpCoeff : p ∣ squarefreeComponent k) : p ≤ max a H := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hcoeffPos : 0 < squarefreeComponent k :=
    squarefreeComponent_pos_of_positive ⟨k, hkPos⟩
  have hpMemCoeff : p ∈ (squarefreeComponent k).primeFactors :=
    hp.mem_primeFactors hpCoeff hcoeffPos.ne'
  have hkParity := mem_primeFactors_squarefreeComponent_iff.mp hpMemCoeff
  have hpk : p ∣ k := Nat.dvd_of_mem_primeFactors hkParity.1
  by_contra hpMax
  have hHltp : H < p := by omega
  have hproductFac :
      (consecutiveProduct N H).factorization p = k.factorization p :=
    factorization_consecutiveProduct_eq_of_mem_prime_dvd hk hp hHltp hpk
  have hpProduct : p ∣ consecutiveProduct N H := by
    rw [consecutiveProduct]
    exact dvd_trans hpk (Finset.dvd_prod_of_mem id hk)
  have hpMemProduct : p ∈ (consecutiveProduct N H).primeFactors :=
    hp.mem_primeFactors hpProduct (consecutiveProduct_ne_zero N H)
  have hpMemProductComponent :
      p ∈ (squarefreeComponent (consecutiveProduct N H)).primeFactors :=
    mem_primeFactors_squarefreeComponent_iff.mpr
      ⟨hpMemProduct, by simpa only [hproductFac] using hkParity.2⟩
  have hpMemFactorialComponent :
      p ∈ (squarefreeComponent a.factorial).primeFactors := by
    rw [← haData.2.2]
    exact hpMemProductComponent
  have hpDvdFactorial : p ∣ a.factorial :=
    Nat.dvd_of_mem_primeFactors
      (mem_primeFactors_squarefreeComponent_iff.mp
        hpMemFactorialComponent).1
  have hpLeA : p ≤ a := hp.dvd_factorial.mp hpDvdFactorial
  omega

/-- Canonical square decomposition of one type-`F₃` interval element, with
the precise smoothness support needed in Lemma 4.3. -/
theorem factorialThreeInterval_element_eq_smoothCoefficient_mul_sq
    {N H a k : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hk : k ∈ consecutiveInterval N H) :
    ∃ c n : ℕ,
      0 < c ∧ 0 < n ∧ Squarefree c ∧
      (∀ p : ℕ, p.Prime → p ∣ c → p ≤ max a H) ∧
      c * n ^ 2 = k := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  let q : PositiveNat := ⟨k, hkPos⟩
  refine ⟨squarefreeComponent k, squarePart q,
    squarefreeComponent_pos_of_positive q, squarePart_pos q,
    squarefree_squarefreeComponent k, ?_, ?_⟩
  · intro p hp hpCoeff
    exact prime_dvd_squarefreeComponent_le_max_of_factorialThree
      haData hk hp hpCoeff
  · have hspec := squarePart_spec q
    dsimp only [q] at hspec
    nlinarith

/-! ## Product envelope and the quantitative selection step -/

/-- Product of the canonical squarefree coefficients across an interval. -/
noncomputable def factorialIntervalCoefficientProduct (N H : ℕ) : ℕ :=
  ∏ k ∈ consecutiveInterval N H, squarefreeComponent k

/-- The exact source-shaped coefficient envelope.  The exponent counts
interval multiples while the prime range is allowed to extend to `P`. -/
noncomputable def factorialCoefficientEnvelope (H P : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 P).filter Nat.Prime, p ^ (H / p + 1)

theorem factorialIntervalCoefficientProduct_pos (N H : ℕ) :
    0 < factorialIntervalCoefficientProduct N H := by
  rw [factorialIntervalCoefficientProduct]
  apply Finset.prod_pos
  intro k hk
  exact squarefreeComponent_pos_of_positive ⟨k, by
    have := (Finset.mem_Ioc.mp hk).1
    omega⟩

theorem factorialCoefficientEnvelope_pos (H P : ℕ) :
    0 < factorialCoefficientEnvelope H P := by
  rw [factorialCoefficientEnvelope]
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Finset.mem_filter.mp hp).2.pos _

private theorem factorization_factorialIntervalCoefficientProduct_le_count
    (N H p : ℕ) (hp : p.Prime) :
    (factorialIntervalCoefficientProduct N H).factorization p ≤
      (intervalMultiples N H p).card := by
  rw [factorialIntervalCoefficientProduct, Nat.factorization_prod_apply]
  · calc
      ∑ k ∈ consecutiveInterval N H,
          (squarefreeComponent k).factorization p ≤
          ∑ k ∈ consecutiveInterval N H, if p ∣ k then 1 else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkPos : 0 < k := by
          have := (Finset.mem_Ioc.mp hk).1
          omega
        by_cases hpk : p ∣ k
        · simp only [if_pos hpk]
          exact (Nat.squarefree_iff_factorization_le_one
            (squarefreeComponent_pos_of_positive ⟨k, hkPos⟩).ne').mp
              (squarefree_squarefreeComponent k) p
        · have hpCoeff : ¬p ∣ squarefreeComponent k := by
            intro hpCoeff
            have hmem : p ∈ (squarefreeComponent k).primeFactors :=
              hp.mem_primeFactors hpCoeff
                (squarefreeComponent_pos_of_positive ⟨k, hkPos⟩).ne'
            exact hpk (Nat.dvd_of_mem_primeFactors
              (mem_primeFactors_squarefreeComponent_iff.mp hmem).1)
          have hfacZero :
              (squarefreeComponent k).factorization p = 0 := by
            by_contra hne
            have hone : 1 ≤ (squarefreeComponent k).factorization p :=
              Nat.one_le_iff_ne_zero.mpr hne
            exact hpCoeff ((hp.dvd_iff_one_le_factorization
              (squarefreeComponent_pos_of_positive ⟨k, hkPos⟩).ne').mpr hone)
          simp only [if_neg hpk]
          exact hfacZero.le
      _ = (intervalMultiples N H p).card := by
        simp [intervalMultiples]
  · intro k hk
    exact (squarefreeComponent_pos_of_positive ⟨k, by
      have := (Finset.mem_Ioc.mp hk).1
      omega⟩).ne'

private theorem factorialCoefficientEnvelope_exponent_le_factorization
    {H P p : ℕ} (hp : p.Prime) (hpLe : p ≤ P) :
    H / p + 1 ≤ (factorialCoefficientEnvelope H P).factorization p := by
  rw [factorialCoefficientEnvelope, Nat.factorization_prod_apply]
  · have hpMem : p ∈ (Finset.Icc 2 P).filter Nat.Prime := by
      simp [hp, hp.two_le, hpLe]
    calc
      H / p + 1 = (p ^ (H / p + 1)).factorization p := by
        exact (Nat.factorization_pow_self hp).symm
      _ ≤ ∑ q ∈ (Finset.Icc 2 P).filter Nat.Prime,
          (q ^ (H / q + 1)).factorization p := by
        exact Finset.single_le_sum
          (s := (Finset.Icc 2 P).filter Nat.Prime)
          (f := fun q => (q ^ (H / q + 1)).factorization p)
          (fun _ _ => Nat.zero_le _) hpMem
  · intro q hq
    exact pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero

/-- Exact divisibility form of the Lemma 4.3 coefficient-product estimate. -/
theorem factorialIntervalCoefficientProduct_dvd_factorialCoefficientEnvelope
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial) :
    factorialIntervalCoefficientProduct N H ∣
      factorialCoefficientEnvelope H (max a H) := by
  rw [← Nat.factorization_le_iff_dvd
    (factorialIntervalCoefficientProduct_pos N H).ne'
    (factorialCoefficientEnvelope_pos H (max a H)).ne']
  intro p
  by_cases hp : p.Prime
  · by_cases hpLe : p ≤ max a H
    · calc
        (factorialIntervalCoefficientProduct N H).factorization p ≤
            (intervalMultiples N H p).card :=
          factorization_factorialIntervalCoefficientProduct_le_count N H p hp
        _ ≤ H / p + 1 := card_intervalMultiples_le N H p hp.pos
        _ ≤ (factorialCoefficientEnvelope H (max a H)).factorization p :=
          factorialCoefficientEnvelope_exponent_le_factorization hp hpLe
    · have hzero :
          (factorialIntervalCoefficientProduct N H).factorization p = 0 := by
        rw [factorialIntervalCoefficientProduct, Nat.factorization_prod_apply]
        · apply Finset.sum_eq_zero
          intro k hk
          have hkPos : 0 < k := by
            have := (Finset.mem_Ioc.mp hk).1
            omega
          have hnotDvd : ¬p ∣ squarefreeComponent k := by
            intro hpdvd
            exact hpLe
              (prime_dvd_squarefreeComponent_le_max_of_factorialThree
                haData hk hp hpdvd)
          by_contra hne
          have hone : 1 ≤ (squarefreeComponent k).factorization p :=
            Nat.one_le_iff_ne_zero.mpr hne
          exact hnotDvd ((hp.dvd_iff_one_le_factorization
            (squarefreeComponent_pos_of_positive ⟨k, hkPos⟩).ne').mpr hone)
        · intro k hk
          exact (squarefreeComponent_pos_of_positive ⟨k, by
            have := (Finset.mem_Ioc.mp hk).1
            omega⟩).ne'
      rw [hzero]
      exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Logarithm of the exact Lemma 4.3 envelope. -/
theorem log_factorialCoefficientEnvelope (H P : ℕ) :
    Real.log (factorialCoefficientEnvelope H P : ℝ) =
      ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        (H / p + 1 : ℕ) * Real.log p := by
  rw [factorialCoefficientEnvelope, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    norm_cast
    exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero

/-- Explicit source-shaped logarithmic envelope
`O(H log P + P)`. -/
theorem log_factorialCoefficientEnvelope_le
    (H P : ℕ) (hP : 0 < P) :
    Real.log (factorialCoefficientEnvelope H P : ℝ) ≤
      Real.log 4 * H * (2 + Real.log P) + Real.log 4 * P := by
  rw [log_factorialCoefficientEnvelope]
  have hterm (p : ℕ) (hp : p ∈ (Finset.Icc 2 P).filter Nat.Prime) :
      ((H / p + 1 : ℕ) : ℝ) * Real.log p ≤
        ((H : ℝ) / p + 1) * Real.log p := by
    apply mul_le_mul_of_nonneg_right
    · simp only [Nat.cast_add, Nat.cast_one]
      linarith [show ((H / p : ℕ) : ℝ) ≤ (H : ℝ) / p from Nat.cast_div_le]
    · exact Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  calc
    ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ((H / p + 1 : ℕ) : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ((H : ℝ) / p + 1) * Real.log p := Finset.sum_le_sum hterm
    _ = (H : ℝ) * weightedPrimeLogSum P + Chebyshev.theta P := by
      rw [weightedPrimeLogSum, Chebyshev.theta_eq_sum_Icc]
      simp only [Nat.floor_natCast]
      have hsets : (Finset.Icc 0 P).filter Nat.Prime =
          (Finset.Icc 2 P).filter Nat.Prime := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hp
          exact ⟨⟨hp.2.two_le, hp.1.2⟩, hp.2⟩
        · intro hp
          exact ⟨⟨Nat.zero_le _, hp.1.2⟩, hp.2⟩
      rw [hsets]
      simp_rw [div_eq_mul_inv, add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        ring
      · simp
    _ ≤ (H : ℝ) * (Real.log 4 * (2 + Real.log P)) +
        Real.log 4 * P := by
      gcongr
      · exact weightedPrimeLogSum_le P hP
      · exact Chebyshev.theta_le_log4_mul_x (by positivity)
    _ = Real.log 4 * H * (2 + Real.log P) + Real.log 4 * P := by ring

/-- The logarithm of the interval coefficient product is the sum of the
individual coefficient logarithms. -/
theorem log_factorialIntervalCoefficientProduct (N H : ℕ) :
    Real.log (factorialIntervalCoefficientProduct N H : ℝ) =
      ∑ k ∈ consecutiveInterval N H, Real.log (squarefreeComponent k) := by
  rw [factorialIntervalCoefficientProduct, Nat.cast_prod, Real.log_prod]
  intro k hk
  norm_cast
  exact (squarefreeComponent_pos_of_positive ⟨k, by
    have := (Finset.mem_Ioc.mp hk).1
    omega⟩).ne'

/-- The explicit logarithmic threshold delivered by splitting the interval
into two halves and averaging the coefficient-product estimate. -/
noncomputable def factorialCoefficientSelectionLogBound (H P : ℕ) : ℝ :=
  3 * Real.log 4 * (2 + Real.log P + (P : ℝ) / H)

private theorem factorial_leftCoefficientHalf_subset (N H : ℕ) :
    leftCoefficientHalf N H ⊆ consecutiveInterval N H := by
  intro k hk
  simp only [leftCoefficientHalf, consecutiveInterval, Finset.mem_Ioc] at hk ⊢
  omega

private theorem factorial_rightCoefficientHalf_subset (N H : ℕ) :
    rightCoefficientHalf N H ⊆ consecutiveInterval N H := by
  intro k hk
  simp only [rightCoefficientHalf, consecutiveInterval, Finset.mem_Ioc] at hk ⊢
  omega

private theorem log_squarefreeComponent_nonneg
    {N H k : ℕ} (hk : k ∈ consecutiveInterval N H) :
    0 ≤ Real.log (squarefreeComponent k) := by
  apply Real.log_nonneg
  exact_mod_cast squarefreeComponent_pos_of_positive ⟨k, by
    have := (Finset.mem_Ioc.mp hk).1
    omega⟩

private theorem factorial_half_log_sum_le_envelope
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hH : 2 ≤ H) {s : Finset ℕ}
    (hs : s ⊆ consecutiveInterval N H) :
    ∑ k ∈ s, Real.log (squarefreeComponent k) ≤
      Real.log 4 * H * (2 + Real.log ((max a H : ℕ) : ℝ)) +
        Real.log 4 * max a H := by
  calc
    ∑ k ∈ s, Real.log (squarefreeComponent k) ≤
        ∑ k ∈ consecutiveInterval N H,
          Real.log (squarefreeComponent k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro k hk _
      exact log_squarefreeComponent_nonneg hk
    _ = Real.log (factorialIntervalCoefficientProduct N H : ℝ) :=
      (log_factorialIntervalCoefficientProduct N H).symm
    _ ≤ Real.log (factorialCoefficientEnvelope H (max a H) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast factorialIntervalCoefficientProduct_pos N H
      · exact_mod_cast Nat.le_of_dvd
          (factorialCoefficientEnvelope_pos H (max a H))
          (factorialIntervalCoefficientProduct_dvd_factorialCoefficientEnvelope
            haData)
    _ ≤ Real.log 4 * H * (2 + Real.log ((max a H : ℕ) : ℝ)) +
        Real.log 4 * max a H :=
      log_factorialCoefficientEnvelope_le H (max a H) (by omega)

private theorem factorial_three_mul_half_card_ge
    (N H : ℕ) (hH : 2 ≤ H) :
    H ≤ 3 * (leftCoefficientHalf N H).card ∧
      H ≤ 3 * (rightCoefficientHalf N H).card := by
  rw [card_leftCoefficientHalf, card_rightCoefficientHalf]
  omega

private theorem factorial_half_constant_sum_ge_envelope
    (H P : ℕ) (hH : 2 ≤ H) (hP : H ≤ P)
    {s : Finset ℕ} (hcard : H ≤ 3 * s.card) :
    Real.log 4 * H * (2 + Real.log P) + Real.log 4 * P ≤
      ∑ _k ∈ s, factorialCoefficientSelectionLogBound H P := by
  have hHReal : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hbase : 0 ≤ Real.log 4 *
      (2 + Real.log P + (P : ℝ) / H) := by
    positivity
  have hcardReal : (H : ℝ) ≤ 3 * s.card := by exact_mod_cast hcard
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [factorialCoefficientSelectionLogBound]
  calc
    Real.log 4 * H * (2 + Real.log P) + Real.log 4 * P =
        (H : ℝ) *
          (Real.log 4 * (2 + Real.log P + (P : ℝ) / H)) := by
      field_simp
    _ ≤ (3 * s.card : ℝ) *
        (Real.log 4 * (2 + Real.log P + (P : ℝ) / H)) := by
      gcongr
    _ = (s.card : ℝ) *
        (3 * Real.log 4 * (2 + Real.log P + (P : ℝ) / H)) := by
      ring

private theorem factorial_exists_in_half_with_small_log
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hH : 2 ≤ H) {s : Finset ℕ}
    (hs : s ⊆ consecutiveInterval N H)
    (hsNonempty : s.Nonempty) (hcard : H ≤ 3 * s.card) :
    ∃ k ∈ s, Real.log (squarefreeComponent k) ≤
      factorialCoefficientSelectionLogBound H (max a H) := by
  apply Finset.exists_le_of_sum_le hsNonempty
  exact (factorial_half_log_sum_le_envelope haData hH hs).trans
    (factorial_half_constant_sum_ge_envelope H (max a H) hH
      (Nat.le_max_right a H) hcard)

/-- Two ordered interval positions have squarefree coefficients within the
explicit averaged factorial-envelope budget. -/
theorem exists_two_factorial_coefficients_with_small_log
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hH : 2 ≤ H) :
    ∃ k₁ k₂ : ℕ,
      k₁ ∈ consecutiveInterval N H ∧
      k₂ ∈ consecutiveInterval N H ∧ k₁ < k₂ ∧
      Real.log (squarefreeComponent k₁) ≤
        factorialCoefficientSelectionLogBound H (max a H) ∧
      Real.log (squarefreeComponent k₂) ≤
        factorialCoefficientSelectionLogBound H (max a H) := by
  have hcards := factorial_three_mul_half_card_ge N H hH
  have hleftNonempty : (leftCoefficientHalf N H).Nonempty := by
    rw [← Finset.card_pos, card_leftCoefficientHalf]
    omega
  have hrightNonempty : (rightCoefficientHalf N H).Nonempty := by
    rw [← Finset.card_pos, card_rightCoefficientHalf]
    omega
  obtain ⟨k₁, hk₁, hk₁Log⟩ := factorial_exists_in_half_with_small_log
    haData hH (factorial_leftCoefficientHalf_subset N H)
      hleftNonempty hcards.1
  obtain ⟨k₂, hk₂, hk₂Log⟩ := factorial_exists_in_half_with_small_log
    haData hH (factorial_rightCoefficientHalf_subset N H)
      hrightNonempty hcards.2
  have hk₁Interval := factorial_leftCoefficientHalf_subset N H hk₁
  have hk₂Interval := factorial_rightCoefficientHalf_subset N H hk₂
  refine ⟨k₁, k₂, hk₁Interval, hk₂Interval, ?_, hk₁Log, hk₂Log⟩
  have hk₁' := Finset.mem_Ioc.mp hk₁
  have hk₂' := Finset.mem_Ioc.mp hk₂
  omega

/-- Exponential form of the two selected coefficient bounds. -/
theorem exists_two_factorial_coefficients_with_exp_bound
    {N H a : ℕ}
    (haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial)
    (hH : 2 ≤ H) :
    ∃ k₁ k₂ : ℕ,
      k₁ ∈ consecutiveInterval N H ∧
      k₂ ∈ consecutiveInterval N H ∧ k₁ < k₂ ∧
      (squarefreeComponent k₁ : ℝ) ≤
        Real.exp (factorialCoefficientSelectionLogBound H (max a H)) ∧
      (squarefreeComponent k₂ : ℝ) ≤
        Real.exp (factorialCoefficientSelectionLogBound H (max a H)) := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk₁k₂, hk₁Log, hk₂Log⟩ :=
    exists_two_factorial_coefficients_with_small_log haData hH
  refine ⟨k₁, k₂, hk₁, hk₂, hk₁k₂, ?_, ?_⟩
  · calc
      (squarefreeComponent k₁ : ℝ) =
          Real.exp (Real.log (squarefreeComponent k₁ : ℝ)) := by
            rw [Real.exp_log]
            exact_mod_cast squarefreeComponent_pos_of_positive ⟨k₁, by
              have := (Finset.mem_Ioc.mp hk₁).1
              omega⟩
      _ ≤ Real.exp (factorialCoefficientSelectionLogBound H (max a H)) :=
        Real.exp_le_exp.mpr hk₁Log
  · calc
      (squarefreeComponent k₂ : ℝ) =
          Real.exp (Real.log (squarefreeComponent k₂ : ℝ)) := by
            rw [Real.exp_log]
            exact_mod_cast squarefreeComponent_pos_of_positive ⟨k₂, by
              have := (Finset.mem_Ioc.mp hk₂).1
              omega⟩
      _ ≤ Real.exp (factorialCoefficientSelectionLogBound H (max a H)) :=
        Real.exp_le_exp.mpr hk₂Log

/-- The exact arithmetic core of Tao's Lemma 4.3: two interval elements
produce a square relation with positive squarefree coefficients supported on
primes at most `P = max a H`.  The later averaging layer sharpens the sizes
of the two coefficients. -/
theorem factorialThreeInterval_exists_smooth_squareRelation
    {N H : ℕ} (hf3 : IsFactorialThreeInterval N H) (hH : 2 ≤ H) :
    ∃ a c₁ c₂ n₁ n₂ h : ℕ,
      1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial ∧
      0 < c₁ ∧ 0 < c₂ ∧ 0 < n₁ ∧ 0 < n₂ ∧
      Squarefree c₁ ∧ Squarefree c₂ ∧
      (∀ p : ℕ, p.Prime → p ∣ c₁ → p ≤ max a H) ∧
      (∀ p : ℕ, p.Prime → p ∣ c₂ → p ≤ max a H) ∧
      0 < h ∧ h < H ∧
      c₁ * n₁ ^ 2 + h = c₂ * n₂ ^ 2 ∧
      c₁ * n₁ ^ 2 ∈ consecutiveInterval N H ∧
      c₂ * n₂ ^ 2 ∈ consecutiveInterval N H := by
  obtain ⟨_hHpos, a, ha, haN, hcomponent⟩ := hf3
  have hk₁ : N + 1 ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hk₂ : N + 2 ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  let haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial := ⟨ha, haN, hcomponent⟩
  obtain ⟨c₁, n₁, hc₁, hn₁, hc₁sf, hc₁smooth, hc₁eq⟩ :=
    factorialThreeInterval_element_eq_smoothCoefficient_mul_sq haData hk₁
  obtain ⟨c₂, n₂, hc₂, hn₂, hc₂sf, hc₂smooth, hc₂eq⟩ :=
    factorialThreeInterval_element_eq_smoothCoefficient_mul_sq haData hk₂
  refine ⟨a, c₁, c₂, n₁, n₂, 1, ha, haN, hcomponent,
    hc₁, hc₂, hn₁, hn₂, hc₁sf, hc₂sf, hc₁smooth, hc₂smooth,
    by norm_num, by omega, ?_, ?_, ?_⟩
  · omega
  · simpa only [hc₁eq] using hk₁
  · simpa only [hc₂eq] using hk₂

/-- Tao's Lemma 4.3 in explicit finite form.  The two squarefree,
`P`-smooth coefficients come from opposite halves of the interval and are
bounded by the exponential of the averaged coefficient-product envelope. -/
theorem factorialThreeInterval_exists_bounded_smooth_squareRelation
    {N H : ℕ} (hf3 : IsFactorialThreeInterval N H) (hH : 2 ≤ H) :
    ∃ a c₁ c₂ n₁ n₂ h : ℕ,
      1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial ∧
      0 < c₁ ∧ 0 < c₂ ∧ 0 < n₁ ∧ 0 < n₂ ∧
      Squarefree c₁ ∧ Squarefree c₂ ∧
      (∀ p : ℕ, p.Prime → p ∣ c₁ → p ≤ max a H) ∧
      (∀ p : ℕ, p.Prime → p ∣ c₂ → p ≤ max a H) ∧
      (c₁ : ℝ) ≤
        Real.exp (factorialCoefficientSelectionLogBound H (max a H)) ∧
      (c₂ : ℝ) ≤
        Real.exp (factorialCoefficientSelectionLogBound H (max a H)) ∧
      0 < h ∧ h < H ∧
      c₁ * n₁ ^ 2 + h = c₂ * n₂ ^ 2 ∧
      c₁ * n₁ ^ 2 ∈ consecutiveInterval N H ∧
      c₂ * n₂ ^ 2 ∈ consecutiveInterval N H := by
  obtain ⟨_hHpos, a, ha, haN, hcomponent⟩ := hf3
  let haData : 1 ≤ a ∧ a < N ∧
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial := ⟨ha, haN, hcomponent⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, hk₁k₂, hk₁Bound, hk₂Bound⟩ :=
    exists_two_factorial_coefficients_with_exp_bound haData hH
  have hk₁Pos : 0 < k₁ := by
    have := (Finset.mem_Ioc.mp hk₁).1
    omega
  have hk₂Pos : 0 < k₂ := by
    have := (Finset.mem_Ioc.mp hk₂).1
    omega
  let q₁ : PositiveNat := ⟨k₁, hk₁Pos⟩
  let q₂ : PositiveNat := ⟨k₂, hk₂Pos⟩
  have hk₁Eq : squarefreeComponent k₁ * squarePart q₁ ^ 2 = k₁ := by
    have hspec := squarePart_spec q₁
    dsimp only [q₁] at hspec
    nlinarith
  have hk₂Eq : squarefreeComponent k₂ * squarePart q₂ ^ 2 = k₂ := by
    have hspec := squarePart_spec q₂
    dsimp only [q₂] at hspec
    nlinarith
  refine ⟨a, squarefreeComponent k₁, squarefreeComponent k₂,
    squarePart q₁, squarePart q₂, k₂ - k₁,
    ha, haN, hcomponent,
    squarefreeComponent_pos_of_positive q₁,
    squarefreeComponent_pos_of_positive q₂,
    squarePart_pos q₁, squarePart_pos q₂,
    squarefree_squarefreeComponent k₁, squarefree_squarefreeComponent k₂,
    ?_, ?_, hk₁Bound, hk₂Bound,
    Nat.sub_pos_of_lt hk₁k₂, ?_, ?_, ?_, ?_⟩
  · intro p hp hpCoeff
    exact prime_dvd_squarefreeComponent_le_max_of_factorialThree
      haData hk₁ hp hpCoeff
  · intro p hp hpCoeff
    exact prime_dvd_squarefreeComponent_le_max_of_factorialThree
      haData hk₂ hp hpCoeff
  · have hk₁Mem := Finset.mem_Ioc.mp hk₁
    have hk₂Mem := Finset.mem_Ioc.mp hk₂
    omega
  · omega
  · simpa only [hk₁Eq] using hk₁
  · simpa only [hk₂Eq] using hk₂

end

end Tao2026
