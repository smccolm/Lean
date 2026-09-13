import Tao2026.PrimeCharacterSums
import Tao2026.CoefficientBounds

/-!
# Mertens bookkeeping for the small-prime fiftieth moment

The lcm in the ordered tuple expansion contains each selected prime only
once.  This file records the exact distinct-prime support and multiplicity
identities needed to apply the weighted prime Mertens estimate without
incorrectly treating repeated coordinates as independent denominators.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- The distinct primes selected by an ordered small-prime tuple. -/
def taoSmallPrimeTupleSupport (t : Fin 50 → ℕ × ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin 50)).image fun k => (t k).2

theorem mem_taoSmallPrimeTupleSupport
    {t : Fin 50 → ℕ × ℕ} {p : ℕ} :
    p ∈ taoSmallPrimeTupleSupport t ↔ ∃ k : Fin 50, (t k).2 = p := by
  simp [taoSmallPrimeTupleSupport]

/-- The number of coordinates at which a selected prime occurs. -/
def taoSmallPrimeTupleMultiplicity
    (t : Fin 50 → ℕ × ℕ) (p : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 50)).filter fun k => (t k).2 = p).card

/-- Every prime in the distinct support of an actual small-prime tuple is
prime and lies below the small-prime cutoff. -/
theorem taoSmallPrimeTupleSupport_prime_le
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    {p : ℕ} (hp : p ∈ taoSmallPrimeTupleSupport t) :
    Nat.Prime p ∧ p ≤ taoSmallAntiSievePrimeCutoff x := by
  rcases mem_taoSmallPrimeTupleSupport.mp hp with ⟨k, rfl⟩
  have hk := mem_taoSmallAntiSieveIndices.mp
    (Fintype.mem_piFinset.mp ht k)
  exact ⟨hk.2.2.1, hk.2.2.2.1⟩

/-- Distinct primes in the support are pairwise coprime. -/
theorem taoSmallPrimeTupleSupport_pairwise_coprime
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    Set.Pairwise (taoSmallPrimeTupleSupport t) Nat.Coprime := by
  intro p hp q hq hpq
  have hpPrime := (taoSmallPrimeTupleSupport_prime_le ht hp).1
  have hqPrime := (taoSmallPrimeTupleSupport_prime_le ht hq).1
  rw [hpPrime.coprime_iff_not_dvd]
  intro hpdvd
  rcases (Nat.dvd_prime hqPrime).mp hpdvd with hpOne | hpEq
  · exact hpPrime.ne_one hpOne
  · exact hpq hpEq

/-- The tuple lcm is exactly the product of its distinct selected primes. -/
theorem taoSmallPrimeTupleModulus_eq_support_prod
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    taoSmallPrimeTupleModulus t =
      (taoSmallPrimeTupleSupport t).prod id := by
  rw [taoSmallPrimeTupleModulus, Finset.lcm_eq_lcm_image]
  exact Finset.lcm_eq_prod (taoSmallPrimeTupleSupport_pairwise_coprime ht)

/-- The distinct support has at most fifty elements. -/
theorem card_taoSmallPrimeTupleSupport_le_fifty
    (t : Fin 50 → ℕ × ℕ) :
    (taoSmallPrimeTupleSupport t).card ≤ 50 := by
  unfold taoSmallPrimeTupleSupport
  simpa using Finset.card_image_le
    (s := (Finset.univ : Finset (Fin 50))) (f := fun k => (t k).2)

/-- A support prime occurs in at least one tuple coordinate. -/
theorem taoSmallPrimeTupleMultiplicity_pos
    {t : Fin 50 → ℕ × ℕ} {p : ℕ}
    (hp : p ∈ taoSmallPrimeTupleSupport t) :
    0 < taoSmallPrimeTupleMultiplicity t p := by
  unfold taoSmallPrimeTupleMultiplicity
  rw [Finset.card_pos]
  rcases mem_taoSmallPrimeTupleSupport.mp hp with ⟨k, hk⟩
  exact ⟨k, by simp [hk]⟩

/-- Regrouping the fifty logarithmic weights by distinct prime and
multiplicity is an exact identity. -/
theorem prod_log_eq_prod_support_pow_multiplicity
    (t : Fin 50 → ℕ × ℕ) :
    (∏ k, Real.log (t k).2) =
      ∏ p ∈ taoSmallPrimeTupleSupport t,
        Real.log p ^ taoSmallPrimeTupleMultiplicity t p := by
  rw [← Finset.prod_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin 50)))
    (t := taoSmallPrimeTupleSupport t)
    (g := fun k => (t k).2)
    (f := fun p => Real.log p)]
  · apply Finset.prod_congr rfl
    intro p hp
    simp [taoSmallPrimeTupleMultiplicity]
  · intro k _hk
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

/-- The support multiplicities sum to the number of tuple coordinates. -/
theorem sum_taoSmallPrimeTupleMultiplicity
    (t : Fin 50 → ℕ × ℕ) :
    ∑ p ∈ taoSmallPrimeTupleSupport t,
        taoSmallPrimeTupleMultiplicity t p = 50 := by
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin 50)))
    (t := taoSmallPrimeTupleSupport t)
    (g := fun k => (t k).2)
    (f := fun _p : ℕ => (1 : ℕ))
    (fun k _hk => Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  simpa [taoSmallPrimeTupleMultiplicity] using h

/-- Exact Mertens-ready factorization of the logarithmic tuple coefficient:
one reciprocal is attached to every distinct support prime, while repeated
occurrences remain visible through their multiplicities. -/
theorem prod_log_div_tupleModulus_eq_prod_support
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t =
      ∏ p ∈ taoSmallPrimeTupleSupport t,
        Real.log p ^ taoSmallPrimeTupleMultiplicity t p / p := by
  rw [prod_log_eq_prod_support_pow_multiplicity,
    taoSmallPrimeTupleModulus_eq_support_prod ht]
  simp only [Nat.cast_prod, id_eq]
  rw [Finset.prod_div_distrib]

/-- The product of the `log p / p` factors contributed by the distinct
selected primes. -/
def taoSmallPrimeTupleMertensWeight (t : Fin 50 → ℕ × ℕ) : ℝ :=
  ∏ p ∈ taoSmallPrimeTupleSupport t, Real.log p / p

/-- The logarithmic factors left by repeated occurrences of support primes. -/
def taoSmallPrimeTupleRepeatedLogWeight (t : Fin 50 → ℕ × ℕ) : ℝ :=
  ∏ p ∈ taoSmallPrimeTupleSupport t,
    Real.log p ^ (taoSmallPrimeTupleMultiplicity t p - 1)

/-- Exact separation of a support-prime factor into its Mertens weight and
the logarithms from its repeated occurrences. -/
theorem pow_log_div_eq_mertens_mul_repeated
    {t : Fin 50 → ℕ × ℕ} {p : ℕ}
    (hp : p ∈ taoSmallPrimeTupleSupport t) :
    Real.log p ^ taoSmallPrimeTupleMultiplicity t p / p =
      (Real.log p / p) *
        Real.log p ^ (taoSmallPrimeTupleMultiplicity t p - 1) := by
  have hm := taoSmallPrimeTupleMultiplicity_pos hp
  calc
    Real.log p ^ taoSmallPrimeTupleMultiplicity t p / p =
        (Real.log p ^ (taoSmallPrimeTupleMultiplicity t p - 1) *
          Real.log p) / p := by
      congr 1
      rw [← pow_succ]
      congr
      omega
    _ = (Real.log p / p) *
        Real.log p ^ (taoSmallPrimeTupleMultiplicity t p - 1) := by ring

/-- Exact global separation into the distinct-prime Mertens weight and the
remaining repeated logarithmic weight. -/
theorem prod_log_div_tupleModulus_eq_mertens_mul_repeated
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t =
      taoSmallPrimeTupleMertensWeight t *
        taoSmallPrimeTupleRepeatedLogWeight t := by
  rw [prod_log_div_tupleModulus_eq_prod_support ht]
  unfold taoSmallPrimeTupleMertensWeight
  unfold taoSmallPrimeTupleRepeatedLogWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact pow_log_div_eq_mertens_mul_repeated hp

/-- The total number of repeated occurrences is `50 - #support`. -/
theorem sum_taoSmallPrimeTupleMultiplicity_sub_one
    (t : Fin 50 → ℕ × ℕ) :
    ∑ p ∈ taoSmallPrimeTupleSupport t,
        (taoSmallPrimeTupleMultiplicity t p - 1) =
      50 - (taoSmallPrimeTupleSupport t).card := by
  have hsplit :
      (∑ p ∈ taoSmallPrimeTupleSupport t,
          (taoSmallPrimeTupleMultiplicity t p - 1)) +
        (taoSmallPrimeTupleSupport t).card = 50 := by
    calc
      (∑ p ∈ taoSmallPrimeTupleSupport t,
          (taoSmallPrimeTupleMultiplicity t p - 1)) +
          (taoSmallPrimeTupleSupport t).card =
          ∑ p ∈ taoSmallPrimeTupleSupport t,
            ((taoSmallPrimeTupleMultiplicity t p - 1) + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ p ∈ taoSmallPrimeTupleSupport t,
          taoSmallPrimeTupleMultiplicity t p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hm := taoSmallPrimeTupleMultiplicity_pos hp
        omega
      _ = 50 := sum_taoSmallPrimeTupleMultiplicity t
  omega

/-- The existing finite weighted-prime sum is nonnegative. -/
theorem weightedPrimeLogSum_nonneg (Y : ℕ) :
    0 ≤ weightedPrimeLogSum Y := by
  unfold weightedPrimeLogSum
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
    (Nat.cast_nonneg p)

/-- Every individual support Mertens factor is bounded by the complete
weighted prime sum up to the small-prime cutoff. -/
theorem support_log_div_le_weightedPrimeLogSum
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    {p : ℕ} (hp : p ∈ taoSmallPrimeTupleSupport t) :
    Real.log p / p ≤ weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) := by
  have hpData := taoSmallPrimeTupleSupport_prime_le ht hp
  have hpMem : p ∈
      (Finset.Icc 2 (taoSmallAntiSievePrimeCutoff x)).filter Nat.Prime := by
    simp [hpData.1, hpData.1.two_le, hpData.2]
  unfold weightedPrimeLogSum
  exact Finset.single_le_sum
    (s := (Finset.Icc 2 (taoSmallAntiSievePrimeCutoff x)).filter Nat.Prime)
    (f := fun q : ℕ => Real.log q / q)
    (fun q hq => by
      have hqPrime := (Finset.mem_filter.mp hq).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqPrime.one_le))
        (Nat.cast_nonneg q)) hpMem

/-- Pointwise product form of the finite weighted Mertens bound on the
distinct support. -/
theorem taoSmallPrimeTupleMertensWeight_le_pow
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    taoSmallPrimeTupleMertensWeight t ≤
      weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^
        (taoSmallPrimeTupleSupport t).card := by
  unfold taoSmallPrimeTupleMertensWeight
  calc
    (∏ p ∈ taoSmallPrimeTupleSupport t, Real.log p / p) ≤
        ∏ _p ∈ taoSmallPrimeTupleSupport t,
          weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := (taoSmallPrimeTupleSupport_prime_le ht hp).1
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
          (Nat.cast_nonneg p)
      · intro p hp
        exact support_log_div_le_weightedPrimeLogSum ht hp
    _ = weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^
        (taoSmallPrimeTupleSupport t).card := by simp

/-- The repeated logarithmic factors cost exactly one cutoff logarithm for
each coordinate beyond the distinct support. -/
theorem taoSmallPrimeTupleRepeatedLogWeight_le
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    taoSmallPrimeTupleRepeatedLogWeight t ≤
      Real.log (taoSmallAntiSievePrimeCutoff x) ^
        (50 - (taoSmallPrimeTupleSupport t).card) := by
  have hcutoffTwo : 2 ≤ taoSmallAntiSievePrimeCutoff x := by
    have hzero := mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht (0 : Fin 50))
    exact hzero.2.2.1.two_le.trans hzero.2.2.2.1
  unfold taoSmallPrimeTupleRepeatedLogWeight
  calc
    (∏ p ∈ taoSmallPrimeTupleSupport t,
        Real.log p ^ (taoSmallPrimeTupleMultiplicity t p - 1)) ≤
        ∏ p ∈ taoSmallPrimeTupleSupport t,
          Real.log (taoSmallAntiSievePrimeCutoff x) ^
            (taoSmallPrimeTupleMultiplicity t p - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact pow_nonneg
          (Real.log_nonneg (by exact_mod_cast
            (taoSmallPrimeTupleSupport_prime_le ht hp).1.one_le)) _
      · intro p hp
        apply pow_le_pow_left₀
        · exact Real.log_nonneg (by exact_mod_cast
            (taoSmallPrimeTupleSupport_prime_le ht hp).1.one_le)
        · exact Real.strictMonoOn_log.monotoneOn
            (by
              show (0 : ℝ) < p
              exact_mod_cast (taoSmallPrimeTupleSupport_prime_le ht hp).1.pos)
            (by
              show (0 : ℝ) < taoSmallAntiSievePrimeCutoff x
              exact_mod_cast (lt_of_lt_of_le (by norm_num) hcutoffTwo))
            (by exact_mod_cast (taoSmallPrimeTupleSupport_prime_le ht hp).2)
    _ = Real.log (taoSmallAntiSievePrimeCutoff x) ^
        (∑ p ∈ taoSmallPrimeTupleSupport t,
          (taoSmallPrimeTupleMultiplicity t p - 1)) := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ = Real.log (taoSmallAntiSievePrimeCutoff x) ^
        (50 - (taoSmallPrimeTupleSupport t).card) := by
      rw [sum_taoSmallPrimeTupleMultiplicity_sub_one]

/-- Mertens-ready pointwise bound for the tuple logarithmic coefficient.
Its exponents add to exactly fifty, including all repeated-prime patterns. -/
theorem prod_log_div_tupleModulus_le_mertens_pow_mul_log_pow
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t ≤
      weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^
          (taoSmallPrimeTupleSupport t).card *
        Real.log (taoSmallAntiSievePrimeCutoff x) ^
          (50 - (taoSmallPrimeTupleSupport t).card) := by
  rw [prod_log_div_tupleModulus_eq_mertens_mul_repeated ht]
  exact mul_le_mul
    (taoSmallPrimeTupleMertensWeight_le_pow ht)
    (taoSmallPrimeTupleRepeatedLogWeight_le ht)
    (by
      unfold taoSmallPrimeTupleRepeatedLogWeight
      positivity)
    (pow_nonneg (weightedPrimeLogSum_nonneg _) _)

/-- Fully explicit pointwise version using the proved finite weighted Mertens
estimate. -/
theorem prod_log_div_tupleModulus_le_log4_bound
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t ≤
      (Real.log 4 *
          (2 + Real.log (taoSmallAntiSievePrimeCutoff x))) ^
          (taoSmallPrimeTupleSupport t).card *
        Real.log (taoSmallAntiSievePrimeCutoff x) ^
          (50 - (taoSmallPrimeTupleSupport t).card) := by
  have hcutoffPos : 0 < taoSmallAntiSievePrimeCutoff x := by
    have hzero := mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht (0 : Fin 50))
    exact hzero.2.2.1.pos.trans_le hzero.2.2.2.1
  calc
    (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t ≤
        weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^
            (taoSmallPrimeTupleSupport t).card *
          Real.log (taoSmallAntiSievePrimeCutoff x) ^
            (50 - (taoSmallPrimeTupleSupport t).card) :=
      prod_log_div_tupleModulus_le_mertens_pow_mul_log_pow ht
    _ ≤ (Real.log 4 *
          (2 + Real.log (taoSmallAntiSievePrimeCutoff x))) ^
            (taoSmallPrimeTupleSupport t).card *
          Real.log (taoSmallAntiSievePrimeCutoff x) ^
            (50 - (taoSmallPrimeTupleSupport t).card) := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ (weightedPrimeLogSum_nonneg _)
          (weightedPrimeLogSum_le _ hcutoffPos) _
      · exact pow_nonneg (Real.log_nonneg (by
          exact_mod_cast hcutoffPos)) _

/-- Admissible shifts for one selected small prime. -/
def taoSmallAntiSieveShifts (H p : ℕ) : Finset ℕ :=
  (Finset.Ico 1 H).filter fun l => ¬p ∣ l

theorem mem_taoSmallAntiSieveShifts {H p l : ℕ} :
    l ∈ taoSmallAntiSieveShifts H p ↔
      1 ≤ l ∧ l < H ∧ ¬p ∣ l := by
  simp [taoSmallAntiSieveShifts, and_assoc]

/-- For a fixed prime, there are at most `H` admissible shifts. -/
theorem card_taoSmallAntiSieveShifts_le (H p : ℕ) :
    (taoSmallAntiSieveShifts H p).card ≤ H := by
  calc
    (taoSmallAntiSieveShifts H p).card ≤
        (Finset.Ico 1 H).card := by
      exact Finset.card_filter_le _ _
    _ ≤ H := by simp

/-- The admissible shift tuples over a prescribed ordered prime tuple. -/
def taoSmallAntiSieveShiftTuples
    (H : ℕ) (p : Fin 50 → ℕ) : Finset (Fin 50 → ℕ) :=
  Fintype.piFinset fun k => taoSmallAntiSieveShifts H (p k)

/-- At most `H^50` shift tuples lie over any prescribed ordered prime tuple. -/
theorem card_taoSmallAntiSieveShiftTuples_le
    (H : ℕ) (p : Fin 50 → ℕ) :
    (taoSmallAntiSieveShiftTuples H p).card ≤ H ^ (50 : ℕ) := by
  unfold taoSmallAntiSieveShiftTuples
  rw [Fintype.card_piFinset]
  calc
    (∏ k, (taoSmallAntiSieveShifts H (p k)).card) ≤
        ∏ _k : Fin 50, H := by
      exact Finset.prod_le_prod' fun k _hk =>
        card_taoSmallAntiSieveShifts_le H (p k)
    _ = H ^ (50 : ℕ) := by simp

/-- Actual ordered pair-tuples lying over a prescribed prime tuple. -/
def taoSmallAntiSieveTuplesWithPrimes
    (x H : ℕ) (p : Fin 50 → ℕ) :
    Finset (Fin 50 → ℕ × ℕ) :=
  (Fintype.piFinset
    (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)).filter
      fun t => ∀ k, (t k).2 = p k

/-- Forgetting the prime coordinates maps a fixed-prime fiber into its
admissible shift tuples. -/
theorem taoSmallAntiSieveTupleFst_mem_shiftTuples
    {x H : ℕ} {p : Fin 50 → ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ taoSmallAntiSieveTuplesWithPrimes x H p) :
    (fun k => (t k).1) ∈ taoSmallAntiSieveShiftTuples H p := by
  rw [taoSmallAntiSieveShiftTuples, Fintype.mem_piFinset]
  intro k
  have htData := Finset.mem_filter.mp ht
  have htk := mem_taoSmallAntiSieveIndices.mp
    (Fintype.mem_piFinset.mp htData.1 k)
  rw [mem_taoSmallAntiSieveShifts]
  exact ⟨htk.1, htk.2.1, by simpa [htData.2 k] using htk.2.2.2.2⟩

/-- Each fixed ordered prime tuple has at most `H^50` compatible ordered
pair-tuples. -/
theorem card_taoSmallAntiSieveTuplesWithPrimes_le
    (x H : ℕ) (p : Fin 50 → ℕ) :
    (taoSmallAntiSieveTuplesWithPrimes x H p).card ≤ H ^ (50 : ℕ) := by
  calc
    (taoSmallAntiSieveTuplesWithPrimes x H p).card ≤
        (taoSmallAntiSieveShiftTuples H p).card := by
      apply Finset.card_le_card_of_injOn (fun t k => (t k).1)
      · intro t ht
        exact taoSmallAntiSieveTupleFst_mem_shiftTuples ht
      · intro t ht u hu hfst
        funext k
        apply Prod.ext
        · exact congrFun hfst k
        · have htPrime := (Finset.mem_filter.mp ht).2 k
          have huPrime := (Finset.mem_filter.mp hu).2 k
          exact htPrime.trans huPrime.symm
    _ ≤ H ^ (50 : ℕ) := card_taoSmallAntiSieveShiftTuples_le H p

/-- Ordered 50-tuples of primes from the small-prime range, with shifts
forgotten. -/
def taoSmallPrimeTuples (x : ℕ) : Finset (Fin 50 → ℕ) :=
  Fintype.piFinset fun _ : Fin 50 => taoSmallAntiSievePrimeRange x

/-- Projecting an actual pair-tuple to its prime coordinates lands in the
ordered small-prime tuple space. -/
theorem taoSmallAntiSieveTupleSnd_mem_primeTuples
    {x H : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (fun k => (t k).2) ∈ taoSmallPrimeTuples x := by
  rw [taoSmallPrimeTuples, Fintype.mem_piFinset]
  intro k
  have htk := mem_taoSmallAntiSieveIndices.mp
    (Fintype.mem_piFinset.mp ht k)
  rw [mem_taoSmallAntiSievePrimeRange]
  exact ⟨htk.2.2.1, htk.2.2.2.1⟩

/-- Summing any nonnegative weight which depends only on the prime
coordinates costs at most `H^50` when the shift coordinates are restored.
This is the exact finite fiber bound used before the repeated Mertens sums. -/
theorem sum_taoSmallAntiSieveTuples_le_H_pow_mul_sum_primeTuples
    (x H : ℕ) (F : (Fin 50 → ℕ) → ℝ)
    (hF : ∀ p ∈ taoSmallPrimeTuples x, 0 ≤ F p) :
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        F (fun k => (t k).2)) ≤
      (H : ℝ) ^ (50 : ℕ) *
        ∑ p ∈ taoSmallPrimeTuples x, F p := by
  let S : Finset (Fin 50 → ℕ × ℕ) :=
    Fintype.piFinset fun _ : Fin 50 => taoSmallAntiSieveIndices x H
  let T : Finset (Fin 50 → ℕ) := taoSmallPrimeTuples x
  let g : (Fin 50 → ℕ × ℕ) → (Fin 50 → ℕ) :=
    fun t k => (t k).2
  have hMaps : ∀ t ∈ S, g t ∈ T := by
    intro t ht
    exact taoSmallAntiSieveTupleSnd_mem_primeTuples ht
  calc
    (∑ t ∈ S, F (g t)) =
        ∑ p ∈ T, ∑ _t ∈ S with g _t = p, F p := by
      exact (Finset.sum_fiberwise_of_maps_to' hMaps F).symm
    _ ≤ ∑ p ∈ T, (H : ℝ) ^ (50 : ℕ) * F p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have hFiber : S.filter (fun t => g t = p) =
            taoSmallAntiSieveTuplesWithPrimes x H p := by
          ext t
          unfold taoSmallAntiSieveTuplesWithPrimes
          rw [Finset.mem_filter, Finset.mem_filter]
          change (t ∈ S ∧ g t = p) ↔
            (t ∈ Fintype.piFinset
              (fun _ : Fin 50 => taoSmallAntiSieveIndices x H) ∧
              ∀ k, (t k).2 = p k)
          rw [show S = Fintype.piFinset
              (fun _ : Fin 50 => taoSmallAntiSieveIndices x H) by rfl]
          constructor
          · intro h
            exact ⟨h.1, fun k => congrFun h.2 k⟩
          · intro h
            exact ⟨h.1, funext h.2⟩
        norm_cast
        rw [hFiber]
        exact card_taoSmallAntiSieveTuplesWithPrimes_le x H p
      · exact hF p hp
    _ = (H : ℝ) ^ (50 : ℕ) * ∑ p ∈ T, F p := by
      rw [Finset.mul_sum]

/-- The lcm of a shift-free ordered prime tuple. -/
def taoOrderedPrimeTupleModulus (p : Fin 50 → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 50)).lcm p

/-- The logarithmic lcm coefficient after all shift coordinates have been
forgotten. -/
def taoOrderedPrimeTupleCoefficient (p : Fin 50 → ℕ) : ℝ :=
  (∏ k, Real.log (p k)) / taoOrderedPrimeTupleModulus p

/-- A harmless pair-valued lift used to reuse the exact support and
multiplicity bookkeeping. -/
def taoOrderedPrimeTuplePairLift
    (p : Fin 50 → ℕ) : Fin 50 → ℕ × ℕ :=
  fun k => (1, p k)

/-- Every shift-free small-prime tuple lifts using the admissible shift one
at height two. -/
theorem taoOrderedPrimeTuplePairLift_mem
    {x : ℕ} {p : Fin 50 → ℕ} (hp : p ∈ taoSmallPrimeTuples x) :
    taoOrderedPrimeTuplePairLift p ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x 2) := by
  rw [Fintype.mem_piFinset]
  intro k
  rw [mem_taoSmallAntiSieveIndices]
  simp only [taoOrderedPrimeTuplePairLift]
  have hpk := Fintype.mem_piFinset.mp hp k
  have hpData := mem_taoSmallAntiSievePrimeRange.mp hpk
  exact ⟨by norm_num, by norm_num, hpData.1, hpData.2,
    hpData.1.not_dvd_one⟩

/-- Pair lifting preserves the lcm coefficient definition exactly. -/
theorem taoOrderedPrimeTupleCoefficient_eq_pairLift
    (p : Fin 50 → ℕ) :
    taoOrderedPrimeTupleCoefficient p =
      (∏ k, Real.log (taoOrderedPrimeTuplePairLift p k).2) /
        taoSmallPrimeTupleModulus (taoOrderedPrimeTuplePairLift p) := by
  rfl

/-- Explicit support-cardinality bound for every shift-free ordered prime
tuple. -/
theorem taoOrderedPrimeTupleCoefficient_le_log4_bound
    {x : ℕ} {p : Fin 50 → ℕ} (hp : p ∈ taoSmallPrimeTuples x) :
    taoOrderedPrimeTupleCoefficient p ≤
      (Real.log 4 *
          (2 + Real.log (taoSmallAntiSievePrimeCutoff x))) ^
          (taoSmallPrimeTupleSupport
            (taoOrderedPrimeTuplePairLift p)).card *
        Real.log (taoSmallAntiSievePrimeCutoff x) ^
          (50 - (taoSmallPrimeTupleSupport
            (taoOrderedPrimeTuplePairLift p)).card) := by
  rw [taoOrderedPrimeTupleCoefficient_eq_pairLift]
  exact prod_log_div_tupleModulus_le_log4_bound
    (taoOrderedPrimeTuplePairLift_mem hp)

/-- The complete logarithmic lcm sum over pair-tuples is reduced to its
shift-free ordered-prime version at the exact cost `H^50`. -/
theorem sum_taoSmallAntiSieveTupleCoefficient_le_shiftFree
    (x H : ℕ) :
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t) ≤
      (H : ℝ) ^ (50 : ℕ) *
        ∑ p ∈ taoSmallPrimeTuples x,
          taoOrderedPrimeTupleCoefficient p := by
  have hnonneg : ∀ p ∈ taoSmallPrimeTuples x,
      0 ≤ taoOrderedPrimeTupleCoefficient p := by
    intro p hp
    unfold taoOrderedPrimeTupleCoefficient
    exact div_nonneg (by
      apply Finset.prod_nonneg
      intro k _hk
      have hpk := mem_taoSmallAntiSievePrimeRange.mp
        (Fintype.mem_piFinset.mp hp k)
      exact Real.log_nonneg (by exact_mod_cast hpk.1.one_le))
      (Nat.cast_nonneg _)
  simpa [taoOrderedPrimeTupleCoefficient, taoOrderedPrimeTupleModulus] using
    sum_taoSmallAntiSieveTuples_le_H_pow_mul_sum_primeTuples
      x H taoOrderedPrimeTupleCoefficient hnonneg

/-- Increasing enumeration of a fixed-cardinality subset of naturals. -/
noncomputable def taoFinsetEnumeration
    {S : Finset ℕ} {j : ℕ} (u : ↑(S.powersetCard j)) : Fin j → ℕ :=
  fun i => ↑(u.1.orderIsoOfFin (Finset.mem_powersetCard.mp u.2).2 i)

/-- The range of the increasing enumeration is exactly the underlying
subset. -/
theorem image_taoFinsetEnumeration
    {S : Finset ℕ} {j : ℕ} (u : ↑(S.powersetCard j)) :
    (Finset.univ : Finset (Fin j)).image (taoFinsetEnumeration u) = u.1 := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, _hi, rfl⟩
    exact (u.1.orderIsoOfFin (Finset.mem_powersetCard.mp u.2).2 i).2
  · intro hp
    let a : u.1 := ⟨p, hp⟩
    let i : Fin j :=
      (u.1.orderIsoOfFin (Finset.mem_powersetCard.mp u.2).2).symm a
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    change ↑(u.1.orderIsoOfFin
      (Finset.mem_powersetCard.mp u.2).2 i) = p
    simp [i, a]

/-- Distinct fixed-cardinality subsets have distinct increasing
enumerations. -/
theorem taoFinsetEnumeration_injective
    (S : Finset ℕ) (j : ℕ) :
    Function.Injective
      (@taoFinsetEnumeration S j) := by
  intro u v huv
  apply Subtype.ext
  have himage := congrArg
    (fun f : Fin j → ℕ => (Finset.univ : Finset (Fin j)).image f) huv
  simpa [image_taoFinsetEnumeration] using himage

/-- Every enumerated element remains in the ambient finite set. -/
theorem taoFinsetEnumeration_mem
    {S : Finset ℕ} {j : ℕ} (u : ↑(S.powersetCard j)) (i : Fin j) :
    taoFinsetEnumeration u i ∈ S := by
  exact (Finset.mem_powersetCard.mp u.2).1
    (u.1.orderIsoOfFin (Finset.mem_powersetCard.mp u.2).2 i).2

/-- Products over a subset agree with products over its increasing
enumeration. -/
theorem prod_taoFinsetEnumeration
    {S : Finset ℕ} {j : ℕ} (u : ↑(S.powersetCard j))
    (w : ℕ → ℝ) :
    (∏ p ∈ u.1, w p) = ∏ i, w (taoFinsetEnumeration u i) := by
  rw [← image_taoFinsetEnumeration u]
  rw [Finset.prod_image]
  intro i _hi k _hk hik
  apply (u.1.orderIsoOfFin
    (Finset.mem_powersetCard.mp u.2).2).injective
  exact Subtype.ext hik

/-- The fixed-cardinality elementary symmetric sum of nonnegative weights is
bounded by the corresponding power of the complete sum. -/
theorem sum_powersetCard_prod_le_sum_pow
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p) (j : ℕ) :
    (∑ u ∈ S.powersetCard j, ∏ p ∈ u, w p) ≤
      (∑ p ∈ S, w p) ^ j := by
  let A := (S.powersetCard j).attach
  let B := Fintype.piFinset fun _ : Fin j => S
  let e : ↑(S.powersetCard j) → (Fin j → ℕ) :=
    @taoFinsetEnumeration S j
  have he : Function.Injective e := taoFinsetEnumeration_injective S j
  have heMaps : ∀ u ∈ A, e u ∈ B := by
    intro u _hu
    change e u ∈ Fintype.piFinset fun _ : Fin j => S
    rw [Fintype.mem_piFinset]
    intro i
    exact taoFinsetEnumeration_mem u i
  calc
    (∑ u ∈ S.powersetCard j, ∏ p ∈ u, w p) =
        ∑ u ∈ A, ∏ p ∈ u.1, w p := by
      rw [← Finset.sum_attach]
    _ = ∑ f ∈ A.image e, ∏ i, w (f i) := by
      rw [Finset.sum_image he.injOn]
      apply Finset.sum_congr rfl
      intro u _hu
      exact prod_taoFinsetEnumeration u w
    _ ≤ ∑ f ∈ B, ∏ i, w (f i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        rcases Finset.mem_image.mp hf with ⟨u, hu, rfl⟩
        exact heMaps u hu
      · intro f hfB _hfImage
        apply Finset.prod_nonneg
        intro i _hi
        exact hw (f i) (Fintype.mem_piFinset.mp hfB i)
    _ = (∑ p ∈ S, w p) ^ j := by
      exact (Finset.sum_pow' S w j).symm

/-- Distinct-prime support of a shift-free ordered prime tuple. -/
def taoOrderedPrimeTupleSupport (p : Fin 50 → ℕ) : Finset ℕ :=
  taoSmallPrimeTupleSupport (taoOrderedPrimeTuplePairLift p)

theorem mem_taoOrderedPrimeTupleSupport
    {p : Fin 50 → ℕ} {q : ℕ} :
    q ∈ taoOrderedPrimeTupleSupport p ↔ ∃ k : Fin 50, p k = q := by
  simp [taoOrderedPrimeTupleSupport, taoOrderedPrimeTuplePairLift,
    mem_taoSmallPrimeTupleSupport]

/-- Supports which can occur among ordered 50-tuples from the small-prime
range. -/
def taoSmallPrimeTupleSupports (x : ℕ) : Finset (Finset ℕ) :=
  (taoSmallAntiSievePrimeRange x).powerset.filter fun u =>
    u.Nonempty ∧ u.card ≤ 50

theorem mem_taoSmallPrimeTupleSupports {x : ℕ} {u : Finset ℕ} :
    u ∈ taoSmallPrimeTupleSupports x ↔
      u ⊆ taoSmallAntiSievePrimeRange x ∧ u.Nonempty ∧ u.card ≤ 50 := by
  simp [taoSmallPrimeTupleSupports]

/-- Every actual ordered prime tuple has one of the finite candidate
supports. -/
theorem taoOrderedPrimeTupleSupport_mem
    {x : ℕ} {p : Fin 50 → ℕ} (hp : p ∈ taoSmallPrimeTuples x) :
    taoOrderedPrimeTupleSupport p ∈ taoSmallPrimeTupleSupports x := by
  rw [taoSmallPrimeTupleSupports, Finset.mem_filter,
    Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases mem_taoOrderedPrimeTupleSupport.mp hq with ⟨k, rfl⟩
    exact Fintype.mem_piFinset.mp hp k
  · exact ⟨p 0, mem_taoOrderedPrimeTupleSupport.mpr ⟨0, rfl⟩⟩
  · exact card_taoSmallPrimeTupleSupport_le_fifty
      (taoOrderedPrimeTuplePairLift p)

/-- Ordered prime tuples having exactly a prescribed distinct support. -/
def taoSmallPrimeTuplesWithSupport
    (x : ℕ) (u : Finset ℕ) : Finset (Fin 50 → ℕ) :=
  (taoSmallPrimeTuples x).filter fun p => taoOrderedPrimeTupleSupport p = u

/-- A fixed support `u` admits at most `#u^50` ordered prime tuples. -/
theorem card_taoSmallPrimeTuplesWithSupport_le
    (x : ℕ) (u : Finset ℕ) :
    (taoSmallPrimeTuplesWithSupport x u).card ≤ u.card ^ (50 : ℕ) := by
  let T := Fintype.piFinset fun _ : Fin 50 => u
  calc
    (taoSmallPrimeTuplesWithSupport x u).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn id
      · intro p hp
        change p ∈ Fintype.piFinset fun _ : Fin 50 => u
        rw [Fintype.mem_piFinset]
        intro k
        have hsupport := (Finset.mem_filter.mp hp).2
        rw [← hsupport]
        exact mem_taoOrderedPrimeTupleSupport.mpr ⟨k, rfl⟩
      · intro p _hp q _hq hpq
        exact hpq
    _ = u.card ^ (50 : ℕ) := by
      change (Fintype.piFinset fun _ : Fin 50 => u).card = u.card ^ 50
      rw [Fintype.card_piFinset]
      simp

/-- Uniform coarse cardinality bound for every support fiber. -/
theorem card_taoSmallPrimeTuplesWithSupport_le_fifty_pow
    (x : ℕ) {u : Finset ℕ} (hu : u.card ≤ 50) :
    (taoSmallPrimeTuplesWithSupport x u).card ≤ 50 ^ (50 : ℕ) := by
  exact (card_taoSmallPrimeTuplesWithSupport_le x u).trans
    (Nat.pow_le_pow_left hu 50)

/-- Support-sensitive coefficient bound retaining the actual product of
`log p / p` weights rather than replacing it pointwise by a full sum. -/
theorem taoOrderedPrimeTupleCoefficient_le_supportWeight
    {x : ℕ} {p : Fin 50 → ℕ} (hp : p ∈ taoSmallPrimeTuples x) :
    taoOrderedPrimeTupleCoefficient p ≤
      (∏ q ∈ taoOrderedPrimeTupleSupport p, Real.log q / q) *
        Real.log (taoSmallAntiSievePrimeCutoff x) ^
          (50 - (taoOrderedPrimeTupleSupport p).card) := by
  have hlift := taoOrderedPrimeTuplePairLift_mem hp
  rw [taoOrderedPrimeTupleCoefficient_eq_pairLift,
    prod_log_div_tupleModulus_eq_mertens_mul_repeated hlift]
  unfold taoSmallPrimeTupleMertensWeight
  change _ ≤
    (∏ q ∈ taoOrderedPrimeTupleSupport p, Real.log q / q) * _
  apply mul_le_mul_of_nonneg_left
  · exact taoSmallPrimeTupleRepeatedLogWeight_le hlift
  · apply Finset.prod_nonneg
    intro q hq
    have hqPrime := (taoSmallPrimeTupleSupport_prime_le hlift hq).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqPrime.one_le))
      (Nat.cast_nonneg q)

/-- Exact support regrouping of the complete shift-free coefficient sum. -/
theorem sum_taoOrderedPrimeTupleCoefficient_eq_sum_supportFibers
    (x : ℕ) :
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) =
      ∑ u ∈ taoSmallPrimeTupleSupports x,
        ∑ p ∈ taoSmallPrimeTuplesWithSupport x u,
          taoOrderedPrimeTupleCoefficient p := by
  have hMaps : ∀ p ∈ taoSmallPrimeTuples x,
      taoOrderedPrimeTupleSupport p ∈ taoSmallPrimeTupleSupports x :=
    fun p hp => taoOrderedPrimeTupleSupport_mem hp
  have h := Finset.sum_fiberwise_of_maps_to hMaps
    taoOrderedPrimeTupleCoefficient
  simpa [taoSmallPrimeTuplesWithSupport] using h.symm

/-- After regrouping by support, each fiber costs at most `50^50`; the
remaining sum is the elementary-symmetric Mertens expression. -/
theorem sum_taoOrderedPrimeTupleCoefficient_le_supportSum
    (x : ℕ) :
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
      (50 : ℝ) ^ (50 : ℕ) *
        ∑ u ∈ taoSmallPrimeTupleSupports x,
          (∏ q ∈ u, Real.log q / q) *
            Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - u.card) := by
  rw [sum_taoOrderedPrimeTupleCoefficient_eq_sum_supportFibers]
  calc
    (∑ u ∈ taoSmallPrimeTupleSupports x,
        ∑ p ∈ taoSmallPrimeTuplesWithSupport x u,
          taoOrderedPrimeTupleCoefficient p) ≤
        ∑ u ∈ taoSmallPrimeTupleSupports x,
          (50 : ℝ) ^ (50 : ℕ) *
            ((∏ q ∈ u, Real.log q / q) *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - u.card)) := by
      apply Finset.sum_le_sum
      intro u hu
      have huData := Finset.mem_filter.mp hu
      have huSubset : u ⊆ taoSmallAntiSievePrimeRange x :=
        Finset.mem_powerset.mp huData.1
      calc
        (∑ p ∈ taoSmallPrimeTuplesWithSupport x u,
            taoOrderedPrimeTupleCoefficient p) ≤
            ∑ _p ∈ taoSmallPrimeTuplesWithSupport x u,
              ((∏ q ∈ u, Real.log q / q) *
                Real.log (taoSmallAntiSievePrimeCutoff x) ^
                  (50 - u.card)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hsupport := (Finset.mem_filter.mp hp).2
          have hpTuple : p ∈ taoSmallPrimeTuples x :=
            (Finset.mem_filter.mp hp).1
          simpa [hsupport] using
            taoOrderedPrimeTupleCoefficient_le_supportWeight
              hpTuple
        _ = ((taoSmallPrimeTuplesWithSupport x u).card : ℝ) *
            ((∏ q ∈ u, Real.log q / q) *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^
                (50 - u.card)) := by simp
        _ ≤ (50 : ℝ) ^ (50 : ℕ) *
            ((∏ q ∈ u, Real.log q / q) *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^
                (50 - u.card)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_taoSmallPrimeTuplesWithSupport_le_fifty_pow
              x huData.2.2
          · apply mul_nonneg
            · apply Finset.prod_nonneg
              intro q hq
              have hqRange := huSubset hq
              have hqPrime := (mem_taoSmallAntiSievePrimeRange.mp hqRange).1
              exact div_nonneg
                (Real.log_nonneg (by exact_mod_cast hqPrime.one_le))
                (Nat.cast_nonneg q)
            · exact pow_nonneg (Real.log_nonneg (by
                have huNonempty := huData.2.1
                rcases huNonempty with ⟨q, hq⟩
                have hqData := mem_taoSmallAntiSievePrimeRange.mp (huSubset hq)
                show (1 : ℝ) ≤ taoSmallAntiSievePrimeCutoff x
                exact_mod_cast hqData.1.one_le.trans hqData.2)) _
    _ = (50 : ℝ) ^ (50 : ℕ) *
        ∑ u ∈ taoSmallPrimeTupleSupports x,
          (∏ q ∈ u, Real.log q / q) *
            Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - u.card) := by
      rw [Finset.mul_sum]

/-- The small-prime range uses the same convention as the existing weighted
prime logarithm sum. -/
theorem sum_taoSmallAntiSievePrimeRange_log_div
    (x : ℕ) :
    (∑ p ∈ taoSmallAntiSievePrimeRange x, Real.log p / p) =
      weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) := by
  unfold taoSmallAntiSievePrimeRange weightedPrimeLogSum
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨⟨hp.2.two_le, by omega⟩, hp.2⟩
    · intro hp
      exact ⟨by omega, hp.2⟩
  · intro p _hp
    rfl

/-- The complete support sum is bounded by the literal fifty-term repeated
Mertens expression.  This performs the formerly missing equality-pattern
summation: fixed supports cost at most `50^50`, and fixed-cardinality support
products are bounded by powers of the complete weighted prime sum. -/
theorem sum_taoOrderedPrimeTupleCoefficient_le_repeatedMertens
    (x : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
      (50 : ℝ) ^ (50 : ℕ) *
        ∑ j ∈ Finset.Icc 1 50,
          weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^ j *
            Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
  calc
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
        (50 : ℝ) ^ (50 : ℕ) *
          ∑ u ∈ taoSmallPrimeTupleSupports x,
            (∏ q ∈ u, Real.log q / q) *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - u.card) :=
      sum_taoOrderedPrimeTupleCoefficient_le_supportSum x
    _ ≤ (50 : ℝ) ^ (50 : ℕ) *
        ∑ j ∈ Finset.Icc 1 50,
          weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^ j *
            Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
      apply mul_le_mul_of_nonneg_left
      · have hMaps : ∀ u ∈ taoSmallPrimeTupleSupports x,
            u.card ∈ Finset.Icc 1 50 := by
          intro u hu
          have huData := mem_taoSmallPrimeTupleSupports.mp hu
          rw [Finset.mem_Icc]
          exact ⟨Finset.one_le_card.mpr huData.2.1, huData.2.2⟩
        rw [← Finset.sum_fiberwise_of_maps_to hMaps]
        apply Finset.sum_le_sum
        intro j hj
        have hjData := Finset.mem_Icc.mp hj
        have hFiber :
            (taoSmallPrimeTupleSupports x).filter (fun u => u.card = j) =
              (taoSmallAntiSievePrimeRange x).powersetCard j := by
          ext u
          rw [Finset.mem_filter, Finset.mem_powersetCard,
            mem_taoSmallPrimeTupleSupports]
          constructor
          · intro hu
            exact ⟨hu.1.1, hu.2⟩
          · intro hu
            refine ⟨⟨hu.1, ?_, ?_⟩, hu.2⟩
            · exact Finset.nonempty_iff_ne_empty.mpr (by
                intro hempty
                rw [hempty, Finset.card_empty] at hu
                omega)
            · omega
        rw [hFiber]
        calc
          (∑ u ∈ (taoSmallAntiSievePrimeRange x).powersetCard j,
              (∏ q ∈ u, Real.log q / q) *
                Real.log (taoSmallAntiSievePrimeCutoff x) ^
                  (50 - u.card)) =
              (∑ u ∈ (taoSmallAntiSievePrimeRange x).powersetCard j,
                ∏ q ∈ u, Real.log q / q) *
                  Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u hu
            rw [(Finset.mem_powersetCard.mp hu).2]
          _ ≤ (∑ q ∈ taoSmallAntiSievePrimeRange x,
                Real.log q / q) ^ j *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
            apply mul_le_mul_of_nonneg_right
            · apply sum_powersetCard_prod_le_sum_pow
              intro q hq
              have hqPrime := (mem_taoSmallAntiSievePrimeRange.mp hq).1
              exact div_nonneg
                (Real.log_nonneg (by exact_mod_cast hqPrime.one_le))
                (Nat.cast_nonneg q)
            · exact pow_nonneg (Real.log_nonneg (by
                show (1 : ℝ) ≤ taoSmallAntiSievePrimeCutoff x
                exact_mod_cast hcutoff)) _
          _ = weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^ j *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
            rw [sum_taoSmallAntiSievePrimeRange_log_div]
      · positivity

/-- The equality-pattern sum with every weighted-prime factor replaced by
the explicit finite Mertens majorant. -/
theorem sum_taoOrderedPrimeTupleCoefficient_le_explicitMertens
    (x : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
      (50 : ℝ) ^ (50 : ℕ) *
        ∑ j ∈ Finset.Icc 1 50,
          (Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x))) ^ j *
          Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
  calc
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
        (50 : ℝ) ^ (50 : ℕ) *
          ∑ j ∈ Finset.Icc 1 50,
            weightedPrimeLogSum (taoSmallAntiSievePrimeCutoff x) ^ j *
              Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) :=
      sum_taoOrderedPrimeTupleCoefficient_le_repeatedMertens x hcutoff
    _ ≤ (50 : ℝ) ^ (50 : ℕ) *
        ∑ j ∈ Finset.Icc 1 50,
          (Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x))) ^ j *
          Real.log (taoSmallAntiSievePrimeCutoff x) ^ (50 - j) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro j _hj
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (weightedPrimeLogSum_nonneg _)
            (weightedPrimeLogSum_le _ hcutoff) j
        · exact pow_nonneg (Real.log_nonneg (by
            show (1 : ℝ) ≤ taoSmallAntiSievePrimeCutoff x
            exact_mod_cast hcutoff)) _
      · positivity

/-- A single `log^50`-shaped bound for the complete shift-free coefficient
sum.  All constants are explicit and independent of `x`. -/
theorem sum_taoOrderedPrimeTupleCoefficient_le_log_pow_fifty
    (x : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
      (50 : ℝ) ^ (50 : ℕ) * 50 *
        (Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ) := by
  let A : ℝ := Real.log 4 *
    (2 + Real.log (taoSmallAntiSievePrimeCutoff x))
  let L : ℝ := Real.log (taoSmallAntiSievePrimeCutoff x)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by
      show (1 : ℝ) ≤ taoSmallAntiSievePrimeCutoff x
      exact_mod_cast hcutoff)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  calc
    (∑ p ∈ taoSmallPrimeTuples x, taoOrderedPrimeTupleCoefficient p) ≤
        (50 : ℝ) ^ (50 : ℕ) *
          ∑ j ∈ Finset.Icc 1 50, A ^ j * L ^ (50 - j) := by
      simpa [A, L] using
        sum_taoOrderedPrimeTupleCoefficient_le_explicitMertens x hcutoff
    _ ≤ (50 : ℝ) ^ (50 : ℕ) *
        (50 * (A + L) ^ (50 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left
      · have hterm : ∀ j ∈ Finset.Icc 1 50,
            A ^ j * L ^ (50 - j) ≤ (A + L) ^ (50 : ℕ) := by
          intro j hj
          have hjLe : j ≤ 50 := (Finset.mem_Icc.mp hj).2
          calc
            A ^ j * L ^ (50 - j) ≤
                (A + L) ^ j * (A + L) ^ (50 - j) := by
              exact mul_le_mul
                (pow_le_pow_left₀ hA (le_add_of_nonneg_right hL) j)
                (pow_le_pow_left₀ hL (le_add_of_nonneg_left hA) (50 - j))
                (pow_nonneg hL _) (pow_nonneg (add_nonneg hA hL) _)
            _ = (A + L) ^ (50 : ℕ) := by
              rw [← pow_add]
              congr
              omega
        have hsum := Finset.sum_le_card_nsmul
          (Finset.Icc 1 50) (fun j : ℕ => A ^ j * L ^ (50 - j))
          ((A + L) ^ (50 : ℕ)) hterm
        simpa only [Nat.card_Icc, Nat.reduceSub, nsmul_eq_mul,
          Nat.cast_ofNat] using hsum
      · positivity
    _ = (50 : ℝ) ^ (50 : ℕ) * 50 *
        (Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ) := by
      simp [A, L, mul_assoc]

/-- Complete elementary Mertens bound for the logarithmic lcm coefficient
over the original ordered pair-tuples, including the exact `H^50` shift
cost. -/
theorem sum_taoSmallAntiSieveTupleCoefficient_le_log_pow_fifty
    (x H : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ k, Real.log (t k).2) / taoSmallPrimeTupleModulus t) ≤
      (H : ℝ) ^ (50 : ℕ) *
        ((50 : ℝ) ^ (50 : ℕ) * 50 *
          (Real.log 4 *
              (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
            Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ)) := by
  exact (sum_taoSmallAntiSieveTupleCoefficient_le_shiftFree x H).trans
    (mul_le_mul_of_nonneg_left
      (sum_taoOrderedPrimeTupleCoefficient_le_log_pow_fifty x hcutoff)
      (pow_nonneg (Nat.cast_nonneg H) _))

/-- Principal-character portion of the conductor-reduced tuple bound. -/
def taoSmallPrimePrincipalConductorSum (x H : ℕ) : ℝ :=
  ∑ t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
    (∏ k, Real.log (t k).2) *
      ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t)

/-- Exceptional squared-moment portion of the conductor-reduced tuple bound. -/
def taoSmallPrimeExceptionalConductorSum
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) : ℝ :=
  ∑ t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
    (∏ k, Real.log (t k).2) *
      (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
          ∑ ψ ∈ taoExceptionalPrimitiveCharacters d (P j),
            ‖taoNormalizedPrimeCharacterSum ψ (P j)‖ ^ (2 : ℕ))

/-- Elementary unexceptional `φ(d)P⁻⁸` portion of the conductor-reduced
tuple bound. -/
def taoSmallPrimeTotientErrorConductorSum
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) : ℝ :=
  ∑ t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
    (∏ k, Real.log (t k).2) *
      (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
          (d.totient : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)))

/-- Exact decomposition of the inserted conductor bound into principal,
exceptional, and elementary totient-error contributions. -/
theorem taoSmallPrimeConductorBoundAtCoordinate_eq_three_parts
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) :
    taoSmallPrimeConductorBoundAtCoordinate P x H j =
      taoSmallPrimePrincipalConductorSum x H +
        taoSmallPrimeExceptionalConductorSum P x H j +
          taoSmallPrimeTotientErrorConductorSum P x H j := by
  unfold taoSmallPrimeConductorBoundAtCoordinate
  unfold taoSmallPrimePrincipalConductorSum
  unfold taoSmallPrimeExceptionalConductorSum
  unfold taoSmallPrimeTotientErrorConductorSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Finset.sum_add_distrib]
  ring

/-- The principal-character portion satisfies the complete explicit weighted
Mertens bound. -/
theorem taoSmallPrimePrincipalConductorSum_le
    (x H : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    taoSmallPrimePrincipalConductorSum x H ≤
      (2 : ℝ) ^ (50 : ℕ) *
        ((H : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) := by
  unfold taoSmallPrimePrincipalConductorSum
  calc
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ k, Real.log (t k).2) *
          ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t)) =
        (2 : ℝ) ^ (50 : ℕ) *
          ∑ t ∈ Fintype.piFinset
            (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
            (∏ k, Real.log (t k).2) /
              taoSmallPrimeTupleModulus t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ ≤ (2 : ℝ) ^ (50 : ℕ) *
        ((H : ℝ) ^ (50 : ℕ) *
          ((50 : ℝ) ^ (50 : ℕ) * 50 *
            (Real.log 4 *
                (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
              Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_taoSmallAntiSieveTupleCoefficient_le_log_pow_fifty
          x H hcutoff) (by positivity)

/-- Removing the divisor one from the classical totient-divisor identity
can only decrease its nonnegative sum. -/
theorem sum_totient_divisors_erase_one_le (q : ℕ) :
    ∑ d ∈ q.divisors.erase 1, d.totient ≤ q := by
  calc
    (∑ d ∈ q.divisors.erase 1, d.totient) ≤
        ∑ d ∈ q.divisors, d.totient := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset 1 q.divisors) (fun _ _ _ => Nat.zero_le _)
    _ = q := Nat.sum_totient q

/-- The divisor-summed unexceptional factor cancels its ambient lcm
denominator, leaving the uniform `2^50 P⁻⁸` error. -/
theorem tupleTotientErrorFactor_le
    (q P : ℕ) (hq : 0 < q) :
    ((2 ^ (50 : ℕ) : ℝ) / q) *
        (∑ d ∈ q.divisors.erase 1,
          (d.totient : ℝ) * (P : ℝ) ^ (-(8 : ℝ))) ≤
      (2 : ℝ) ^ (50 : ℕ) * (P : ℝ) ^ (-(8 : ℝ)) := by
  rw [← Finset.sum_mul]
  have hsum :
      (∑ d ∈ q.divisors.erase 1, (d.totient : ℝ)) ≤ (q : ℝ) := by
    exact_mod_cast sum_totient_divisors_erase_one_le q
  have hratio :
      (∑ d ∈ q.divisors.erase 1, (d.totient : ℝ)) / (q : ℝ) ≤ 1 := by
    exact (div_le_one (by exact_mod_cast hq)).mpr hsum
  calc
    ((2 ^ (50 : ℕ) : ℝ) / q) *
        ((∑ d ∈ q.divisors.erase 1, (d.totient : ℝ)) *
          (P : ℝ) ^ (-(8 : ℝ))) =
        (2 : ℝ) ^ (50 : ℕ) *
          ((∑ d ∈ q.divisors.erase 1, (d.totient : ℝ)) / q) *
            (P : ℝ) ^ (-(8 : ℝ)) := by ring
    _ ≤ (2 : ℝ) ^ (50 : ℕ) * 1 *
        (P : ℝ) ^ (-(8 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg P) _)
    _ = (2 : ℝ) ^ (50 : ℕ) *
        (P : ℝ) ^ (-(8 : ℝ)) := by ring

/-- The sum of logarithms over the literal small-prime range is exactly the
Chebyshev theta function at the cutoff. -/
theorem sum_taoSmallAntiSievePrimeRange_log_eq_theta (x : ℕ) :
    (∑ p ∈ taoSmallAntiSievePrimeRange x, Real.log p) =
      Chebyshev.theta (taoSmallAntiSievePrimeCutoff x) := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  unfold taoSmallAntiSievePrimeRange
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨⟨Nat.zero_le _, by omega⟩, hp.2⟩
    · intro hp
      exact ⟨by omega, hp.2⟩
  · intro p _hp
    rfl

/-- Restoring all shift coordinates in the unweighted logarithmic tuple sum
costs `H^50`; the remaining independent prime sum is bounded by Chebyshev's
explicit estimate. -/
theorem sum_taoSmallAntiSieveTupleLogProduct_le
    (x H : ℕ) (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        ∏ k, Real.log (t k).2) ≤
      (H : ℝ) ^ (50 : ℕ) *
        (Real.log 4 * taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ) := by
  have hprimeWeightNonneg : ∀ p ∈ taoSmallPrimeTuples x,
      0 ≤ ∏ k, Real.log (p k) := by
    intro p hp
    apply Finset.prod_nonneg
    intro k _hk
    have hpk := mem_taoSmallAntiSievePrimeRange.mp
      (Fintype.mem_piFinset.mp hp k)
    exact Real.log_nonneg (by exact_mod_cast hpk.1.one_le)
  calc
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        ∏ k, Real.log (t k).2) ≤
        (H : ℝ) ^ (50 : ℕ) *
          ∑ p ∈ taoSmallPrimeTuples x,
            ∏ k, Real.log (p k) :=
      sum_taoSmallAntiSieveTuples_le_H_pow_mul_sum_primeTuples
        x H (fun p => ∏ k, Real.log (p k)) hprimeWeightNonneg
    _ = (H : ℝ) ^ (50 : ℕ) *
        Chebyshev.theta (taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ) := by
      congr 1
      unfold taoSmallPrimeTuples
      calc
        (∑ p ∈ Fintype.piFinset
            (fun _ : Fin 50 => taoSmallAntiSievePrimeRange x),
            ∏ k, Real.log (p k)) =
            ∏ _k : Fin 50,
              ∑ q ∈ taoSmallAntiSievePrimeRange x, Real.log q := by
          exact Finset.sum_prod_piFinset
            (R := ℝ) (s := taoSmallAntiSievePrimeRange x)
            (g := fun (_k : Fin 50) (q : ℕ) => Real.log q)
        _ = Chebyshev.theta (taoSmallAntiSievePrimeCutoff x) ^
            (50 : ℕ) := by
          rw [sum_taoSmallAntiSievePrimeRange_log_eq_theta]
          simp
    _ ≤ (H : ℝ) ^ (50 : ℕ) *
        (Real.log 4 * taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ) := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (Chebyshev.theta_nonneg _)
          (Chebyshev.theta_le_log4_mul_x (by exact_mod_cast hcutoff.le)) _
      · positivity

/-- Complete explicit bound for the elementary unexceptional conductor
error. -/
theorem taoSmallPrimeTotientErrorConductorSum_le
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001)
    (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    taoSmallPrimeTotientErrorConductorSum P x H j ≤
      ((2 : ℝ) ^ (50 : ℕ) * (P j : ℝ) ^ (-(8 : ℝ))) *
        ((H : ℝ) ^ (50 : ℕ) *
          (Real.log 4 * taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ)) := by
  unfold taoSmallPrimeTotientErrorConductorSum
  calc
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ k, Real.log (t k).2) *
          (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
            ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
              (d.totient : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)))) ≤
        ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
          (∏ k, Real.log (t k).2) *
            ((2 : ℝ) ^ (50 : ℕ) *
              (P j : ℝ) ^ (-(8 : ℝ))) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left
      · exact tupleTotientErrorFactor_le
          (taoSmallPrimeTupleModulus t) (P j)
          (taoSmallPrimeTupleModulus_pos_of_mem ht)
      · apply Finset.prod_nonneg
        intro k _hk
        have hkPrime := (mem_taoSmallAntiSieveIndices.mp
          (Fintype.mem_piFinset.mp ht k)).2.2.1
        exact Real.log_nonneg (by exact_mod_cast hkPrime.one_le)
    _ = ((2 : ℝ) ^ (50 : ℕ) *
          (P j : ℝ) ^ (-(8 : ℝ))) *
        ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
          ∏ k, Real.log (t k).2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ ≤ ((2 : ℝ) ^ (50 : ℕ) *
          (P j : ℝ) ^ (-(8 : ℝ))) *
        ((H : ℝ) ^ (50 : ℕ) *
          (Real.log 4 * taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_taoSmallAntiSieveTupleLogProduct_le x H hcutoff)
        (mul_nonneg (by positivity)
          (Real.rpow_nonneg (Nat.cast_nonneg (P j)) _))

/-- Explicit elementary majorant for the principal contribution. -/
def taoSmallPrimePrincipalMertensMajorant (x H : ℕ) : ℝ :=
  (2 : ℝ) ^ (50 : ℕ) *
    ((H : ℝ) ^ (50 : ℕ) *
      ((50 : ℝ) ^ (50 : ℕ) * 50 *
        (Real.log 4 *
            (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
          Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ)))

/-- Explicit elementary majorant for the summed unexceptional error. -/
def taoSmallPrimeTotientErrorMajorant
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) : ℝ :=
  ((2 : ℝ) ^ (50 : ℕ) * (P j : ℝ) ^ (-(8 : ℝ))) *
    ((H : ℝ) ^ (50 : ℕ) *
      (Real.log 4 * taoSmallAntiSievePrimeCutoff x) ^ (50 : ℕ))

/-- The conductor-reduced tuple bound now has only one non-elementary term:
the explicit exceptional squared-moment sum consumed by Lemma 5.1. -/
theorem taoSmallPrimeConductorBoundAtCoordinate_le_exceptional_add_elementary
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001)
    (hcutoff : 0 < taoSmallAntiSievePrimeCutoff x) :
    taoSmallPrimeConductorBoundAtCoordinate P x H j ≤
      taoSmallPrimePrincipalMertensMajorant x H +
        taoSmallPrimeExceptionalConductorSum P x H j +
          taoSmallPrimeTotientErrorMajorant P x H j := by
  rw [taoSmallPrimeConductorBoundAtCoordinate_eq_three_parts]
  exact add_le_add
    (add_le_add
      (taoSmallPrimePrincipalConductorSum_le x H hcutoff)
      (le_refl _))
    (taoSmallPrimeTotientErrorConductorSum_le P x H j hcutoff)

/-- Source-facing small-prime moment reduction after all elementary Mertens
and unexceptional estimates: only the exceptional squared-moment tuple sum
remains. -/
theorem exists_taoSmallPrimeFiftiethMoment_le_exceptional_add_elementary
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ)
    (hcutoffSep : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallAntiSievePrimeCutoff x < P j)
    (hcutoffPos : 0 < taoSmallAntiSievePrimeCutoff x) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          taoSmallPrimeExceptionalConductorSum P x H j +
            taoSmallPrimeTotientErrorMajorant P x H j) := by
  rcases exists_taoSmallPrimeFiftiethMoment_le_conductorBound
      P hP x H m' hcutoffSep with ⟨j, hj, hmoment⟩
  refine ⟨j, hj, hmoment.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (taoSmallPrimeConductorBoundAtCoordinate_le_exceptional_add_elementary
      P x H j hcutoffPos) (by norm_num)

/-- Exact fiber description of the small anti-sieve indices over a fixed
prime. -/
theorem mem_taoSmallAntiSieveIndices_iff_prime_shift
    {x H l p : ℕ} :
    (l, p) ∈ taoSmallAntiSieveIndices x H ↔
      p ∈ taoSmallAntiSievePrimeRange x ∧
        l ∈ taoSmallAntiSieveShifts H p := by
  rw [mem_taoSmallAntiSieveIndices, mem_taoSmallAntiSievePrimeRange,
    mem_taoSmallAntiSieveShifts]
  tauto

end

end Tao2026
