import Tao2026.SmoothNumberCEPIntervals

/-!
# Canfield--Erdős--Pomerance source weights

This file records the exact geometric band weights at the start of the proof
of CEP Theorem 3.1.  With zero-based source index `j`, equation (3.7) is the
identity that the weights below sum to one.
-/

open scoped BigOperators

namespace Tao2026

noncomputable section

open Finset

/-- The normalized geometric weight with ratio `exp a`.  The source takes
`a = 1 / log(u)^2` and `j = 0, ..., k-1`. -/
def cepExponentialBandWeight (a : ℝ) (k j : ℕ) : ℝ :=
  ((Real.exp a - 1) / (Real.exp ((k : ℝ) * a) - 1)) *
    Real.exp ((j : ℝ) * a)

/-- Exact normalized geometric-sum identity, CEP (3.7). -/
theorem sum_cepExponentialBandWeight_eq_one
    {a : ℝ} {k : ℕ} (ha : 0 < a) (hk : 0 < k) :
    ∑ j ∈ Finset.range k, cepExponentialBandWeight a k j = 1 := by
  have hq : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkExp : 1 < Real.exp ((k : ℝ) * a) :=
    Real.one_lt_exp_iff.mpr (mul_pos hkR ha)
  have hpow : Real.exp ((k : ℝ) * a) = Real.exp a ^ k := by
    simpa using (Real.exp_nat_mul a k)
  simp_rw [cepExponentialBandWeight, Real.exp_nat_mul]
  rw [← Finset.mul_sum, geom_sum_eq hq.ne']
  rw [← hpow]
  field_simp [sub_ne_zero.mpr hq.ne', sub_ne_zero.mpr hkExp.ne']

theorem cepExponentialBandWeight_pos
    {a : ℝ} {k j : ℕ} (ha : 0 < a) (hk : 0 < k) :
    0 < cepExponentialBandWeight a k j := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnum : 0 < Real.exp a - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ha)
  have hden : 0 < Real.exp ((k : ℝ) * a) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hkR ha))
  exact mul_pos (div_pos hnum hden) (Real.exp_pos _)

/-- Polynomial form of the reverse weighted geometric-sum identity. -/
theorem reverseWeightedGeomSum_mul_sq (q : ℝ) : ∀ k : ℕ,
    (∑ j ∈ Finset.range k, ((k - j : ℕ) : ℝ) * q ^ j) * (q - 1) ^ 2 =
      q ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * q + (k : ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hsum :
          (∑ j ∈ Finset.range (k + 1),
              (((k + 1) - j : ℕ) : ℝ) * q ^ j) =
            (∑ j ∈ Finset.range k, ((k - j : ℕ) : ℝ) * q ^ j) +
              ∑ j ∈ Finset.range (k + 1), q ^ j := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
        rw [← add_assoc]
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hsub : k + 1 - j = (k - j) + 1 := by omega
        rw [hsub, Nat.cast_add, Nat.cast_one]
        ring
      rw [hsum, add_mul, ih]
      have hgeom := geom_sum_mul q (k + 1)
      calc
        q ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * q + (k : ℝ) +
            (∑ j ∈ Finset.range (k + 1), q ^ j) * (q - 1) ^ 2 =
            q ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * q + (k : ℝ) +
              (q ^ (k + 1) - 1) * (q - 1) := by
          rw [sq, ← mul_assoc, hgeom]
        _ = q ^ (k + 1 + 1) - (((k + 1) + 1 : ℕ) : ℝ) * q +
              ((k + 1 : ℕ) : ℝ) := by
          rw [pow_succ]
          push_cast
          ring

theorem reverseWeightedGeomSum_eq
    {q : ℝ} (hq : q ≠ 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, ((k - j : ℕ) : ℝ) * q ^ j =
      (q ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * q + (k : ℝ)) / (q - 1) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hq))).2
  exact reverseWeightedGeomSum_mul_sq q k

/-- Exact first reverse-index moment of the normalized source weights.  This
is the closed expression expanded asymptotically in CEP equation (3.8). -/
theorem sum_cepExponentialBandWeight_mul_reverseIndex
    {a : ℝ} {k : ℕ} (ha : 0 < a) (hk : 0 < k) :
    ∑ j ∈ Finset.range k,
        cepExponentialBandWeight a k j * ((k - j : ℕ) : ℝ) =
      Real.exp a / (Real.exp a - 1) -
        (k : ℝ) / (Real.exp ((k : ℝ) * a) - 1) := by
  let q : ℝ := Real.exp a
  have hq : 1 < q := by simpa [q] using Real.one_lt_exp_iff.mpr ha
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkExp : 1 < Real.exp ((k : ℝ) * a) :=
    Real.one_lt_exp_iff.mpr (mul_pos hkR ha)
  have hkPow : Real.exp ((k : ℝ) * a) = q ^ k := by
    simpa [q] using (Real.exp_nat_mul a k)
  simp_rw [cepExponentialBandWeight, Real.exp_nat_mul]
  change ∑ j ∈ Finset.range k,
      ((q - 1) / (q ^ k - 1) * q ^ j) * ((k - j : ℕ) : ℝ) =
        q / (q - 1) - (k : ℝ) / (q ^ k - 1)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hsumComm :
      (∑ j ∈ Finset.range k, q ^ j * ((k - j : ℕ) : ℝ)) =
        ∑ j ∈ Finset.range k, ((k - j : ℕ) : ℝ) * q ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsumComm, reverseWeightedGeomSum_eq hq.ne' k]
  change (q - 1) / (q ^ k - 1) *
      ((q ^ (k + 1) - ((k + 1 : ℕ) : ℝ) * q + (k : ℝ)) /
        (q - 1) ^ 2) = q / (q - 1) - (k : ℝ) / (q ^ k - 1)
  have hqSub : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  have hkSub : q ^ k - 1 ≠ 0 := by
    rw [← hkPow]
    exact sub_ne_zero.mpr hkExp.ne'
  field_simp [hqSub, hkSub]
  push_cast
  ring

/-- The source step size `1 / log(u)^2`. -/
def cepSourceWeightStep (u : ℝ) : ℝ := 1 / Real.log u ^ 2

/-- The source choice `k = floor(log(u)^2 log log(u))`. -/
def cepSourceBandCount (u : ℝ) : ℕ :=
  ⌊Real.log u ^ 2 * Real.log (Real.log u)⌋₊

/-- The source's weight `α_j`, with zero-based index `j`. -/
def cepSourceBandWeight (u : ℝ) (j : ℕ) : ℝ :=
  cepExponentialBandWeight (cepSourceWeightStep u) (cepSourceBandCount u) j

/-- The number `⌊α_j u⌋` of prime factors chosen from source band `j`. -/
def cepSourceBandMultiplicity (u : ℝ) (j : ℕ) : ℕ :=
  ⌊cepSourceBandWeight u j * u⌋₊

/-- The weighted reverse-band moment appearing in (3.6)--(3.8). -/
def cepSourceReverseWeightMoment (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    cepSourceBandWeight u j * ((cepSourceBandCount u - j : ℕ) : ℝ)

/-- The same moment after replacing `α_j u` by its integer floor. -/
def cepSourceReverseMultiplicityMoment (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    (cepSourceBandMultiplicity u j : ℝ) *
      ((cepSourceBandCount u - j : ℕ) : ℝ)

/-- Total reverse-index mass controlling the aggregate flooring error. -/
def cepSourceReverseIndexMass (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    ((cepSourceBandCount u - j : ℕ) : ℝ)

theorem cepSourceWeightStep_pos {u : ℝ} (hu : 1 < u) :
    0 < cepSourceWeightStep u := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  simp only [cepSourceWeightStep, one_div]
  positivity

theorem cepSourceBandWeight_pos
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) (j : ℕ) :
    0 < cepSourceBandWeight u j :=
  cepExponentialBandWeight_pos (cepSourceWeightStep_pos hu) hk

/-- Source-specific form of CEP (3.7). -/
theorem sum_cepSourceBandWeight_eq_one
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    ∑ j ∈ Finset.range (cepSourceBandCount u), cepSourceBandWeight u j = 1 := by
  exact sum_cepExponentialBandWeight_eq_one (cepSourceWeightStep_pos hu) hk

/-- Flooring the source multiplicities loses at most one unit per band. -/
theorem sum_cepSourceBandMultiplicity_bounds
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    u - (cepSourceBandCount u : ℝ) ≤
        ∑ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourceBandMultiplicity u j : ℝ) ∧
      (∑ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourceBandMultiplicity u j : ℝ)) ≤ u := by
  let k := cepSourceBandCount u
  have hsum : ∑ j ∈ Finset.range k, cepSourceBandWeight u j = 1 :=
    sum_cepSourceBandWeight_eq_one hu hk
  constructor
  · calc
      u - (k : ℝ) =
          ∑ j ∈ Finset.range k, (cepSourceBandWeight u j * u - 1) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
        simp
      _ ≤ ∑ j ∈ Finset.range k, (cepSourceBandMultiplicity u j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hfloor := Nat.lt_floor_add_one (cepSourceBandWeight u j * u)
        push_cast at hfloor
        change cepSourceBandWeight u j * u - 1 ≤
          (⌊cepSourceBandWeight u j * u⌋₊ : ℝ)
        linarith
  · calc
      (∑ j ∈ Finset.range k, (cepSourceBandMultiplicity u j : ℝ)) ≤
          ∑ j ∈ Finset.range k, cepSourceBandWeight u j * u := by
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.floor_le (mul_nonneg
          (cepSourceBandWeight_pos hu hk j).le (by linarith))
      _ = u := by
        rw [← Finset.sum_mul, hsum]
        ring

/-- Exact aggregate form of the flooring error in equation (3.6). -/
theorem cepSourceReverseMultiplicityMoment_bounds
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    u * cepSourceReverseWeightMoment u - cepSourceReverseIndexMass u ≤
        cepSourceReverseMultiplicityMoment u ∧
      cepSourceReverseMultiplicityMoment u ≤
        u * cepSourceReverseWeightMoment u := by
  let k := cepSourceBandCount u
  constructor
  · calc
      u * cepSourceReverseWeightMoment u - cepSourceReverseIndexMass u =
          ∑ j ∈ Finset.range k,
            (cepSourceBandWeight u j * u - 1) * ((k - j : ℕ) : ℝ) := by
        simp only [cepSourceReverseWeightMoment, cepSourceReverseIndexMass,
          k, sub_mul, one_mul, Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ cepSourceReverseMultiplicityMoment u := by
        simp only [cepSourceReverseMultiplicityMoment, k]
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right
        · have hfloor := Nat.lt_floor_add_one (cepSourceBandWeight u j * u)
          push_cast at hfloor
          change cepSourceBandWeight u j * u - 1 ≤
            (⌊cepSourceBandWeight u j * u⌋₊ : ℝ)
          linarith
        · positivity
  · calc
      cepSourceReverseMultiplicityMoment u ≤
          ∑ j ∈ Finset.range k,
            (cepSourceBandWeight u j * u) * ((k - j : ℕ) : ℝ) := by
        simp only [cepSourceReverseMultiplicityMoment, k]
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right
        · exact Nat.floor_le (mul_nonneg
            (cepSourceBandWeight_pos hu hk j).le (by linarith))
        · positivity
      _ = u * cepSourceReverseWeightMoment u := by
        simp only [cepSourceReverseWeightMoment, k]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring

/-- Source-specific exact form underlying CEP (3.8). -/
theorem sum_cepSourceBandWeight_mul_reverseIndex
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    ∑ j ∈ Finset.range (cepSourceBandCount u),
        cepSourceBandWeight u j *
          ((cepSourceBandCount u - j : ℕ) : ℝ) =
      Real.exp (cepSourceWeightStep u) /
          (Real.exp (cepSourceWeightStep u) - 1) -
        (cepSourceBandCount u : ℝ) /
          (Real.exp ((cepSourceBandCount u : ℝ) * cepSourceWeightStep u) - 1) := by
  exact sum_cepExponentialBandWeight_mul_reverseIndex
    (cepSourceWeightStep_pos hu) hk

/-- Coarse but uniform moment bound: a normalized weight supported on reverse
indices at most `k` has first moment at most `k`. -/
theorem cepSourceReverseWeightMoment_le_bandCount
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    cepSourceReverseWeightMoment u ≤ (cepSourceBandCount u : ℝ) := by
  calc
    cepSourceReverseWeightMoment u =
        ∑ j ∈ Finset.range (cepSourceBandCount u),
          cepSourceBandWeight u j *
            ((cepSourceBandCount u - j : ℕ) : ℝ) := rfl
    _ ≤ ∑ j ∈ Finset.range (cepSourceBandCount u),
          cepSourceBandWeight u j * (cepSourceBandCount u : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast Nat.sub_le _ _
      · exact (cepSourceBandWeight_pos hu hk j).le
    _ = (cepSourceBandCount u : ℝ) := by
      rw [← Finset.sum_mul, sum_cepSourceBandWeight_eq_one hu hk, one_mul]

end

end Tao2026
