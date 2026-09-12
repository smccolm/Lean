import Tao2026.SmoothNumberCEPSource

/-!
# Size of the CEP source multipliers

This file gives the exact finite lower-size ledger behind equation (3.6):
each selected multiplier is bounded below by the product of its source-band
lower endpoints, and that product is a single power of `x` with an explicit
exponent.
-/

open scoped BigOperators

namespace Tao2026

noncomputable section

open Finset

/-- The exponent obtained by taking every selected prime at its band's lower
endpoint. -/
def cepSourceMultiplierLowerExponent (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    (cepSourceBandMultiplicity u j : ℝ) *
      cepSourceBandLowerExponent u (cepSourceBandCount u - 1 - j)

/-- The companion exponent obtained by taking every selected prime at its
band's upper endpoint. -/
def cepSourceMultiplierUpperExponent (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    (cepSourceBandMultiplicity u j : ℝ) *
      cepSourceBandUpperExponent u (cepSourceBandCount u - 1 - j)

/-- Total selected prime multiplicity in the source packet. -/
def cepSourceMultiplicityTotal (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    (cepSourceBandMultiplicity u j : ℝ)

/-- Reverse moment appropriate to the upper endpoints, whose reversed index
is one less than the lower-endpoint index. -/
def cepSourceUpperReverseMultiplicityMoment (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (cepSourceBandCount u),
    (cepSourceBandMultiplicity u j : ℝ) *
      ((cepSourceBandCount u - 1 - j : ℕ) : ℝ)

theorem prod_rpow_nat_eq_rpow_sum_mul
    {ι : Type*} [DecidableEq ι] {x : ℝ} (hx : 0 < x)
    (s : Finset ι) (a : ι → ℝ) (r : ι → ℕ) :
    ∏ i ∈ s, (x ^ a i) ^ r i =
      x ^ ∑ i ∈ s, (r i : ℝ) * a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le,
        ← Real.rpow_add hx]
      congr 1
      ring

/-- Exact algebraic expansion of the lower exponent in (3.6). -/
theorem cepSourceMultiplierLowerExponent_eq
    (u : ℝ) :
    cepSourceMultiplierLowerExponent u =
      (∑ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourceBandMultiplicity u j : ℝ)) / u -
        cepSourceReverseMultiplicityMoment u /
          (u * Real.log u ^ 3) := by
  let k := cepSourceBandCount u
  calc
    cepSourceMultiplierLowerExponent u =
        ∑ j ∈ Finset.range k,
          ((cepSourceBandMultiplicity u j : ℝ) / u -
            ((cepSourceBandMultiplicity u j : ℝ) * ((k - j : ℕ) : ℝ)) /
              (u * Real.log u ^ 3)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [cepSourceBandLowerExponent, k]
      have hjk : j < k := Finset.mem_range.mp hj
      have hindex : k - 1 - j + 1 = k - j := by omega
      rw [hindex]
      ring
    _ = (∑ j ∈ Finset.range k,
          (cepSourceBandMultiplicity u j : ℝ)) / u -
        cepSourceReverseMultiplicityMoment u /
          (u * Real.log u ^ 3) := by
      simp only [cepSourceReverseMultiplicityMoment, k]
      rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]

/-- Exact algebraic expansion of the upper multiplier exponent. -/
theorem cepSourceMultiplierUpperExponent_eq (u : ℝ) :
    cepSourceMultiplierUpperExponent u =
      cepSourceMultiplicityTotal u / u -
        cepSourceUpperReverseMultiplicityMoment u /
          (u * Real.log u ^ 3) := by
  let k := cepSourceBandCount u
  calc
    cepSourceMultiplierUpperExponent u =
        ∑ j ∈ Finset.range k,
          ((cepSourceBandMultiplicity u j : ℝ) / u -
            ((cepSourceBandMultiplicity u j : ℝ) *
                ((k - 1 - j : ℕ) : ℝ)) /
              (u * Real.log u ^ 3)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [cepSourceBandUpperExponent, k]
      ring
    _ = cepSourceMultiplicityTotal u / u -
        cepSourceUpperReverseMultiplicityMoment u /
          (u * Real.log u ^ 3) := by
      simp only [cepSourceMultiplicityTotal,
        cepSourceUpperReverseMultiplicityMoment, k]
      rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]

/-- The upper-endpoint reverse moment is the lower-endpoint reverse moment
minus the total multiplicity. -/
theorem cepSourceUpperReverseMultiplicityMoment_eq (u : ℝ) :
    cepSourceUpperReverseMultiplicityMoment u =
      cepSourceReverseMultiplicityMoment u - cepSourceMultiplicityTotal u := by
  let k := cepSourceBandCount u
  simp only [cepSourceUpperReverseMultiplicityMoment,
    cepSourceReverseMultiplicityMoment, cepSourceMultiplicityTotal]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  have hindex : k - 1 - j = k - j - 1 := by omega
  have hone : 1 ≤ k - j := by omega
  rw [hindex]
  push_cast [Nat.cast_sub hone]
  ring

/-- Exact inequality form of (3.6), retaining the weighted moment rather
than replacing it by asymptotic notation. -/
theorem one_sub_count_div_sub_moment_div_le_cepSourceMultiplierLowerExponent
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    1 - (cepSourceBandCount u : ℝ) / u -
        cepSourceReverseWeightMoment u / Real.log u ^ 3 ≤
      cepSourceMultiplierLowerExponent u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hsum := (sum_cepSourceBandMultiplicity_bounds hu hk).1
  have hmoment := (cepSourceReverseMultiplicityMoment_bounds hu hk).2
  rw [cepSourceMultiplierLowerExponent_eq]
  calc
    1 - (cepSourceBandCount u : ℝ) / u -
        cepSourceReverseWeightMoment u / Real.log u ^ 3 =
      (u - (cepSourceBandCount u : ℝ)) / u -
        (u * cepSourceReverseWeightMoment u) /
          (u * Real.log u ^ 3) := by
      field_simp [hu0.ne', hlog.ne']
    _ ≤ (∑ j ∈ Finset.range (cepSourceBandCount u),
          (cepSourceBandMultiplicity u j : ℝ)) / u -
        cepSourceReverseMultiplicityMoment u /
          (u * Real.log u ^ 3) := by
      exact sub_le_sub
        (div_le_div_of_nonneg_right hsum hu0.le)
        (div_le_div_of_nonneg_right hmoment
          (mul_nonneg hu0.le (pow_nonneg hlog.le 3)))

/-- Coarse source-size bound sufficient for an `O(u log log u)` bootstrap:
replace the exact weighted moment by the band count `k`. -/
theorem one_sub_count_div_sub_count_div_log_cube_le_cepSourceMultiplierLowerExponent
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    1 - (cepSourceBandCount u : ℝ) / u -
        (cepSourceBandCount u : ℝ) / Real.log u ^ 3 ≤
      cepSourceMultiplierLowerExponent u := by
  have hmoment := cepSourceReverseWeightMoment_le_bandCount hu hk
  have hden : 0 ≤ Real.log u ^ 3 :=
    pow_nonneg (Real.log_pos hu).le 3
  exact (sub_le_sub_left
      (div_le_div_of_nonneg_right hmoment hden)
      (1 - (cepSourceBandCount u : ℝ) / u)).trans
    (one_sub_count_div_sub_moment_div_le_cepSourceMultiplierLowerExponent
      hu hk)

/-- Closed finite (3.6)--(3.8) lower exponent, before estimating its two
elementary exponential fractions. -/
theorem cepSource_closedLowerExponent_le
    {u : ℝ} (hu : 1 < u) (hk : 0 < cepSourceBandCount u) :
    1 - (cepSourceBandCount u : ℝ) / u -
        (Real.exp (cepSourceWeightStep u) /
              (Real.exp (cepSourceWeightStep u) - 1) -
            (cepSourceBandCount u : ℝ) /
              (Real.exp ((cepSourceBandCount u : ℝ) *
                cepSourceWeightStep u) - 1)) /
          Real.log u ^ 3 ≤
      cepSourceMultiplierLowerExponent u := by
  rw [← sum_cepSourceBandWeight_mul_reverseIndex hu hk]
  exact one_sub_count_div_sub_moment_div_le_cepSourceMultiplierLowerExponent hu hk

/-- The product of source-band lower endpoint powers is the power of `x`
with the preceding explicit exponent. -/
theorem prod_cepSourceBandLower_pow_eq_rpow
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ∏ j ∈ Finset.range (cepSourceBandCount u),
        (cepSourceBandLower x u (cepSourceBandCount u - 1 - j)) ^
          cepSourceBandMultiplicity u j =
      x ^ cepSourceMultiplierLowerExponent u := by
  simpa [cepSourceBandLower, cepSourceMultiplierLowerExponent] using
    prod_rpow_nat_eq_rpow_sum_mul hx
      (Finset.range (cepSourceBandCount u))
      (fun j => cepSourceBandLowerExponent u (cepSourceBandCount u - 1 - j))
      (cepSourceBandMultiplicity u)

/-- The product of source-band upper endpoint powers is the corresponding
single power of `x`. -/
theorem prod_cepSourceBandUpper_pow_eq_rpow
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ∏ j ∈ Finset.range (cepSourceBandCount u),
        (cepSourceBandUpper x u (cepSourceBandCount u - 1 - j)) ^
          cepSourceBandMultiplicity u j =
      x ^ cepSourceMultiplierUpperExponent u := by
  simpa [cepSourceBandUpper, cepSourceMultiplierUpperExponent] using
    prod_rpow_nat_eq_rpow_sum_mul hx
      (Finset.range (cepSourceBandCount u))
      (fun j => cepSourceBandUpperExponent u (cepSourceBandCount u - 1 - j))
      (cepSourceBandMultiplicity u)

/-- Every multiplier in the exact source packet satisfies the finite lower
size estimate used in CEP equation (3.6). -/
theorem rpow_cepSourceMultiplierLowerExponent_le_cast
    {x u : ℝ} {y m : ℕ} (hx : 0 < x)
    (hm : m ∈ cepSourcePacketProducts x u y) :
    x ^ cepSourceMultiplierLowerExponent u ≤ (m : ℝ) := by
  rw [cepSourcePacketProducts, cepMultiscalePacketProducts,
    Finset.mem_image] at hm
  obtain ⟨f, hf, rfl⟩ := hm
  rw [← prod_cepSourceBandLower_pow_eq_rpow hx u]
  apply prod_pow_le_cast_cepMultiscalePacketValue
  · intro j hj
    exact Real.rpow_nonneg hx.le _
  · intro j hj (p : TaoBoundedPrime y) hp
    change p ∈ cepSourcePrimeBand x u y
      (cepSourceBandCount u - 1 - j) at hp
    exact (mem_cepSourcePrimeBand_iff.mp hp).1.le
  · exact hf

/-- Source multiplier lower bound with the closed (3.6)--(3.8) exponent. -/
theorem rpow_cepSourceClosedLowerExponent_le_cast
    {x u : ℝ} {y m : ℕ} (hx : 1 ≤ x) (hu : 1 < u)
    (hk : 0 < cepSourceBandCount u)
    (hm : m ∈ cepSourcePacketProducts x u y) :
    x ^ (1 - (cepSourceBandCount u : ℝ) / u -
        (Real.exp (cepSourceWeightStep u) /
              (Real.exp (cepSourceWeightStep u) - 1) -
            (cepSourceBandCount u : ℝ) /
              (Real.exp ((cepSourceBandCount u : ℝ) *
                cepSourceWeightStep u) - 1)) /
          Real.log u ^ 3) ≤ (m : ℝ) := by
  exact (Real.rpow_le_rpow_of_exponent_le hx
    (cepSource_closedLowerExponent_le hu hk)).trans
      (rpow_cepSourceMultiplierLowerExponent_le_cast
        (lt_of_lt_of_le zero_lt_one hx) hm)

/-- Every source multiplier satisfies the coarse lower exponent with only
the two transparent band-count losses. -/
theorem rpow_cepSourceCoarseLowerExponent_le_cast
    {x u : ℝ} {y m : ℕ} (hx : 1 ≤ x) (hu : 1 < u)
    (hk : 0 < cepSourceBandCount u)
    (hm : m ∈ cepSourcePacketProducts x u y) :
    x ^ (1 - (cepSourceBandCount u : ℝ) / u -
        (cepSourceBandCount u : ℝ) / Real.log u ^ 3) ≤ (m : ℝ) := by
  exact (Real.rpow_le_rpow_of_exponent_le hx
    (one_sub_count_div_sub_count_div_log_cube_le_cepSourceMultiplierLowerExponent
      hu hk)).trans
      (rpow_cepSourceMultiplierLowerExponent_le_cast
        (lt_of_lt_of_le zero_lt_one hx) hm)

/-- Every exact source multiplier is bounded above by the product of its
band upper endpoints. -/
theorem cast_le_rpow_cepSourceMultiplierUpperExponent
    {x u : ℝ} {y m : ℕ} (hx : 0 < x)
    (hm : m ∈ cepSourcePacketProducts x u y) :
    (m : ℝ) ≤ x ^ cepSourceMultiplierUpperExponent u := by
  rw [cepSourcePacketProducts, cepMultiscalePacketProducts,
    Finset.mem_image] at hm
  obtain ⟨f, hf, rfl⟩ := hm
  rw [← prod_cepSourceBandUpper_pow_eq_rpow hx u]
  apply cast_cepMultiscalePacketValue_le_prod_pow
  · intro j hj (p : TaoBoundedPrime y) hp
    change p ∈ cepSourcePrimeBand x u y
      (cepSourceBandCount u - 1 - j) at hp
    exact (mem_cepSourcePrimeBand_iff.mp hp).2
  · exact hf

end

end Tao2026
