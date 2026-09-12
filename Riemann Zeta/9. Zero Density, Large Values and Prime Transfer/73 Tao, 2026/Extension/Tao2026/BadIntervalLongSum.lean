import Tao2026.BadIntervalLongSaddle

/-!
# Summing the long bad-interval fibers

This module performs the finite dyadic-length and prime-scale aggregation
after the corrected degree-two saddle estimate.
-/

namespace Tao2026

open Filter

noncomputable section

/-- Dyadic exponents sufficient to contain every power-of-two length at most
`x`. -/
def badIntervalLongDyadicExponents (x : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 x + 1)

/-- The exact natural-power encoding of Tao's moderate prime range
`p₀ ≤ x^0.15`. -/
def badIntervalLongModeratePrimes (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun p₀ => p₀ ^ 20 ≤ x ^ 3

/-- Parameter pairs in the long, moderate-prime branch. -/
def badIntervalLongModerateFiberIndices (x : ℕ) : Finset (ℕ × ℕ) :=
  ((badIntervalLongModeratePrimes x).product
      (badIntervalLongDyadicExponents x)).filter fun pr =>
    taoTypicalLengthCutoff x ≤ 2 ^ pr.2 ∧ 2 ^ pr.2 < pr.1

/-- The actual union of all fixed fibers in this parameter range. -/
def badIntervalLongModerateFailureUnion (x : ℕ) : Finset ℕ :=
  (badIntervalLongModerateFiberIndices x).biUnion fun pr =>
    scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)

/-- The actual comparable-scale normalized intervals in the long branch whose
named largest prime lies in Tao's moderate range. -/
noncomputable def taoLongModerateFailureIndices (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    taoTypicalLengthCutoff x ≤ NH.2 ∧
      ∃ p₀ k m : ℕ,
        IsNormalizedBadInterval NH.1 NH.2 p₀ k m ∧ p₀ ^ 20 ≤ x ^ 3

/-- Union of the actual long moderate-prime normalized intervals. -/
noncomputable def taoLongModerateFailureUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (taoLongModerateFailureIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_badIntervalLongModeratePrimes {x p₀ : ℕ} :
    p₀ ∈ badIntervalLongModeratePrimes x ↔
      1 ≤ p₀ ∧ p₀ ≤ x ∧ p₀ ^ 20 ≤ x ^ 3 := by
  simp only [badIntervalLongModeratePrimes, Finset.mem_filter,
    Finset.mem_Icc, and_assoc]

theorem mem_badIntervalLongModerateFiberIndices {x p₀ r : ℕ} :
    (p₀, r) ∈ badIntervalLongModerateFiberIndices x ↔
      p₀ ∈ badIntervalLongModeratePrimes x ∧
      r ∈ badIntervalLongDyadicExponents x ∧
      taoTypicalLengthCutoff x ≤ 2 ^ r ∧ 2 ^ r < p₀ := by
  simp [badIntervalLongModerateFiberIndices, and_assoc]

theorem mem_taoLongModerateFailureIndices {x N H : ℕ} :
    (N, H) ∈ taoLongModerateFailureIndices x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        taoTypicalLengthCutoff x ≤ H ∧
        ∃ p₀ k m : ℕ,
          IsNormalizedBadInterval N H p₀ k m ∧ p₀ ^ 20 ≤ x ^ 3 := by
  classical
  simp [taoLongModerateFailureIndices]

/-- Cardinality of the union is bounded by the sum of its fixed fibers. -/
theorem card_badIntervalLongModerateFailureUnion_le_sum (x : ℕ) :
    (badIntervalLongModerateFailureUnion x).card ≤
      ∑ pr ∈ badIntervalLongModerateFiberIndices x,
        (scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card := by
  classical
  exact Finset.card_biUnion_le

/-- After the eventual fixed-fiber theorem, enlarge the restricted parameter
set to the full finite product. -/
theorem eventually_card_badIntervalLongModerateFailureUnion_cast_le_sum :
    ∀ᶠ x : ℕ in atTop,
      ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        ∑ p₀ ∈ badIntervalLongModeratePrimes x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
  filter_upwards
    [eventually_scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_four_of_long]
      with x hfiber
  classical
  have hunion : ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
      ∑ pr ∈ badIntervalLongModerateFiberIndices x,
        ((scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card : ℝ) := by
    exact_mod_cast card_badIntervalLongModerateFailureUnion_le_sum x
  calc
    ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        ∑ pr ∈ badIntervalLongModerateFiberIndices x,
          ((scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card : ℝ) :=
      hunion
    _ ≤ ∑ pr ∈ badIntervalLongModerateFiberIndices x,
          128 * (x : ℝ) / ((pr.1 : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
      apply Finset.sum_le_sum
      intro pr hpr
      have hdata := mem_badIntervalLongModerateFiberIndices.mp hpr
      exact hfiber hdata.2.2.1 hdata.2.2.2
        (mem_badIntervalLongModeratePrimes.mp hdata.1).2.2
    _ ≤ ∑ pr ∈ (badIntervalLongModeratePrimes x).product
          (badIntervalLongDyadicExponents x),
          128 * (x : ℝ) / ((pr.1 : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun pr _hpr _hnot => by positivity)
    _ = ∑ p₀ ∈ badIntervalLongModeratePrimes x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
      simpa using (Finset.sum_product'
        (badIntervalLongModeratePrimes x)
        (badIntervalLongDyadicExponents x)
        (fun p₀ _r =>
          128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ))))

theorem sum_Icc_one_div_natCast_eq_harmonic (x : ℕ) :
    (∑ p₀ ∈ Finset.Icc 1 x, 1 / (p₀ : ℝ)) =
      ((harmonic x : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Elementary comparison between the discrete base-two logarithm used to
count dyadic lengths and the real logarithm.  It is recorded locally so that
the Section 6 aggregation does not depend on the later relation-counting
modules. -/
theorem badInterval_natLogTwo_cast_le_log_div {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
    simpa only [mul_comm] using hlog)

/-- The dyadic count and reciprocal prime-scale sum cost only the displayed
two logarithmic factors. -/
theorem eventually_card_badIntervalLongModerateFailureUnion_cast_le_log_bound :
    ∀ᶠ x : ℕ in atTop,
      ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        ((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ)) *
          (1 + Real.log (x : ℝ)) := by
  filter_upwards
    [eventually_card_badIntervalLongModerateFailureUnion_cast_le_sum]
      with x hsum
  classical
  have hsubset : badIntervalLongModeratePrimes x ⊆ Finset.Icc 1 x := by
    exact Finset.filter_subset _ _
  have hfull :
      (∑ p₀ ∈ badIntervalLongModeratePrimes x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ))) ≤
        ∑ p₀ ∈ Finset.Icc 1 x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p₀ _hp _hnot => by positivity)
  have hinner (p₀ : ℕ) (hp₀ : p₀ ∈ Finset.Icc 1 x) :
      (∑ _r ∈ badIntervalLongDyadicExponents x,
          128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ))) =
        ((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ)) * (1 / (p₀ : ℝ)) := by
    have hpPos : (0 : ℝ) < (p₀ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hp₀).1
    simp only [badIntervalLongDyadicExponents, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hpPos, ne_of_gt (taoZ_pos x)]
  calc
    ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        ∑ p₀ ∈ badIntervalLongModeratePrimes x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := hsum
    _ ≤ ∑ p₀ ∈ Finset.Icc 1 x,
          ∑ _r ∈ badIntervalLongDyadicExponents x,
            128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := hfull
    _ = ∑ p₀ ∈ Finset.Icc 1 x,
          (((Nat.log 2 x + 1 : ℕ) : ℝ) *
            (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ))) *
            (1 / (p₀ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      simpa only [mul_assoc] using hinner p₀ hp₀
    _ = (((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ))) *
          (∑ p₀ ∈ Finset.Icc 1 x, 1 / (p₀ : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ))) *
          ((harmonic x : ℚ) : ℝ) := by
      rw [sum_Icc_one_div_natCast_eq_harmonic]
    _ ≤ ((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ)) *
          (1 + Real.log (x : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log x

/-- The two logarithmic losses from summing over dyadic lengths and prime
scales are eventually absorbed by one factor of Tao's saddle scale. -/
theorem eventually_badIntervalLongSummationFactor_le_taoZ :
    ∀ᶠ x : ℕ in atTop,
      (((Nat.log 2 x + 1 : ℕ) : ℝ) * 128) *
          (1 + Real.log (x : ℝ)) ≤ taoZ x := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [hlog.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_log_pow_twenty_add_one_le_two_mul_sqrt_taoZ,
      tendsto_taoZ_atTop.eventually (eventually_ge_atTop (4 : ℝ))]
      with x hlogTwo habsorb hzFour
  have hxPos : 0 < x := by
    by_contra hx
    have hxZero : x = 0 := Nat.eq_zero_of_not_pos hx
    norm_num [hxZero] at hlogTwo
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hnatLog : (Nat.log 2 x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have hbase := badInterval_natLogTwo_cast_le_log_div hxPos
    have hdiv : Real.log (x : ℝ) / Real.log 2 ≤
        2 * Real.log (x : ℝ) := by
      have hlogNonneg : 0 ≤ Real.log (x : ℝ) := by linarith
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
      nlinarith
    exact hbase.trans hdiv
  have hcount : ((Nat.log 2 x + 1 : ℕ) : ℝ) ≤
      3 * Real.log (x : ℝ) := by
    push_cast
    linarith
  have hharmonicFactor : 1 + Real.log (x : ℝ) ≤
      2 * Real.log (x : ℝ) := by linarith
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := by linarith
  have hlogPow18 : (768 : ℝ) ≤ (Real.log (x : ℝ)) ^ (18 : ℕ) := by
    calc
      (768 : ℝ) ≤ 2 ^ (18 : ℕ) := by norm_num
      _ ≤ (Real.log (x : ℝ)) ^ (18 : ℕ) := by
        exact pow_le_pow_left₀ (by norm_num) hlogTwo 18
  have hfactorLog :
      (((Nat.log 2 x + 1 : ℕ) : ℝ) * 128) *
          (1 + Real.log (x : ℝ)) ≤
        (Real.log (x : ℝ)) ^ (20 : ℕ) + 1 := by
    calc
      (((Nat.log 2 x + 1 : ℕ) : ℝ) * 128) *
          (1 + Real.log (x : ℝ)) ≤
        (3 * Real.log (x : ℝ) * 128) *
          (2 * Real.log (x : ℝ)) := by gcongr
      _ = 768 * (Real.log (x : ℝ)) ^ (2 : ℕ) := by ring
      _ ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := by
        calc
          768 * (Real.log (x : ℝ)) ^ (2 : ℕ) ≤
              (Real.log (x : ℝ)) ^ (18 : ℕ) *
                (Real.log (x : ℝ)) ^ (2 : ℕ) := by gcongr
          _ = (Real.log (x : ℝ)) ^ (20 : ℕ) := by ring
      _ ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) + 1 := by linarith
  have hsqrtSq : (Real.sqrt (taoZ x)) ^ 2 = taoZ x :=
    Real.sq_sqrt (taoZ_pos x).le
  have hsqrtNonneg : 0 ≤ Real.sqrt (taoZ x) := Real.sqrt_nonneg _
  have hsqrtAbsorb : 2 * Real.sqrt (taoZ x) ≤ taoZ x := by
    nlinarith
  exact hfactorLog.trans (habsorb.trans hsqrtAbsorb)

/-- The complete long moderate-prime union has a power saving stronger than
the weak alternative required in Proposition 6.5. -/
theorem eventually_card_badIntervalLongModerateFailureUnion_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ (3 : ℕ) := by
  filter_upwards
    [eventually_card_badIntervalLongModerateFailureUnion_cast_le_log_bound,
      eventually_badIntervalLongSummationFactor_le_taoZ]
      with x hsource habsorb
  have hzPos := taoZ_pos x
  calc
    ((badIntervalLongModerateFailureUnion x).card : ℝ) ≤
        ((Nat.log 2 x + 1 : ℕ) : ℝ) *
          (128 * (x : ℝ) / (taoZ x) ^ (4 : ℕ)) *
          (1 + Real.log (x : ℝ)) := hsource
    _ = (x : ℝ) *
        ((((Nat.log 2 x + 1 : ℕ) : ℝ) * 128) *
          (1 + Real.log (x : ℝ))) / (taoZ x) ^ (4 : ℕ) := by ring
    _ ≤ (x : ℝ) * taoZ x / (taoZ x) ^ (4 : ℕ) := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left habsorb (by positivity)
      · positivity
    _ = (x : ℝ) / (taoZ x) ^ (3 : ℕ) := by
      field_simp [ne_of_gt hzPos]

/-- Every actual normalized interval in the long moderate-prime branch occurs
in one of the explicitly summed fixed fibers. -/
theorem taoLongModerateFailureUnion_subset_badIntervalLongModerateFailureUnion
    {x : ℕ} (hx : 2 ≤ x) :
    taoLongModerateFailureUnion x ⊆
      badIntervalLongModerateFailureUnion x := by
  classical
  intro n hn
  obtain ⟨⟨N, H⟩, hNH, hnInterval⟩ := Finset.mem_biUnion.mp hn
  rw [mem_taoLongModerateFailureIndices] at hNH
  obtain ⟨hscale, hlong, p₀, k, m, hnorm, hpRange⟩ := hNH
  have hscaleData := mem_scaleNormalizedBadIntervalIndices.mp hscale
  obtain ⟨p', k', m', hnorm', hleft, hright⟩ := hscaleData.2.2
  have hstart : N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H := by
    exact mem_scaleNormalizedBadIntervalStartsAt.mpr
      ⟨hscaleData.1, k, m, hnorm, hleft, hright⟩
  have hpSq : p₀ ^ 2 ≤ 2 * x :=
    p₀_sq_le_two_mul_x_of_mem_scaleNormalizedBadIntervalStartsAt hstart
  have hpLeX : p₀ ≤ x := by
    nlinarith [sq_nonneg (p₀ - x)]
  obtain ⟨hHTwo, _hbad, hpPrime, hHltp, _hpMax, _hk, _hm,
      _hkm, _hendpoint, r, hr⟩ := hnorm
  have hrPowLe : 2 ^ r ≤ x := by omega
  have hrLog : r ≤ Nat.log 2 x :=
    Nat.le_log_of_pow_le (by norm_num) hrPowLe
  have hpMem : p₀ ∈ badIntervalLongModeratePrimes x := by
    exact mem_badIntervalLongModeratePrimes.mpr
      ⟨hpPrime.one_le, hpLeX, hpRange⟩
  have hrMem : r ∈ badIntervalLongDyadicExponents x := by
    simp [badIntervalLongDyadicExponents, hrLog]
  have hpr : (p₀, r) ∈ badIntervalLongModerateFiberIndices x := by
    exact mem_badIntervalLongModerateFiberIndices.mpr
      ⟨hpMem, hrMem, by simpa [← hr] using hlong,
        by simpa [← hr] using hHltp⟩
  refine Finset.mem_biUnion.mpr ⟨(p₀, r), hpr, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨N, ?_, ?_⟩
  · simpa [← hr] using hstart
  · simpa [← hr] using hnInterval

theorem card_taoLongModerateFailureUnion_le
    {x : ℕ} (hx : 2 ≤ x) :
    (taoLongModerateFailureUnion x).card ≤
      (badIntervalLongModerateFailureUnion x).card :=
  Finset.card_le_card
    (taoLongModerateFailureUnion_subset_badIntervalLongModerateFailureUnion hx)

/-- Final summed estimate for the actual long moderate-prime failure branch. -/
theorem eventually_card_taoLongModerateFailureUnion_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoLongModerateFailureUnion x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ (3 : ℕ) := by
  filter_upwards
    [eventually_card_badIntervalLongModerateFailureUnion_cast_le,
      eventually_ge_atTop (2 : ℕ)] with x hbound hx
  have hcard : ((taoLongModerateFailureUnion x).card : ℝ) ≤
      ((badIntervalLongModerateFailureUnion x).card : ℝ) := by
    exact_mod_cast card_taoLongModerateFailureUnion_le hx
  exact hcard.trans hbound

end

end Tao2026
