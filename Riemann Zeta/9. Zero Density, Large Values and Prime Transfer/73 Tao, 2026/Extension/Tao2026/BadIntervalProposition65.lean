import Tao2026.BadIntervalSmoothBranches
import Tao2026.BadIntervalLargeLength

/-!
# Fixed-cutoff assembly for Proposition 6.5

This module assembles the already quantified failure branches for one fixed
pair of prime-window exponents.  It isolates the finite interval logic from
the remaining slowly varying cutoff diagonalization.
-/

namespace Tao2026

open Filter

noncomputable section

/-- Non-typical comparable-scale normalized intervals for the concrete
cutoffs `floor(z^(9/10))` and `ceil(z^3)`. -/
noncomputable def taoFixedNonTypicalFailureIndices (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    ∃ p₀ k m : ℕ,
      IsNonTypicalScaleNormalizedBadInterval x (taoTypicalLengthCutoff x)
        (taoTypicalSquareThreshold x) (taoZPowerFloor (9 / 10 : ℝ) x)
        (taoTypicalSquareThreshold x) NH.1 NH.2 p₀ k m

/-- The actual interval union associated with the fixed non-typical family. -/
noncomputable def taoFixedNonTypicalFailureUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (taoFixedNonTypicalFailureIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_taoFixedNonTypicalFailureIndices {x N H : ℕ} :
    (N, H) ∈ taoFixedNonTypicalFailureIndices x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        ∃ p₀ k m : ℕ,
          IsNonTypicalScaleNormalizedBadInterval x (taoTypicalLengthCutoff x)
            (taoTypicalSquareThreshold x) (taoZPowerFloor (9 / 10 : ℝ) x)
            (taoTypicalSquareThreshold x) N H p₀ k m := by
  classical
  simp [taoFixedNonTypicalFailureIndices]

/-- The eight concrete failure unions used in the fixed-cutoff assembly. -/
noncomputable def taoFixedProposition65FailureCover (x : ℕ) : Finset ℕ :=
  taoLargeLengthFailureUnion x ∪
    (taoShortLargePrimeFailureUnion x ∪
      (taoLongModerateFailureUnion x ∪
        (taoLargeSquareFailureUnion x ∪
          (taoSmallPrimeFailureUnion x
              (taoOneTermExponentCutoff (2 / 5 : ℝ) x) ∪
            (taoShortSmoothPrimeFailureUnion x
                (taoBadIntervalSourceOutsideCentralPrimeRange x) ∪
              (taoDeficientPrimeFailureUnion x
                  (taoTypicalSquareThreshold x)
                  (taoZPowerFloor (9 / 10 : ℝ) x)
                  (taoTypicalSquareThreshold x)
                  (taoBadIntervalCentralPrimeRange x) ∪
                taoShortSmoothPrimeFailureUnion x
                  (taoBadIntervalSourceLargeSmoothPrimeRange x)))))))

/-- The distinguished square factor violates condition (ii) whenever its
prime reaches the square threshold. -/
theorem IsNonTypicalScaleNormalizedBadInterval.p₀_lt_squareThreshold_of_avoids
    {x lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m)
    (havoid : AvoidsSquareMultiplesAtLeast N H squareThreshold) :
    p₀ < squareThreshold := by
  obtain ⟨_hH, _hbad, _hp, _hHltp, _hpMax, hk, _hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := hnon.1
  by_contra hnot
  have hthreshold : squareThreshold ≤ p₀ := by omega
  have hpSq : p₀ ^ 2 ∣ k := by
    rw [hkm]
    exact dvd_mul_right (p₀ ^ 2) m
  exact havoid k hk p₀ hthreshold hpSq

/-- Membership in a normalized interval supplies the square-root bound on
its distinguished prime at the outer scale `2x`. -/
theorem IsNonTypicalScaleNormalizedBadInterval.p₀_le_two_mul_sqrt
    {x lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    p₀ ≤ (2 * x).sqrt := by
  obtain ⟨_hH, _hbad, _hp, _hHltp, _hpMax, hk, hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := hnon.1
  have hmPos : 0 < m := Nat.pos_of_ne_zero (isSmooth_iff.mp hmSmooth).1
  have hpSqLeK : p₀ * p₀ ≤ k := by
    rw [hkm, pow_two]
    exact Nat.le_mul_of_pos_right _ hmPos
  have hkUpper : k ≤ N + H := (Finset.mem_Ioc.mp hk).2
  have hright : N + H ≤ 2 * x := hnon.2.2.1
  exact Nat.le_sqrt.mpr (hpSqLeK.trans (hkUpper.trans hright))

/-- The concrete ceiling cutoff is itself a critical smoothness selector at
ambient scale `2x`. -/
theorem isTaoCriticalSmoothRegime_two_mul_exponentCutoff
    {β : ℝ} (hβ : 0 < β) :
    IsTaoCriticalSmoothRegime (fun x => 2 * x)
      (taoOneTermExponentCutoff β) β :=
  ⟨tendsto_log_two_mul_div_log_nat,
    tendsto_log_exponentCutoff_div_log_taoZ hβ⟩

/-- Small-prime disposal with the ceiling-rounded cutoff used by the exact
fixed partition. -/
theorem eventually_card_taoSmallPrimeFailureUnion_exponentCutoff_le
    {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ((taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff β x)).card : ℝ) ≤
        (2 * x : ℕ) / (taoZ x) ^ (1 / β - ε) := by
  have hregime := isTaoCriticalSmoothRegime_two_mul_exponentCutoff hβ
  filter_upwards [
    hregime.eventually_psiNat_cast_le_self_div_taoZ_rpow hβ hε] with x hx
  have hcard :
      ((taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff β x)).card : ℝ) ≤
        (psiNat (2 * x) (taoOneTermExponentCutoff β x) : ℝ) := by
    exact_mod_cast card_taoSmallPrimeFailureUnion_le_psiNat
      x (taoOneTermExponentCutoff β x)
  exact hcard.trans hx

/-- At exponent `2/5`, the exact ceiling-rounded small-prime branch retains
the same explicit `z^(-12/5)` saving. -/
theorem eventually_card_taoSmallPrimeFailureUnion_exponentCutoff_two_fifths_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card : ℝ) ≤
        (2 * x : ℕ) / (taoZ x) ^ (12 / 5 : ℝ) := by
  have hexponent :
      1 / (2 / 5 : ℝ) - (1 / 10 : ℝ) = 12 / 5 := by
    norm_num
  simpa only [hexponent] using
    eventually_card_taoSmallPrimeFailureUnion_exponentCutoff_le
      (β := (2 / 5 : ℝ)) (ε := (1 / 10 : ℝ))
      (by norm_num) (by norm_num)

set_option maxRecDepth 4000 in
/-- Every fixed-cutoff non-typical interval belongs to one of the eight
quantitatively controlled failure unions. -/
theorem eventually_taoFixedNonTypicalFailureUnion_subset_cover :
    ∀ᶠ x : ℕ in atTop,
      taoFixedNonTypicalFailureUnion x ⊆
        taoFixedProposition65FailureCover x := by
  classical
  filter_upwards [eventually_exponentCutoff_sq_le
      (β := (5 / 4 : ℝ)) (by norm_num), eventually_ge_atTop (2 : ℕ),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hcutSq hx hzOne
  intro n hn
  rw [taoFixedNonTypicalFailureUnion, Finset.mem_biUnion] at hn
  obtain ⟨⟨N, H⟩, hNH, hnInterval⟩ := hn
  rw [mem_taoFixedNonTypicalFailureIndices] at hNH
  obtain ⟨hscale, p₀, k, m, hnon⟩ := hNH
  have hnorm := hnon.1
  have hpPrime := hnorm.2.2.1
  have hpTwo : 2 ≤ p₀ := hpPrime.two_le
  have hlargeLengthOrShort :
      (x : ℝ) ^ (7 / 50 : ℝ) ≤ (H : ℝ) ∨
        H < badIntervalLargePrimeLengthCutoff x := by
    by_cases hlarge : (x : ℝ) ^ (7 / 50 : ℝ) ≤ (H : ℝ)
    · exact Or.inl hlarge
    · right
      have hreal : (H : ℝ) < (x : ℝ) ^ (7 / 50 : ℝ) := lt_of_not_ge hlarge
      have hceil : (x : ℝ) ^ (7 / 50 : ℝ) ≤
          (badIntervalLargePrimeLengthCutoff x : ℝ) := by
        exact Nat.le_ceil _
      exact_mod_cast hreal.trans_le hceil
  rcases hlargeLengthOrShort with hlarge | hprelimShort
  · rw [taoFixedProposition65FailureCover, Finset.mem_union]
    left
    rw [taoLargeLengthFailureUnion, Finset.mem_biUnion]
    exact ⟨(N, H), mem_taoLargeLengthFailureIndices.mpr ⟨hscale, hlarge⟩,
      hnInterval⟩
  · by_cases hpLarge : x ^ 3 < p₀ ^ 20
    · rw [taoFixedProposition65FailureCover, Finset.mem_union]
      right
      rw [Finset.mem_union]
      left
      rw [taoShortLargePrimeFailureUnion, Finset.mem_biUnion]
      exact ⟨(N, H), mem_taoShortLargePrimeFailureIndices.mpr
        ⟨hscale, hprelimShort, p₀, k, m, hnorm, hpLarge⟩, hnInterval⟩
    · have hpModerate : p₀ ^ 20 ≤ x ^ 3 := Nat.le_of_not_gt hpLarge
      by_cases hlong : taoTypicalLengthCutoff x ≤ H
      · rw [taoFixedProposition65FailureCover, Finset.mem_union]
        right
        rw [Finset.mem_union]
        right
        rw [Finset.mem_union]
        left
        rw [taoLongModerateFailureUnion, Finset.mem_biUnion]
        exact ⟨(N, H), mem_taoLongModerateFailureIndices.mpr
          ⟨hscale, hlong, p₀, k, m, hnorm, hpModerate⟩, hnInterval⟩
      · have hshort : H < taoTypicalLengthCutoff x := Nat.lt_of_not_ge hlong
        by_cases havoid : AvoidsSquareMultiplesAtLeast N H
            (taoTypicalSquareThreshold x)
        · have hpUpper : p₀ ≤ taoTypicalSquareThreshold x :=
            (hnon.p₀_lt_squareThreshold_of_avoids havoid).le
          by_cases hpSmall :
              p₀ ≤ taoOneTermExponentCutoff (2 / 5 : ℝ) x
          · rw [taoFixedProposition65FailureCover, Finset.mem_union]
            right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
            rw [Finset.mem_union]; right; rw [Finset.mem_union]; left
            rw [taoSmallPrimeFailureUnion, Finset.mem_biUnion]
            exact ⟨(N, H), mem_taoSmallPrimeFailureIndices.mpr
              ⟨hscale, p₀, k, m, hnorm, hpSmall⟩, hnInterval⟩
          · have hpAboveSmall :
                taoOneTermExponentCutoff (2 / 5 : ℝ) x < p₀ :=
              Nat.lt_of_not_ge hpSmall
            by_cases hpNine :
                p₀ ≤ taoOneTermExponentCutoff (9 / 10 : ℝ) x
            · have hpSq : p₀ * p₀ ≤ x := by
                have hpCut : p₀ ≤ taoOneTermExponentCutoff (5 / 4 : ℝ) x :=
                  hpNine.trans (taoOneTermExponentCutoff_mono_of_one_le
                    hzOne (by norm_num))
                exact (Nat.mul_le_mul hpCut hpCut).trans (by simpa [pow_two] using hcutSq)
              have hpBand : p₀ ∈ taoOneTermExponentPrimeBand
                  (2 / 5 : ℝ) (9 / 10 : ℝ) x := by
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_filter.mpr
                    ⟨Finset.mem_Icc.mpr ⟨hpTwo, Nat.le_sqrt.mpr hpSq⟩, hpPrime⟩,
                    hpAboveSmall, hpNine⟩
              rw [taoFixedProposition65FailureCover, Finset.mem_union]
              right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
              rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
              rw [Finset.mem_union]; left
              rw [taoShortSmoothPrimeFailureUnion, Finset.mem_biUnion]
              exact ⟨(N, H), mem_taoShortSmoothPrimeFailureIndices.mpr
                ⟨hscale, hshort, p₀, k, m, hnorm,
                  Finset.mem_union.mpr (Or.inl hpBand)⟩, hnInterval⟩
            · have hpAboveNine :
                  taoOneTermExponentCutoff (9 / 10 : ℝ) x < p₀ :=
                Nat.lt_of_not_ge hpNine
              by_cases hpEleven :
                  p₀ ≤ taoOneTermExponentCutoff (11 / 10 : ℝ) x
              · have hpCut : p₀ ≤ taoOneTermExponentCutoff (5 / 4 : ℝ) x :=
                  hpEleven.trans (taoOneTermExponentCutoff_mono_of_one_le
                    hzOne (by norm_num))
                have hpSq : p₀ * p₀ ≤ x :=
                  (Nat.mul_le_mul hpCut hpCut).trans (by simpa [pow_two] using hcutSq)
                have hpBand : p₀ ∈ taoBadIntervalCentralPrimeRange x :=
                  Finset.mem_filter.mpr
                    ⟨Finset.mem_filter.mpr
                      ⟨Finset.mem_Icc.mpr ⟨hpTwo, Nat.le_sqrt.mpr hpSq⟩, hpPrime⟩,
                      hpAboveNine, hpEleven⟩
                rw [taoFixedProposition65FailureCover, Finset.mem_union]
                right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; left
                rw [taoDeficientPrimeFailureUnion, Finset.mem_biUnion]
                refine ⟨(N, H), ?_, hnInterval⟩
                rw [taoDeficientPrimeFailureIndices, Finset.mem_filter]
                exact ⟨hscale, hshort, havoid, p₀, k, m, hnon, hpUpper, hpBand⟩
              · have hpAboveEleven :
                  taoOneTermExponentCutoff (11 / 10 : ℝ) x < p₀ :=
                    Nat.lt_of_not_ge hpEleven
                by_cases hpFiveFour :
                    p₀ ≤ taoOneTermExponentCutoff (5 / 4 : ℝ) x
                · have hpSq : p₀ * p₀ ≤ x :=
                    (Nat.mul_le_mul hpFiveFour hpFiveFour).trans
                      (by simpa [pow_two] using hcutSq)
                  have hpBand : p₀ ∈ taoOneTermExponentPrimeBand
                      (11 / 10 : ℝ) (5 / 4 : ℝ) x :=
                    Finset.mem_filter.mpr
                      ⟨Finset.mem_filter.mpr
                        ⟨Finset.mem_Icc.mpr ⟨hpTwo, Nat.le_sqrt.mpr hpSq⟩,
                          hpPrime⟩, hpAboveEleven, hpFiveFour⟩
                  rw [taoFixedProposition65FailureCover, Finset.mem_union]
                  right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                  rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                  rw [Finset.mem_union]; left
                  rw [taoShortSmoothPrimeFailureUnion, Finset.mem_biUnion]
                  exact ⟨(N, H), mem_taoShortSmoothPrimeFailureIndices.mpr
                    ⟨hscale, hshort, p₀, k, m, hnorm,
                      Finset.mem_union.mpr (Or.inr hpBand)⟩, hnInterval⟩
                · have hpBand : p₀ ∈ taoBadIntervalSourceLargeSmoothPrimeRange x :=
                    Finset.mem_filter.mpr
                      ⟨Finset.mem_filter.mpr
                        ⟨Finset.mem_Icc.mpr
                          ⟨hpTwo, hnon.p₀_le_two_mul_sqrt⟩, hpPrime⟩,
                        Nat.lt_of_not_ge hpFiveFour, hpUpper⟩
                  rw [taoFixedProposition65FailureCover, Finset.mem_union]
                  right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                  rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                  rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                  rw [taoShortSmoothPrimeFailureUnion, Finset.mem_biUnion]
                  exact ⟨(N, H), mem_taoShortSmoothPrimeFailureIndices.mpr
                    ⟨hscale, hshort, p₀, k, m, hnorm, hpBand⟩, hnInterval⟩
        · rw [taoFixedProposition65FailureCover, Finset.mem_union]
          right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
          rw [Finset.mem_union]; left
          rw [taoLargeSquareFailureUnion, Finset.mem_biUnion]
          exact ⟨(N, H), mem_taoLargeSquareFailureIndices.mpr
            ⟨hscale, hshort, havoid⟩, hnInterval⟩

/-- Cardinality of a right-associated union of eight finite sets is bounded
by the sum of their cardinalities. -/
theorem card_union_eight_le {α : Type*} [DecidableEq α]
    (A B C D E F G H : Finset α) :
    (A ∪ (B ∪ (C ∪ (D ∪ (E ∪ (F ∪ (G ∪ H))))))).card ≤
      A.card + B.card + C.card + D.card + E.card + F.card + G.card + H.card := by
  have hA := Finset.card_union_le A (B ∪ (C ∪ (D ∪ (E ∪ (F ∪ (G ∪ H))))))
  have hB := Finset.card_union_le B (C ∪ (D ∪ (E ∪ (F ∪ (G ∪ H)))))
  have hC := Finset.card_union_le C (D ∪ (E ∪ (F ∪ (G ∪ H))))
  have hD := Finset.card_union_le D (E ∪ (F ∪ (G ∪ H)))
  have hE := Finset.card_union_le E (F ∪ (G ∪ H))
  have hF := Finset.card_union_le F (G ∪ H)
  have hG := Finset.card_union_le G H
  omega

/-- The fixed failure cover has cardinality at most the sum of the eight
already isolated branch cardinalities. -/
theorem card_taoFixedProposition65FailureCover_le (x : ℕ) :
    (taoFixedProposition65FailureCover x).card ≤
      (taoLargeLengthFailureUnion x).card +
      (taoShortLargePrimeFailureUnion x).card +
      (taoLongModerateFailureUnion x).card +
      (taoLargeSquareFailureUnion x).card +
      (taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoBadIntervalSourceOutsideCentralPrimeRange x)).card +
      (taoDeficientPrimeFailureUnion x
        (taoTypicalSquareThreshold x)
        (taoZPowerFloor (9 / 10 : ℝ) x)
        (taoTypicalSquareThreshold x)
        (taoBadIntervalCentralPrimeRange x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoBadIntervalSourceLargeSmoothPrimeRange x)).card := by
  simpa only [taoFixedProposition65FailureCover] using card_union_eight_le
    (taoLargeLengthFailureUnion x)
    (taoShortLargePrimeFailureUnion x)
    (taoLongModerateFailureUnion x)
    (taoLargeSquareFailureUnion x)
    (taoSmallPrimeFailureUnion x
      (taoOneTermExponentCutoff (2 / 5 : ℝ) x))
    (taoShortSmoothPrimeFailureUnion x
      (taoBadIntervalSourceOutsideCentralPrimeRange x))
    (taoDeficientPrimeFailureUnion x
      (taoTypicalSquareThreshold x)
      (taoZPowerFloor (9 / 10 : ℝ) x)
      (taoTypicalSquareThreshold x)
      (taoBadIntervalCentralPrimeRange x))
    (taoShortSmoothPrimeFailureUnion x
      (taoBadIntervalSourceLargeSmoothPrimeRange x))

/-- Every fixed positive power of `z` is eventually below every fixed
positive power of the ambient natural scale. -/
theorem eventually_taoZ_rpow_le_nat_rpow
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, (taoZ x) ^ A ≤ (x : ℝ) ^ c := by
  have hratio := tendsto_log_taoZ_div_log_nat_zero
  have hthreshold : (0 : ℝ) < c / A := div_pos hc hA
  filter_upwards [hratio.eventually (Iio_mem_nhds hthreshold),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hsmall hlogX
  have hxPos : (0 : ℝ) < x := by
    exact zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg x)).mp hlogX)
  have hlogCompare : A * Real.log (taoZ x) ≤ c * Real.log (x : ℝ) := by
    have hraw : Real.log (taoZ x) < (c / A) * Real.log (x : ℝ) :=
      (div_lt_iff₀ hlogX).mp hsmall
    have hscaled := mul_lt_mul_of_pos_left hraw hA
    calc
      A * Real.log (taoZ x) ≤
          A * ((c / A) * Real.log (x : ℝ)) := hscaled.le
      _ = c * Real.log (x : ℝ) := by field_simp
  rw [Real.rpow_def_of_pos (taoZ_pos x), Real.rpow_def_of_pos hxPos]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hlogCompare)

/-- A fixed power saving in `x` dominates any prescribed fixed power of
`z` in the denominator. -/
theorem eventually_nat_rpow_one_sub_le_self_div_taoZ_rpow
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (1 - c) ≤ (x : ℝ) / (taoZ x) ^ A := by
  filter_upwards [eventually_taoZ_rpow_le_nat_rpow hA hc,
    eventually_ge_atTop (1 : ℕ)] with x hpower hx
  have hxPos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hzPowPos : 0 < (taoZ x) ^ A := Real.rpow_pos_of_pos (taoZ_pos x) _
  rw [le_div_iff₀ hzPowPos]
  calc
    (x : ℝ) ^ (1 - c) * (taoZ x) ^ A ≤
        (x : ℝ) ^ (1 - c) * (x : ℝ) ^ c := by
      exact mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hxPos.le _)
    _ = (x : ℝ) := by
      rw [← Real.rpow_add hxPos]
      norm_num

/-- A stronger fixed `z` exponent and fixed leading constant imply a weaker
fixed exponent once `z` is large. -/
theorem eventually_const_mul_self_div_taoZ_rpow_le
    {C a b : ℝ} (hC : 0 < C) (hgap : b < a) :
    ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) / (taoZ x) ^ a ≤
        (x : ℝ) / (taoZ x) ^ b := by
  have hgapPos : 0 < a - b := sub_pos.mpr hgap
  have hpowTop : Tendsto (fun z : ℝ => z ^ (a - b)) atTop atTop :=
    tendsto_rpow_atTop hgapPos
  filter_upwards [(hpowTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop C)] with x hCpow
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hgapPowPos : 0 < (taoZ x) ^ (a - b) :=
    Real.rpow_pos_of_pos hzPos _
  have hcoeff : C / (taoZ x) ^ (a - b) ≤ 1 :=
    (div_le_one hgapPowPos).2 hCpow
  have htargetNonneg : 0 ≤ (x : ℝ) / (taoZ x) ^ b := by positivity
  have halgebra (X G B : ℝ) (hG : G ≠ 0) (hB : B ≠ 0) :
      C * X / (G * B) = (C / G) * (X / B) := by
    field_simp [hG, hB]
  have hpow : (taoZ x) ^ a =
      (taoZ x) ^ (a - b) * (taoZ x) ^ b := by
    rw [← Real.rpow_add hzPos]
    congr 1
    ring
  calc
    C * (x : ℝ) / (taoZ x) ^ a =
        (C / (taoZ x) ^ (a - b)) *
          ((x : ℝ) / (taoZ x) ^ b) := by
      rw [hpow]
      exact halgebra (x : ℝ) ((taoZ x) ^ (a - b)) ((taoZ x) ^ b)
        hgapPowPos.ne' (Real.rpow_pos_of_pos hzPos b).ne'
    _ ≤ 1 * ((x : ℝ) / (taoZ x) ^ b) :=
      mul_le_mul_of_nonneg_right hcoeff htargetNonneg
    _ = (x : ℝ) / (taoZ x) ^ b := one_mul _

/-- Quantitative fixed-cutoff Proposition 6.5: the complete non-typical
interval union has a uniform exponent margin beyond `z^2`. -/
theorem eventually_card_taoFixedNonTypicalFailureUnion_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoFixedNonTypicalFailureUnion x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^ (2 + 1 / 4000 : ℝ) := by
  obtain ⟨c, hc, hlargeLength⟩ :=
    exists_eventually_card_taoLargeLengthFailureUnion_cast_le
  let commonExponent : ℝ := 2 + 1 / 2000
  let finalExponent : ℝ := 2 + 1 / 4000
  let T : ℕ → ℝ := fun x => (x : ℝ) / (taoZ x) ^ commonExponent
  have hlargeLengthConvert :=
    eventually_nat_rpow_one_sub_le_self_div_taoZ_rpow
      (A := commonExponent) (c := c) (by norm_num [commonExponent]) hc
  have hlargePrimeConvert :=
    eventually_nat_rpow_one_sub_le_self_div_taoZ_rpow
      (A := commonExponent) (c := (1 / 200 : ℝ))
      (by norm_num [commonExponent]) (by norm_num)
  have hlongConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := (3 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have hsquareConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (24 : ℝ)) (a := (5 / 2 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have hsmallConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (2 : ℝ)) (a := (12 / 5 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have houtsideConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := (2 + 1 / 1000 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have hcentralConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := (2 + 1 / 200 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have hhighConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := (2 + 1 / 800 : ℝ)) (b := commonExponent)
    (by norm_num) (by norm_num [commonExponent])
  have hfinalConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (8 : ℝ)) (a := commonExponent) (b := finalExponent)
    (by norm_num) (by norm_num [commonExponent, finalExponent])
  filter_upwards [eventually_taoFixedNonTypicalFailureUnion_subset_cover,
    hlargeLength, hlargeLengthConvert,
    eventually_card_taoShortLargePrimeFailureUnion_cast_le,
    hlargePrimeConvert,
    eventually_card_taoLongModerateFailureUnion_cast_le, hlongConvert,
    eventually_card_taoLargeSquareFailureUnion_cast_le, hsquareConvert,
    eventually_card_taoSmallPrimeFailureUnion_exponentCutoff_two_fifths_le,
    hsmallConvert,
    eventually_card_taoSourceOutsideCentralPrimeFailureUnion_le,
    houtsideConvert,
    eventually_card_taoCentralDeficientPrimeFailureUnion_le, hcentralConvert,
    eventually_card_taoSourceLargeSmoothPrimeFailureUnion_le, hhighConvert,
    hfinalConvert] with x hsubset hlarge hlargeC hlargePrime hlargePrimeC
      hlong hlongC hsquare hsquareC hsmall hsmallC houtside houtsideC
      hcentral hcentralC hhigh hhighC hfinal
  have hcardNat : (taoFixedNonTypicalFailureUnion x).card ≤
      (taoFixedProposition65FailureCover x).card :=
    Finset.card_le_card hsubset
  have hcover := card_taoFixedProposition65FailureCover_le x
  have hcard : ((taoFixedNonTypicalFailureUnion x).card : ℝ) ≤
      ((taoLargeLengthFailureUnion x).card : ℝ) +
      (taoShortLargePrimeFailureUnion x).card +
      (taoLongModerateFailureUnion x).card +
      (taoLargeSquareFailureUnion x).card +
      (taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoBadIntervalSourceOutsideCentralPrimeRange x)).card +
      (taoDeficientPrimeFailureUnion x
        (taoTypicalSquareThreshold x)
        (taoZPowerFloor (9 / 10 : ℝ) x)
        (taoTypicalSquareThreshold x)
        (taoBadIntervalCentralPrimeRange x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoBadIntervalSourceLargeSmoothPrimeRange x)).card := by
    exact_mod_cast hcardNat.trans hcover
  have hlargeT : ((taoLargeLengthFailureUnion x).card : ℝ) ≤ T x :=
    hlarge.trans hlargeC
  have hlargePrimeT : ((taoShortLargePrimeFailureUnion x).card : ℝ) ≤ T x := by
    have hpow : (x : ℝ) ^ (199 / 200 : ℝ) =
        (x : ℝ) ^ (1 - 1 / 200 : ℝ) := by norm_num
    rw [hpow] at hlargePrime
    exact hlargePrime.trans hlargePrimeC
  have hlongT : ((taoLongModerateFailureUnion x).card : ℝ) ≤ T x := by
    exact hlong.trans (by simpa [T] using hlongC)
  have hsquareT : ((taoLargeSquareFailureUnion x).card : ℝ) ≤ T x := by
    exact hsquare.trans (by simpa [T] using hsquareC)
  have hsmallT : ((taoSmallPrimeFailureUnion x
      (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card : ℝ) ≤ T x := by
    exact hsmall.trans (by simpa [T] using hsmallC)
  have houtsideT : ((taoShortSmoothPrimeFailureUnion x
      (taoBadIntervalSourceOutsideCentralPrimeRange x)).card : ℝ) ≤ T x := by
    exact houtside.trans (by simpa [T] using houtsideC)
  have hcentralT : ((taoDeficientPrimeFailureUnion x
      (taoTypicalSquareThreshold x) (taoZPowerFloor (9 / 10 : ℝ) x)
      (taoTypicalSquareThreshold x)
      (taoBadIntervalCentralPrimeRange x)).card : ℝ) ≤ T x := by
    exact hcentral.trans (by simpa [T] using hcentralC)
  have hhighT : ((taoShortSmoothPrimeFailureUnion x
      (taoBadIntervalSourceLargeSmoothPrimeRange x)).card : ℝ) ≤ T x := by
    exact hhigh.trans (by simpa [T] using hhighC)
  calc
    ((taoFixedNonTypicalFailureUnion x).card : ℝ) ≤
        ((taoLargeLengthFailureUnion x).card : ℝ) +
        (taoShortLargePrimeFailureUnion x).card +
        (taoLongModerateFailureUnion x).card +
        (taoLargeSquareFailureUnion x).card +
        (taoSmallPrimeFailureUnion x
          (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
        (taoShortSmoothPrimeFailureUnion x
          (taoBadIntervalSourceOutsideCentralPrimeRange x)).card +
        (taoDeficientPrimeFailureUnion x
          (taoTypicalSquareThreshold x)
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoTypicalSquareThreshold x)
          (taoBadIntervalCentralPrimeRange x)).card +
        (taoShortSmoothPrimeFailureUnion x
          (taoBadIntervalSourceLargeSmoothPrimeRange x)).card := hcard
    _ ≤ 8 * T x := by linarith
    _ ≤ (x : ℝ) / (taoZ x) ^ finalExponent := by
      calc
        8 * T x = 8 * (x : ℝ) / (taoZ x) ^ commonExponent := by
          dsimp only [T]
          ring
        _ ≤ (x : ℝ) / (taoZ x) ^ finalExponent := hfinal
    _ = (x : ℝ) / (taoZ x) ^ (2 + 1 / 4000 : ℝ) := rfl

end

end Tao2026
