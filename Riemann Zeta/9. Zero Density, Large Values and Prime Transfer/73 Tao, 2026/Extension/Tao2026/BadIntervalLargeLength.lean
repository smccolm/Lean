import Tao2026.BadIntervalLargePrimeSum
import Tao2026.PrimeIntervals

/-!
# The preliminary large-length bad-interval branch

This module implements the first disposal in Tao's proof of Proposition 6.5.
If a normalized bad interval has `H ≥ x^(7/50)`, then a fixed positive
proportion of that interval supplies real starting points for a prime-free
interval of length `(2x)^(41/300)`.  The exponent `41/300` lies strictly
between the Guth--Maynard threshold `2/15` and Tao's cutoff `7/50`.

A finite greedy interval selection controls all overlaps at once, including
between different dyadic values of `H`; consequently no logarithmic loss is
needed.  Proposition 2.3(iii) then gives a genuine fixed power saving for the
actual union of normalized intervals in this branch.
-/

namespace Tao2026

open Filter Set MeasureTheory Asymptotics

noncomputable section

/-- A fixed exponent strictly between `2/15` and Tao's large-length cutoff
`7/50`. -/
def badIntervalLargeLengthPrimeExponent : ℝ := 41 / 300

/-- The physical prime-free length used at outer endpoint scale `2x`. -/
def badIntervalLargeLengthPrimeGap (x : ℕ) : ℝ :=
  (2 * (x : ℝ)) ^ badIntervalLargeLengthPrimeExponent

/-- Actual comparable-scale normalized intervals in Tao's preliminary
`H ≥ x^0.14` branch. -/
noncomputable def taoLargeLengthFailureIndices (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    (x : ℝ) ^ (7 / 50 : ℝ) ≤ (NH.2 : ℝ)

/-- The actual union disposed of in the preliminary large-length branch. -/
noncomputable def taoLargeLengthFailureUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (taoLargeLengthFailureIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_taoLargeLengthFailureIndices {x N H : ℕ} :
    (N, H) ∈ taoLargeLengthFailureIndices x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        (x : ℝ) ^ (7 / 50 : ℝ) ≤ (H : ℝ) := by
  classical
  simp [taoLargeLengthFailureIndices]

/-- Encode `(N,N+H]` as the closed natural interval `[N+1,N+H]`. -/
def badIntervalClosedEndpoints (NH : ℕ × ℕ) : ℕ × ℕ :=
  (NH.1 + 1, NH.1 + NH.2)

/-- The finite interval family underlying the large-length failure union. -/
noncomputable def taoLargeLengthClosedFamily (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (taoLargeLengthFailureIndices x).image badIntervalClosedEndpoints

theorem closedNatInterval_badIntervalClosedEndpoints (N H : ℕ) :
    closedNatInterval (badIntervalClosedEndpoints (N, H)) =
      consecutiveInterval N H := by
  ext n
  simp [closedNatInterval, badIntervalClosedEndpoints, consecutiveInterval]

theorem taoLargeLengthFailureUnion_eq_closedFamily (x : ℕ) :
    taoLargeLengthFailureUnion x =
      (taoLargeLengthClosedFamily x).biUnion closedNatInterval := by
  classical
  ext n
  simp only [taoLargeLengthFailureUnion, taoLargeLengthClosedFamily,
    Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨NH, hNH, hn⟩
    refine ⟨badIntervalClosedEndpoints NH, ⟨NH, hNH, rfl⟩, ?_⟩
    rw [closedNatInterval_badIntervalClosedEndpoints]
    exact hn
  · rintro ⟨ab, ⟨NH, hNH, rfl⟩, hn⟩
    refine ⟨NH, hNH, ?_⟩
    rw [← closedNatInterval_badIntervalClosedEndpoints]
    exact hn

theorem taoLargeLengthClosedFamily_valid {x : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ taoLargeLengthClosedFamily x) :
    ab.1 ≤ ab.2 := by
  classical
  rw [taoLargeLengthClosedFamily, Finset.mem_image] at hab
  obtain ⟨⟨N, H⟩, hNH, rfl⟩ := hab
  have hscale := (mem_taoLargeLengthFailureIndices.mp hNH).1
  obtain ⟨_hN, _hH, p, k, m, hnorm, _hleft, _hright⟩ :=
    mem_scaleNormalizedBadIntervalIndices.mp hscale
  have hH : 2 ≤ H := hnorm.1
  simp only [badIntervalClosedEndpoints]
  omega

/-- The real block of prime-free starts contributed by one selected bad
interval.  The left endpoint is open so that the possibly prime integer `N`
is excluded. -/
def badIntervalLargeLengthEndpointSegment (x : ℕ) (ab : ℕ × ℕ) : Set ℝ :=
  Ioc ((ab.1 - 1 : ℕ) : ℝ)
    ((ab.2 : ℝ) - badIntervalLargeLengthPrimeGap x)

/-- Disjoint closed natural intervals give disjoint real endpoint segments. -/
theorem badIntervalLargeLengthEndpointSegments_pairwiseDisjoint
    {x : ℕ} {g : Finset (ℕ × ℕ)}
    (hvalid : ∀ ab ∈ g, ab.1 ≤ ab.2)
    (hg : ∀ ab ∈ g, ∀ cd ∈ g, ab ≠ cd →
      Disjoint (closedNatInterval ab) (closedNatInterval cd)) :
    Set.PairwiseDisjoint (↑g)
      (badIntervalLargeLengthEndpointSegment x) := by
  intro ab hab cd hcd habne
  have hdisj := hg ab hab cd hcd habne
  change Disjoint (badIntervalLargeLengthEndpointSegment x ab)
    (badIntervalLargeLengthEndpointSegment x cd)
  rw [Set.disjoint_left]
  intro y hyab hycd
  change (((ab.1 - 1 : ℕ) : ℝ) < y ∧
      y ≤ (ab.2 : ℝ) - badIntervalLargeLengthPrimeGap x) at hyab
  change (((cd.1 - 1 : ℕ) : ℝ) < y ∧
      y ≤ (cd.2 : ℝ) - badIntervalLargeLengthPrimeGap x) at hycd
  have hfirstNe : ab.1 ≠ cd.1 := by
    intro hfirst
    have habMem : ab.1 ∈ closedNatInterval ab := by
      simp only [closedNatInterval, Finset.mem_Icc]
      exact ⟨le_rfl, hvalid ab hab⟩
    have hcdMem : ab.1 ∈ closedNatInterval cd := by
      simp only [closedNatInterval, Finset.mem_Icc, hfirst]
      exact ⟨le_rfl, hvalid cd hcd⟩
    exact Finset.disjoint_left.mp hdisj habMem hcdMem
  rcases lt_or_gt_of_ne hfirstNe with hfirst | hfirst
  · have habSecond : ab.2 < cd.1 := by
      by_contra hnot
      have hcdFirstMem : cd.1 ∈ closedNatInterval cd := by
        simp only [closedNatInterval, Finset.mem_Icc]
        exact ⟨le_rfl, hvalid cd hcd⟩
      have hcdFirstMemAb : cd.1 ∈ closedNatInterval ab := by
        simp only [closedNatInterval, Finset.mem_Icc]
        exact ⟨hfirst.le, Nat.le_of_not_gt hnot⟩
      exact Finset.disjoint_left.mp hdisj hcdFirstMemAb hcdFirstMem
    have hsep : (ab.2 : ℝ) ≤ ((cd.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ab.2 ≤ cd.1 - 1)
    have habUpper : y ≤ (ab.2 : ℝ) :=
      hyab.2.trans (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
    linarith
  · have hcdSecond : cd.2 < ab.1 := by
      by_contra hnot
      have habFirstMem : ab.1 ∈ closedNatInterval ab := by
        simp only [closedNatInterval, Finset.mem_Icc]
        exact ⟨le_rfl, hvalid ab hab⟩
      have habFirstMemCd : ab.1 ∈ closedNatInterval cd := by
        simp only [closedNatInterval, Finset.mem_Icc]
        exact ⟨hfirst.le, Nat.le_of_not_gt hnot⟩
      exact Finset.disjoint_left.mp hdisj habFirstMem habFirstMemCd
    have hsep : (cd.2 : ℝ) ≤ ((ab.1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : cd.2 ≤ ab.1 - 1)
    have hcdUpper : y ≤ (cd.2 : ℝ) :=
      hycd.2.trans (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
    linarith

/-- Every selected endpoint segment lies in the literal prime-free endpoint
set at scale `2x`. -/
theorem badIntervalLargeLengthEndpointSegment_subset_primeFree
    {x : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ taoLargeLengthClosedFamily x) :
    badIntervalLargeLengthEndpointSegment x ab ⊆
      primeFreeEndpointSet (2 * (x : ℝ))
        badIntervalLargeLengthPrimeExponent := by
  classical
  rw [taoLargeLengthClosedFamily, Finset.mem_image] at hab
  obtain ⟨⟨N, H⟩, hNH, rfl⟩ := hab
  have hscale := (mem_taoLargeLengthFailureIndices.mp hNH).1
  obtain ⟨_hN, _hH, p₀, k, m, hnorm, _hleft, hright⟩ :=
    mem_scaleNormalizedBadIntervalIndices.mp hscale
  intro y hy
  rw [mem_primeFreeEndpointSet]
  simp only [badIntervalLargeLengthEndpointSegment,
    badIntervalClosedEndpoints] at hy
  have hgapNonneg : 0 ≤ badIntervalLargeLengthPrimeGap x := by
    exact Real.rpow_nonneg (by positivity) _
  refine ⟨(by
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    exact hNnonneg.trans hy.1.le), ?_, ?_⟩
  · have hyUpper : y ≤ (N + H : ℕ) := by
      exact hy.2.trans (sub_le_self _ hgapNonneg)
    exact hyUpper.trans (by exact_mod_cast hright)
  · intro p hp hpy
    have hpN : N < p := by
      exact_mod_cast (hy.1.trans_le hpy.1)
    have hpUpperReal : (p : ℝ) ≤ (N : ℝ) + (H : ℝ) := by
      have hgapEq : badIntervalLargeLengthPrimeGap x =
          (2 * (x : ℝ)) ^ badIntervalLargeLengthPrimeExponent := rfl
      rw [← hgapEq] at hpy
      norm_num at hy
      linarith [hpy.2, hy.2]
    have hpUpper : p ≤ N + H := by exact_mod_cast hpUpperReal
    exact hnorm.not_prime_of_mem
      (by simp [consecutiveInterval, hpN, hpUpper]) hp

/-- At the spare exponent `41/300 < 7/50`, the fixed prime-gap length is at
most half every length in the large branch. -/
theorem eventually_two_mul_badIntervalLargeLengthPrimeGap_le :
    ∀ᶠ x : ℕ in atTop,
      2 * badIntervalLargeLengthPrimeGap x ≤
        (x : ℝ) ^ (7 / 50 : ℝ) := by
  let a : ℝ := 41 / 300
  let b : ℝ := 7 / 50
  let K : ℝ := 2 * (2 : ℝ) ^ a
  have hK : 0 < K := by dsimp [K]; positivity
  have hab : a < b := by dsimp [a, b]; norm_num
  have hsmall := (GafniTao.rpow_isLittleO_rpow hab).bound (inv_pos.mpr hK)
  have hnatTop : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hnatTop.eventually hsmall,
    eventually_ge_atTop (1 : ℕ)] with x hx hxOne
  have hxPos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxa : 0 ≤ (x : ℝ) ^ a := Real.rpow_nonneg hxPos.le _
  have hxb : 0 ≤ (x : ℝ) ^ b := Real.rpow_nonneg hxPos.le _
  have hxBound : (x : ℝ) ^ a ≤ K⁻¹ * (x : ℝ) ^ b := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hxa, abs_of_nonneg hxb] using hx
  have hmul : K * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
    calc
      K * (x : ℝ) ^ a ≤ K * (K⁻¹ * (x : ℝ) ^ b) :=
        mul_le_mul_of_nonneg_left hxBound hK.le
      _ = (x : ℝ) ^ b := by field_simp [ne_of_gt hK]
  have hgap : badIntervalLargeLengthPrimeGap x =
      (2 : ℝ) ^ a * (x : ℝ) ^ a := by
    dsimp [badIntervalLargeLengthPrimeGap,
      badIntervalLargeLengthPrimeExponent, a]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxPos.le]
  dsimp [K, b] at hmul
  rw [hgap]
  simpa only [mul_assoc] using hmul

/-- Each interval in the large family contributes enough endpoint measure to
pay for half of its natural length. -/
theorem closedNatIntervalLength_le_two_mul_endpointSegment_measure
    {x : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ taoLargeLengthClosedFamily x)
    (hgap : 2 * badIntervalLargeLengthPrimeGap x ≤
      (x : ℝ) ^ (7 / 50 : ℝ)) :
    (closedNatIntervalLength ab : ℝ) ≤
      2 * (volume (badIntervalLargeLengthEndpointSegment x ab)).toReal := by
  classical
  rw [taoLargeLengthClosedFamily, Finset.mem_image] at hab
  obtain ⟨⟨N, H⟩, hNH, rfl⟩ := hab
  have hlarge := (mem_taoLargeLengthFailureIndices.mp hNH).2
  have hhalf : 2 * badIntervalLargeLengthPrimeGap x ≤ (H : ℝ) :=
    hgap.trans hlarge
  have hwidth : 0 ≤ (H : ℝ) - badIntervalLargeLengthPrimeGap x := by
    linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * x by positivity)
      badIntervalLargeLengthPrimeExponent]
  have harg : 0 ≤
      ((N + H : ℕ) : ℝ) - badIntervalLargeLengthPrimeGap x -
        ((N + 1 - 1 : ℕ) : ℝ) := by
    norm_num
    linarith
  rw [show closedNatIntervalLength (badIntervalClosedEndpoints (N, H)) = H by
    simp [closedNatIntervalLength, badIntervalClosedEndpoints]]
  change (H : ℝ) ≤ 2 *
    (volume (Ioc (((N + 1 - 1 : ℕ) : ℝ))
      (((N + H : ℕ) : ℝ) - badIntervalLargeLengthPrimeGap x))).toReal
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal harg]
  norm_num
  linarith

/-- Finite incidence/double-count estimate for the entire actual large-H
union. -/
theorem card_taoLargeLengthFailureUnion_cast_le_primeFreeMeasure
    {x : ℕ}
    (hgap : 2 * badIntervalLargeLengthPrimeGap x ≤
      (x : ℝ) ^ (7 / 50 : ℝ)) :
    ((taoLargeLengthFailureUnion x).card : ℝ) ≤
      6 * primeFreeEndpointMeasure (2 * (x : ℝ))
        badIntervalLargeLengthPrimeExponent := by
  classical
  obtain ⟨g, hgSub, hgPairwise, hgCover⟩ :=
    exists_disjoint_closedIntervals_cover_by_triples
      (taoLargeLengthClosedFamily x)
      (fun ab hab => taoLargeLengthClosedFamily_valid hab)
  let U : Set ℝ := ⋃ ab ∈ g,
    badIntervalLargeLengthEndpointSegment x ab
  have hpair : Set.PairwiseDisjoint (↑g)
      (badIntervalLargeLengthEndpointSegment x) :=
    badIntervalLargeLengthEndpointSegments_pairwiseDisjoint
      (fun ab hab => taoLargeLengthClosedFamily_valid (hgSub hab)) hgPairwise
  have hmeasureU : (volume U).toReal =
      ∑ ab ∈ g,
        (volume (badIntervalLargeLengthEndpointSegment x ab)).toReal := by
    change volume.real (⋃ ab ∈ g,
      badIntervalLargeLengthEndpointSegment x ab) = _
    rw [measureReal_biUnion_finset hpair
      (fun ab hab => measurableSet_Ioc)
      (h := fun ab hab => measure_Ioc_lt_top.ne)]
    rfl
  have hUSub : U ⊆ primeFreeEndpointSet (2 * (x : ℝ))
      badIntervalLargeLengthPrimeExponent := by
    intro y hy
    simp only [U, mem_iUnion] at hy
    obtain ⟨ab, hab, hyab⟩ := hy
    exact badIntervalLargeLengthEndpointSegment_subset_primeFree
      (hgSub hab) hyab
  have hmeasureLe : (volume U).toReal ≤
      primeFreeEndpointMeasure (2 * (x : ℝ))
        badIntervalLargeLengthPrimeExponent := by
    exact measureReal_mono hUSub
      (measure_primeFreeEndpointSet_lt_top _ _).ne
  have hcardNat : (taoLargeLengthFailureUnion x).card ≤
      ∑ ab ∈ g, 3 * closedNatIntervalLength ab := by
    rw [taoLargeLengthFailureUnion_eq_closedFamily]
    calc
      ((taoLargeLengthClosedFamily x).biUnion closedNatInterval).card ≤
          (g.biUnion tripleClosedNatInterval).card :=
        Finset.card_le_card hgCover
      _ ≤ ∑ ab ∈ g, (tripleClosedNatInterval ab).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ ab ∈ g, 3 * closedNatIntervalLength ab := by
        apply Finset.sum_le_sum
        intro ab hab
        exact card_tripleClosedNatInterval_le
          (taoLargeLengthClosedFamily_valid (hgSub hab))
  have hcardReal : ((taoLargeLengthFailureUnion x).card : ℝ) ≤
      ∑ ab ∈ g, 3 * (closedNatIntervalLength ab : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((taoLargeLengthFailureUnion x).card : ℝ) ≤
        ∑ ab ∈ g, 3 * (closedNatIntervalLength ab : ℝ) := hcardReal
    _ ≤ ∑ ab ∈ g, 6 *
        (volume (badIntervalLargeLengthEndpointSegment x ab)).toReal := by
      apply Finset.sum_le_sum
      intro ab hab
      have hlen := closedNatIntervalLength_le_two_mul_endpointSegment_measure
        (hgSub hab) hgap
      linarith
    _ = 6 * (volume U).toReal := by
      rw [hmeasureU, Finset.mul_sum]
    _ ≤ 6 * primeFreeEndpointMeasure (2 * (x : ℝ))
          badIntervalLargeLengthPrimeExponent := by gcongr

/-- Tao's Proposition 2.3(iii), after the exact finite incidence transfer,
disposes of all normalized intervals with `H ≥ x^(7/50)` by a fixed power
saving. -/
theorem exists_eventually_card_taoLargeLengthFailureUnion_cast_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℕ in atTop,
        ((taoLargeLengthFailureUnion x).card : ℝ) ≤
          (x : ℝ) ^ (1 - c) := by
  have hthetaLower : (2 / 15 : ℝ) <
      badIntervalLargeLengthPrimeExponent := by
    norm_num [badIntervalLargeLengthPrimeExponent]
  obtain ⟨c₀, hc₀, hprop⟩ :=
    taoProposition23iii_guthMaynard hthetaLower
  let c : ℝ := c₀ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hexponent : 1 - c₀ < 1 - 2 * c := by
    dsimp [c]
    linarith
  obtain ⟨C, hC, hmeasure⟩ :=
    GafniTao.fixedPowerBound_of_epsilonExponentBound_lt hprop hexponent
  have hscaleTop : Tendsto (fun x : ℕ => 2 * (x : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hmeasureNat := hscaleTop.eventually hmeasure
  have hconstants : ∀ᶠ x : ℕ in atTop,
      6 * C * (2 : ℝ) ^ (1 - 2 * c) ≤ (x : ℝ) ^ c := by
    have hpowTop : Tendsto (fun x : ℕ => (x : ℝ) ^ c) atTop atTop :=
      (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
    exact hpowTop.eventually (eventually_ge_atTop _)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_two_mul_badIntervalLargeLengthPrimeGap_le,
    hmeasureNat, hconstants, eventually_ge_atTop (1 : ℕ)]
      with x hgap hmeasureX hconstant hxOne
  have hincidence :=
    card_taoLargeLengthFailureUnion_cast_le_primeFreeMeasure hgap
  have hmeasureNonneg : 0 ≤ primeFreeEndpointMeasure
      (2 * (x : ℝ)) badIntervalLargeLengthPrimeExponent := by
    exact ENNReal.toReal_nonneg
  have hbasePos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hboundMeasure : primeFreeEndpointMeasure
      (2 * (x : ℝ)) badIntervalLargeLengthPrimeExponent ≤
      C * (2 * (x : ℝ)) ^ (1 - 2 * c) := by
    exact (le_abs_self _).trans hmeasureX
  calc
    ((taoLargeLengthFailureUnion x).card : ℝ) ≤
        6 * primeFreeEndpointMeasure (2 * (x : ℝ))
          badIntervalLargeLengthPrimeExponent := hincidence
    _ ≤ 6 * (C * (2 * (x : ℝ)) ^ (1 - 2 * c)) := by gcongr
    _ = (6 * C * (2 : ℝ) ^ (1 - 2 * c)) *
          (x : ℝ) ^ (1 - 2 * c) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbasePos.le]
      ring
    _ ≤ (x : ℝ) ^ c * (x : ℝ) ^ (1 - 2 * c) := by
      gcongr
    _ = (x : ℝ) ^ (1 - c) := by
      rw [← Real.rpow_add hbasePos]
      congr 1
      ring

end

end Tao2026
