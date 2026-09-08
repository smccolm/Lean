import GafniTao.ExceptionalDensity

/-!
# The all-interval branch of Gafni--Tao Theorem 1.1

The conclusion here is obtained from eventual emptiness of the literal
exceptional set.  No measure-zero-to-empty inference is used.
-/

open Filter Set

namespace GafniTao

noncomputable section

/-- Uniform ordinary density on the entire nonnegative strip.  The lower
half is elementary and will be supplied internally from the source
upper-half hypothesis. -/
def UniformNonnegativeOrdinaryDensityEnvelope (Azero : ℝ) : Prop :=
  ∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 1 →
    ZeroDensityEnvelope sigma Azero

/-- If every exact half-open strip is eventually empty, so is the exact
full-zero event in equation (2.7). -/
theorem eventually_equation27FullZeroLargeSet_eq_empty_of_strips
    {J : ℕ} (hJ : 0 < J) {theta delta : ℝ}
    (hdelta : 0 < delta)
    (hStrips : ∀ j ∈ Finset.range J,
      ∀ᶠ X : ℝ in atTop,
        equation27StripLargeSet J j theta delta X = ∅) :
    ∀ᶠ X : ℝ in atTop,
      equation27FullZeroLargeSet J theta delta X = ∅ := by
  have hAll : ∀ᶠ X : ℝ in atTop, ∀ j ∈ Finset.range J,
      equation27StripLargeSet J j theta delta X = ∅ :=
    (Finset.eventually_all (Finset.range J)).2 hStrips
  filter_upwards [hAll, eventually_gt_atTop (0 : ℝ)] with X hAllX hX
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxUnion := equation27FullZeroLargeSet_subset_biUnion_strip
    hJ hdelta hX hx
  simp only [Set.mem_iUnion] at hxUnion
  obtain ⟨j, hj⟩ := hxUnion
  obtain ⟨hjRange, hxj⟩ := hj
  rw [hAllX j hjRange] at hxj
  exact hxj

/-- Under a coefficient strictly below the all-interval threshold, every
strip is killed either by the ordinary density estimate or by the proved
Pintz--Ford right-edge argument. -/
theorem eventually_equation27FullZeroLargeSet_eq_empty_of_uniform
    {C B Tzero c Tone theta delta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hZeroFree : VinogradovKorobovCountVanishing c Tone)
    (hC : 0 < C) (hc : 0 < c)
    (hEnvelope : UniformNonnegativeOrdinaryDensityEnvelope Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hthreshold : 1 - 1 / Azero < theta) (hAzero : 0 < Azero) :
    ∃ J : ℕ, 0 < J ∧
      ∀ᶠ X : ℝ in atTop,
        equation27FullZeroLargeSet J theta delta X = ∅ := by
  have hthetaGap : 0 < 1 - theta := by linarith
  have hcoefficient : (1 - theta) * Azero < 1 := by
    have hdiv : 1 - theta < 1 / Azero := by linarith
    rwa [lt_div_iff₀ hAzero] at hdiv
  let eta : ℝ := nearOneRightEdgeWidth C 2
  have heta : 0 < eta := nearOneRightEdgeWidth_pos hC (by norm_num)
  let margin : ℝ := (1 - (1 - theta) * Azero) * eta
  have hmargin : 0 < margin := by
    dsimp only [margin]
    positivity
  obtain ⟨J, hJ, hJmargin, _hJmargin2⟩ :=
    exists_positive_nat_with_inverse_margins hmargin hmargin
  refine ⟨J, hJ, eventually_equation27FullZeroLargeSet_eq_empty_of_strips
    hJ hdelta ?_⟩
  intro j hj
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hjLt : j < J := Finset.mem_range.mp hj
  have hsigmaNonneg : 0 ≤ (j : ℝ) / J := by positivity
  have hsigmaLtOne : (j : ℝ) / J < 1 := by
    rw [div_lt_one hJr]
    exact_mod_cast hjLt
  have hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]
    exact_mod_cast Nat.succ_le_iff.mpr hjLt
  by_cases hAtRight : 1 - eta ≤ (j : ℝ) / J
  · exact eventually_equation27StripLargeSet_eq_empty_of_rightEdge
      hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper hdelta hdeltaOne
        (by simpa only [eta] using hAtRight)
  · have hInterior : (j : ℝ) / J < 1 - eta := lt_of_not_ge hAtRight
    have hDensityJ := hEnvelope ((j : ℝ) / J) hsigmaNonneg hsigmaLtOne.le
    apply eventually_equation27StripLargeSet_eq_empty_of_density
      hJ hthetaUpper hdelta hdeltaOne hAzero.le hsigmaNonneg hsigmaUpper
        hDensityJ
    have hstep : (((j + 1 : ℕ) : ℝ) / J) =
        (j : ℝ) / J + 1 / J := by
      push_cast
      field_simp [hJr.ne']
    rw [hstep]
    have hinteriorGap : eta < 1 - (j : ℝ) / J := by linarith
    have hmain : 1 / (J : ℝ) <
        (1 - (1 - theta) * Azero) * (1 - (j : ℝ) / J) := by
      have hcoefPos : 0 < 1 - (1 - theta) * Azero := by linarith
      exact hJmargin.trans
        (mul_lt_mul_of_pos_left hinteriorGap hcoefPos)
    nlinarith

/-- Eventual emptiness transfers through the exact exceptional-set entry
bridge on one multiplicative source interval. -/
theorem eventually_localShortIntervalExceptionalSet_eq_empty_of_uniform
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B Tzero c Tone theta delta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hZeroFree : VinogradovKorobovCountVanishing c Tone)
    (hC : 0 < C) (hc : 0 < c)
    (hEnvelope : UniformNonnegativeOrdinaryDensityEnvelope Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hthreshold : 1 - 1 / Azero < theta) (hAzero : 0 < Azero) :
    ∃ J : ℕ, 0 < J ∧
      ∀ᶠ X : ℝ in atTop,
        localShortIntervalExceptionalSet J theta delta X = ∅ := by
  obtain ⟨CFormula, hCFormula, hEntry⟩ :=
    eventually_localExceptionalSet_subset_equation27 hFormula
  have hthetaGap : 0 < 1 - theta := by linarith
  have hcoefficient : (1 - theta) * Azero < 1 := by
    have hdiv : 1 - theta < 1 / Azero := by linarith
    rwa [lt_div_iff₀ hAzero] at hdiv
  let eta : ℝ := nearOneRightEdgeWidth C 2
  have heta : 0 < eta := nearOneRightEdgeWidth_pos hC (by norm_num)
  let margin : ℝ := (1 - (1 - theta) * Azero) * eta
  have hmargin : 0 < margin := by
    dsimp only [margin]
    positivity
  obtain ⟨Jzero, hJzero⟩ := exists_nat_gt
    (max (6 * (8 / theta + 2)) (24 * CFormula / delta))
  obtain ⟨J, hJzeroJ, hJ, hJmargin, _hJmargin2⟩ :=
    exists_nat_ge_with_inverse_margins Jzero hmargin hmargin
  have hJzeroReal : (Jzero : ℝ) ≤ J := by exact_mod_cast hJzeroJ
  have hJLocal : 6 * (8 / theta + 2) ≤ (J : ℝ) :=
    (le_max_left _ _).trans (hJzero.le.trans hJzeroReal)
  have hJFormula : 24 * CFormula ≤ delta * (J : ℝ) := by
    have hRatio : 24 * CFormula / delta ≤ (J : ℝ) :=
      (le_max_right _ _).trans (hJzero.le.trans hJzeroReal)
    have := (div_le_iff₀ hdelta).mp hRatio
    nlinarith
  have hFull : ∀ᶠ X : ℝ in atTop,
      equation27FullZeroLargeSet J theta delta X = ∅ := by
    apply eventually_equation27FullZeroLargeSet_eq_empty_of_strips hJ hdelta
    intro j hj
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    have hjLt : j < J := Finset.mem_range.mp hj
    have hsigmaNonneg : 0 ≤ (j : ℝ) / J := by positivity
    have hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1 := by
      rw [div_le_one hJr]
      exact_mod_cast Nat.succ_le_iff.mpr hjLt
    have hsigmaLtOne : (j : ℝ) / J < 1 := by
      rw [div_lt_one hJr]
      exact_mod_cast hjLt
    by_cases hAtRight : 1 - eta ≤ (j : ℝ) / J
    · exact eventually_equation27StripLargeSet_eq_empty_of_rightEdge
        hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper hdelta hdeltaOne
          (by simpa only [eta] using hAtRight)
    · have hInterior : (j : ℝ) / J < 1 - eta := lt_of_not_ge hAtRight
      have hDensityJ := hEnvelope ((j : ℝ) / J) hsigmaNonneg hsigmaLtOne.le
      apply eventually_equation27StripLargeSet_eq_empty_of_density
        hJ hthetaUpper hdelta hdeltaOne hAzero.le hsigmaNonneg hsigmaUpper
          hDensityJ
      have hstep : (((j + 1 : ℕ) : ℝ) / J) =
          (j : ℝ) / J + 1 / J := by
        push_cast
        field_simp [hJr.ne']
      rw [hstep]
      have hinteriorGap : eta < 1 - (j : ℝ) / J := by linarith
      have hmain : 1 / (J : ℝ) <
          (1 - (1 - theta) * Azero) * (1 - (j : ℝ) / J) := by
        have hcoefPos : 0 < 1 - (1 - theta) * Azero := by linarith
        exact hJmargin.trans
          (mul_lt_mul_of_pos_left hinteriorGap hcoefPos)
      nlinarith
  have hSubset := hEntry hJ hthetaLower hthetaUpper hdelta hdeltaOne
    hJLocal hJFormula
  refine ⟨J, hJ, ?_⟩
  filter_upwards [hSubset, hFull] with X hSubsetX hFullX
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have := hSubsetX hx
  rw [hFullX] at this
  exact this

/-- Eventual emptiness on the finite multiplicative cover gives eventual
emptiness of the actual source set `E_delta(X,theta)`. -/
theorem eventually_shortIntervalExceptionalSet_eq_empty_of_uniform
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B Tzero c Tone theta delta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hZeroFree : VinogradovKorobovCountVanishing c Tone)
    (hC : 0 < C) (hc : 0 < c)
    (hEnvelope : UniformNonnegativeOrdinaryDensityEnvelope Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hthreshold : 1 - 1 / Azero < theta) (hAzero : 0 < Azero) :
    ∀ᶠ X : ℝ in atTop,
      shortIntervalExceptionalSet delta X theta = ∅ := by
  obtain ⟨J, hJ, hLocal⟩ :=
    eventually_localShortIntervalExceptionalSet_eq_empty_of_uniform hFormula
      hDensity hZeroFree hC hc hEnvelope hthetaLower hthetaUpper hdelta
        hdeltaOne hthreshold hAzero
  let u : ℝ := delta / J
  let s := Finset.range (⌈1 / u⌉₊ + 1)
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hEach : ∀ k ∈ s, ∀ᶠ X : ℝ in atTop,
      localShortIntervalExceptionalSet J theta delta
        (localCoverLeft X u k) = ∅ := by
    intro k hk
    exact (tendsto_localCoverLeft_atTop hu k).eventually hLocal
  have hAll : ∀ᶠ X : ℝ in atTop, ∀ k ∈ s,
      localShortIntervalExceptionalSet J theta delta
        (localCoverLeft X u k) = ∅ :=
    (Finset.eventually_all s).2 hEach
  filter_upwards [hAll, eventually_gt_atTop (0 : ℝ)] with X hAllX hX
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxUnion := shortIntervalExceptionalSet_subset_local_union
    hJ hX hdelta hx
  simp only [Set.mem_iUnion] at hxUnion
  obtain ⟨k, hkRange, hxLocal⟩ := hxUnion
  have hk : k ∈ s := by simpa only [s, u] using hkRange
  rw [hAllX k hk] at hxLocal
  exact hxLocal

/-- Source-facing all-interval PNT: every positive relative error threshold
is eventually avoided by every real left endpoint. -/
def AllShortIntervalsPNT (theta : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∀ᶠ x : ℝ in atTop,
      |shortIntervalDiscrepancy x theta| < delta * x ^ theta

/-- The exact all-interval conclusion from eventual emptiness of every
`E_delta(X,theta)`. -/
theorem allShortIntervalsPNT_of_eventually_exceptional_empty
    {theta : ℝ}
    (hEmpty : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ X : ℝ in atTop,
        shortIntervalExceptionalSet delta X theta = ∅) :
    AllShortIntervalsPNT theta := by
  intro delta hdelta
  have hEmptyDelta := hEmpty delta hdelta
  filter_upwards [hEmptyDelta, eventually_gt_atTop (0 : ℝ)] with x hx hX
  apply lt_of_not_ge
  intro hbad
  have hmem : x ∈ shortIntervalExceptionalSet delta x theta := by
    exact ⟨⟨le_rfl, by linarith⟩, hbad⟩
  rw [hx] at hmem
  exact hmem

/-- Exact conditional all-interval half of Gafni--Tao Theorem 1.1. -/
theorem gafniTaoTheorem11_allIntervals
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B Tzero c Tone theta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hZeroFree : VinogradovKorobovCountVanishing c Tone)
    (hC : 0 < C) (hc : 0 < c)
    (hEnvelope : UniformNonnegativeOrdinaryDensityEnvelope Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hthreshold : 1 - 1 / Azero < theta) (hAzero : 0 < Azero) :
    AllShortIntervalsPNT theta := by
  apply allShortIntervalsPNT_of_eventually_exceptional_empty
  intro delta hdelta
  let delta' : ℝ := min (delta / 2) (1 / 2)
  have hdelta' : 0 < delta' := by dsimp only [delta']; positivity
  have hdelta'One : delta' < 1 := by
    exact (min_le_right _ _).trans_lt (by norm_num)
  have hSmall := eventually_shortIntervalExceptionalSet_eq_empty_of_uniform
    hFormula hDensity hZeroFree hC hc hEnvelope hthetaLower hthetaUpper
      hdelta' hdelta'One hthreshold hAzero
  have hdelta'Le : delta' ≤ delta := by
    exact (min_le_left _ _).trans (by linarith)
  filter_upwards [hSmall, eventually_ge_atTop (0 : ℝ)] with X hSmallX hX
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxSmall := shortIntervalExceptionalSet_anti_delta hX hdelta'Le hx
  rw [hSmallX] at hxSmall
  exact hxSmall

/-- Native full-strip uniform envelope at the frozen `30/13` coefficient. -/
theorem uniformNonnegativeOrdinaryDensityEnvelope_thirty_thirteenths :
    UniformNonnegativeOrdinaryDensityEnvelope (30 / 13) := by
  intro sigma hsigma hsigmaUpper
  exact uniform_thirty_thirteenths_zeroDensityEnvelope_nonnegative
    hsigma hsigmaUpper

/-- Native Gafni--Tao/Guth--Maynard all-interval threshold. -/
theorem gafniTaoTheorem11_allIntervals_guthMaynard_native
    {theta : ℝ} (htheta : 17 / 30 < theta) (hthetaUpper : theta < 1) :
    AllShortIntervalsPNT theta := by
  obtain ⟨c, Tzero, Tdensity, hc, hZeroFree, hDensity⟩ :=
    exists_pintz_nearOne_log_density_native
  apply gafniTaoTheorem11_allIntervals sharpTruncatedExplicitFormulaBound_native
    hDensity hZeroFree pintzNearOneDensityCoefficient_pos hc
    uniformNonnegativeOrdinaryDensityEnvelope_thirty_thirteenths
    (by linarith) hthetaUpper
  · rw [← seventeen_thirtieths_eq_uniform_all_threshold]
    exact htheta
  · norm_num

end

end GafniTao
