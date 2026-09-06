import GafniTao.Pintz2023PowerChoice
import GafniTao.Pintz2023DetectorArithmetic

/-!
# Pintz (2023): one perturbation with all power-selection margins

The phrase “with a sufficiently small epsilon” in Section 4 must serve the
detector, both Corollary-3 denominators, the final exponent, the `h < 20/eps`
argument, and the strict separation between the `k`- and `ell`-scales.  This
module chooses one epsilon and one positive reserve for all of them.
-/

open Topology

namespace GafniTao

noncomputable section

structure Pintz2023PowerMarginData
    (eta target : ℝ) (k ell : ℕ) where
  epsilon : ℝ
  delta : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  epsilon_lt_target : epsilon < target
  eta_le_one_twentyFour : eta ≤ 1 / 24
  cutoff_exponent : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ)
  detector_decay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0
  k_alpha : eta + 6 * epsilon < pintz2023HBAlpha k
  ell_alpha : 2 * eta + 6 * epsilon < pintz2023HBAlpha ell
  k_margin : 6 * (k : ℝ) * epsilon <
    1 - ((k : ℝ) - 1) * eta
  ell_margin : 6 * (ell : ℝ) * epsilon <
    1 - 2 * eta * ((ell : ℝ) - 1)
  power_smallness : 6 * (ell : ℝ) * epsilon < 1 / 15
  equation420_small : epsilon ≤ eta / (100 * (ell : ℝ))
  delta_pos : 0 < delta
  delta_lt_target : delta < target
  scale_separation :
    epsilon / (10 * (ell : ℝ)) +
        pintz2023CriticalScaleExponent k eta epsilon + delta <
      pintz2023EllThreshold eta epsilon ell
  exponent_budget :
    eta * pintzPerturbedCoefficient eta epsilon k ell <
      eta * pintzTheoremOneCoefficient eta k ell + target

/-- A single source perturbation satisfying every strict margin used from
equations (4.11) through (4.25). -/
theorem exists_pintz2023_power_margin_data
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hetaUpper : eta < 1 / 24)
    (htarget : 0 < target) :
    Nonempty (Pintz2023PowerMarginData eta target k ell) := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hkZeroNe : pintzKDenominator eta 0 k ≠ 0 :=
    (pintzCell_k_base_denominator_pos hcell).ne'
  have hellZeroNe : pintzEllDenominator eta 0 ell ≠ 0 :=
    (pintzCell_ell_base_denominator_pos hcell).ne'
  let f : ℝ → ℝ := fun e =>
    e / (10 * (ell : ℝ)) + 1 / pintzKDenominator eta e k -
      1 / pintzEllDenominator eta e ell
  have hlinear : ContinuousAt (fun e : ℝ => e / (10 * (ell : ℝ))) 0 := by
    fun_prop
  have hkContinuous : ContinuousAt
      (fun e : ℝ => 1 / pintzKDenominator eta e k) 0 := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun e : ℝ =>
        pintzKDenominator eta e k) 0 by
          unfold pintzKDenominator
          fun_prop)
    exact hkZeroNe
  have hellContinuous : ContinuousAt
      (fun e : ℝ => 1 / pintzEllDenominator eta e ell) 0 := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun e : ℝ =>
        pintzEllDenominator eta e ell) 0 by
          unfold pintzEllDenominator
          fun_prop)
    exact hellZeroNe
  have hfContinuous : ContinuousAt f 0 := by
    dsimp only [f]
    exact (hlinear.add hkContinuous).sub hellContinuous
  have hfZero : f 0 < 0 := by
    have horder := pintzCell_threshold_order hcell
    dsimp only [f]
    simpa [pintzKDenominator, pintzEllDenominator] using
      (sub_neg.mpr horder)
  obtain ⟨radius, hradius, hclose⟩ :=
    Metric.continuousAt_iff.mp hfContinuous (-f 0 / 2) (by linarith)
  obtain ⟨epsilon₀, hepsilon₀, hepsilonOne₀, hcutoff₀, hdecay₀,
      hkAlpha₀, hellAlpha₀, hkMargin₀, hellMargin₀, hbudget₀⟩ :=
    exists_pintz_source_perturbation hcell htarget
  let smallCap : ℝ :=
    min (1 / (180 * (ell : ℝ)))
      (min (eta / (100 * (ell : ℝ))) target)
  have hsmallCap : 0 < smallCap := by dsimp only [smallCap]; positivity
  let epsilon : ℝ := min epsilon₀ (min radius smallCap) / 2
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsilonLe₀ : epsilon ≤ epsilon₀ := by
    dsimp only [epsilon]
    have := min_le_left epsilon₀ (min radius smallCap)
    nlinarith
  have hepsilonLtRadius : epsilon < radius := by
    dsimp only [epsilon]
    have hmin := min_le_right epsilon₀ (min radius smallCap)
    have := min_le_left radius smallCap
    nlinarith
  have hepsilonLtSmall : epsilon < smallCap := by
    dsimp only [epsilon]
    have hmin := min_le_right epsilon₀ (min radius smallCap)
    have := min_le_right radius smallCap
    nlinarith
  have hepsilonTarget : epsilon < target :=
    hepsilonLtSmall.trans_le (by
      dsimp only [smallCap]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hepsilonOne : epsilon ≤ 1 := hepsilonLe₀.trans hepsilonOne₀
  have hcutoff : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ) := by
    have hden : 0 < 10 * (ell : ℝ) := by positivity
    have hquot : epsilon / (10 * (ell : ℝ)) ≤
        epsilon₀ / (10 * (ell : ℝ)) :=
      (div_le_div_iff_of_pos_right hden).mpr hepsilonLe₀
    exact hquot.trans hcutoff₀
  have hdecay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0 := by
    rw [pintz2023DetectorExponent_eq_base_add] at hdecay₀ ⊢
    have hslope : 0 < 1 + eta / (5 * (ell : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_right hepsilonLe₀ hslope.le
    linarith
  have hkAlpha : eta + 6 * epsilon < pintz2023HBAlpha k := by
    linarith
  have hellAlpha : 2 * eta + 6 * epsilon < pintz2023HBAlpha ell := by
    linarith
  have hkMargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta := by
    have := mul_le_mul_of_nonneg_left hepsilonLe₀
      (show (0 : ℝ) ≤ 6 * (k : ℝ) by positivity)
    linarith
  have hellMargin : 6 * (ell : ℝ) * epsilon <
      1 - 2 * eta * ((ell : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_left hepsilonLe₀
      (show (0 : ℝ) ≤ 6 * (ell : ℝ) by positivity)
    linarith
  have hpowerSmall : 6 * (ell : ℝ) * epsilon < 1 / 15 := by
    have hepsilonLtOldSmall : epsilon < 1 / (180 * (ell : ℝ)) :=
      hepsilonLtSmall.trans_le (by
        dsimp only [smallCap]
        exact min_le_left _ _)
    have hmul := mul_lt_mul_of_pos_left hepsilonLtOldSmall
      (show (0 : ℝ) < 6 * (ell : ℝ) by positivity)
    have heq : 6 * (ell : ℝ) * (1 / (180 * (ell : ℝ))) = 1 / 30 := by
      field_simp [hellReal.ne']
      norm_num
    rw [heq] at hmul
    nlinarith
  have hequation420Small : epsilon ≤ eta / (100 * (ell : ℝ)) :=
    hepsilonLtSmall.le.trans (by
      dsimp only [smallCap]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdist : dist epsilon 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hepsilon]
    exact hepsilonLtRadius
  have hfClose := hclose hdist
  rw [Real.dist_eq] at hfClose
  have hfNeg : f epsilon < 0 := by
    have habs := le_abs_self (f epsilon - f 0)
    nlinarith
  have hstrict :
      epsilon / (10 * (ell : ℝ)) +
          pintz2023CriticalScaleExponent k eta epsilon <
        pintz2023EllThreshold eta epsilon ell := by
    dsimp only [f] at hfNeg
    unfold pintz2023CriticalScaleExponent pintz2023EllThreshold
    simpa only [pintzKDenominator] using (sub_neg.mp hfNeg)
  let scaleGap : ℝ :=
    pintz2023EllThreshold eta epsilon ell -
      (epsilon / (10 * (ell : ℝ)) +
        pintz2023CriticalScaleExponent k eta epsilon)
  have hscaleGap : 0 < scaleGap := by
    dsimp only [scaleGap]
    linarith
  let delta : ℝ := min (scaleGap / 2) (target / 2)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by linarith) (by linarith)
  have hdeltaTarget : delta < target := by
    dsimp only [delta]
    have := min_le_right (scaleGap / 2) (target / 2)
    linarith
  have hscale :
      epsilon / (10 * (ell : ℝ)) +
          pintz2023CriticalScaleExponent k eta epsilon + delta <
        pintz2023EllThreshold eta epsilon ell := by
    have hdeltaGap : delta ≤ scaleGap / 2 := by
      dsimp only [delta]
      exact min_le_left _ _
    dsimp only [scaleGap] at hdeltaGap
    linarith
  have hCoeffMono := pintzPerturbedCoefficient_mono_epsilon
    hepsilonLe₀ hk hell hkMargin₀ hellMargin₀
  have hbudget :
      eta * pintzPerturbedCoefficient eta epsilon k ell <
        eta * pintzTheoremOneCoefficient eta k ell + target := by
    have := mul_le_mul_of_nonneg_left hCoeffMono heta.le
    exact this.trans_lt hbudget₀
  exact ⟨⟨epsilon, delta, hepsilon, hepsilonOne, hepsilonTarget,
    hetaUpper.le, hcutoff, hdecay,
    hkAlpha, hellAlpha, hkMargin, hellMargin, hpowerSmall,
    hequation420Small, hdelta,
    hdeltaTarget, hscale, hbudget⟩⟩

#print axioms exists_pintz2023_power_margin_data

end

end GafniTao
