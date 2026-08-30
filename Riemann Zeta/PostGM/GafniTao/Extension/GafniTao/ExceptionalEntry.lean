import GafniTao.SharpExplicitFormula

/-!
# Entry from the genuine exceptional set to equation (2.7)

This file performs the deterministic triangle-inequality step after the local
Brun--Titchmarsh replacement and the sharp truncated explicit formula.  The
source constants remain visible as lower bounds on the natural strip count.
-/

open Filter Set
open scoped ENNReal

namespace GafniTao

/-- The actual short-interval exceptional event restricted to one of the
paper's half-open multiplicative source intervals. -/
noncomputable def localShortIntervalExceptionalSet
    (J : ℕ) (theta delta X : ℝ) : Set ℝ :=
  {x | x ∈ Ico X ((1 + delta / J) * X) ∧
    delta * x ^ theta ≤ |shortIntervalDiscrepancy x theta|}

/-- Real-valued Lebesgue measure of the actual local exceptional event. -/
noncomputable def localShortIntervalExceptionalMeasure
    (J : ℕ) (theta delta X : ℝ) : ℝ :=
  (MeasureTheory.volume
    (localShortIntervalExceptionalSet J theta delta X)).toReal

theorem local_entry_loss_coeff_le_third
    {theta delta J : ℝ} (hdelta : 0 < delta)
    (hJ : 0 < J) (hJLarge : 6 * (8 / theta + 2) ≤ J) :
    2 * (8 / theta + 2) * (delta / J) ≤ delta / 3 := by
  have hscaled := mul_le_mul_of_nonneg_left hJLarge hdelta.le
  rw [show 2 * (8 / theta + 2) * (delta / J) =
      (2 * (8 / theta + 2) * delta) / J by ring,
    div_le_iff₀ hJ]
  nlinarith

theorem rpow_le_two_mul_base_rpow
    {X x theta : ℝ} (hX : 0 < X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1) (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X) :
    x ^ theta ≤ 2 * X ^ theta := by
  have hxPos : 0 < x := hX.trans_le hxLower
  calc
    x ^ theta ≤ (2 * X) ^ theta :=
      Real.rpow_le_rpow hxPos.le hxUpper hthetaLower
    _ = 2 ^ theta * X ^ theta := by
      rw [Real.mul_rpow (by norm_num) hX.le]
    _ ≤ 2 * X ^ theta := by
      gcongr
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          hthetaUpper

/-- For a sufficiently large fixed `J`, the combined local-scale and
Brun--Titchmarsh replacement error is at most `delta/3 * X^theta`, uniformly
on the source interval. -/
theorem eventually_local_replacement_total_le_third
    {J : ℕ} (hJ : 0 < J) {theta delta : ℝ}
    (htheta : 0 < theta) (hthetaUpper : theta ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hJLarge : 6 * (8 / theta + 2) ≤ (J : ℝ)) :
    ∀ᶠ X in atTop, ∀ x : ℝ,
      X ≤ x → x ≤ (1 + delta / J) * X →
      |localMangoldtSum X theta x - mangoldtShortSum x theta| +
          |x / localTau X theta - x ^ theta| ≤
        (delta / 3) * X ^ theta := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hu : 0 < delta / (J : ℝ) := div_pos hdelta hJr
  have huOne : delta / (J : ℝ) ≤ 1 := by
    rw [div_le_one hJr]
    exact hdeltaOne.le.trans (by exact_mod_cast hJ)
  filter_upwards [eventually_abs_localMangoldtSum_sub_short_le_relative
      htheta hthetaUpper hu huOne,
      eventually_ge_atTop 1] with X hReplace hX x hxLower hxUpper
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hxToTwo : x ≤ 2 * X := by
    have hfactor : 1 + delta / (J : ℝ) ≤ 2 := by linarith
    exact hxUpper.trans (mul_le_mul_of_nonneg_right hfactor hXPos.le)
  have hscaleNonneg := localScale_sub_nonneg hXPos htheta.le hthetaUpper
    hxLower hxUpper
  have hscale := localScale_sub_le hXPos htheta.le hthetaUpper
    hxLower hxUpper
  have hxPow := rpow_le_two_mul_base_rpow hXPos htheta.le hthetaUpper
    hxLower hxToTwo
  have hcoeff := local_entry_loss_coeff_le_third hdelta hJr hJLarge
  have hreplace := hReplace x hxLower hxUpper
  rw [abs_of_nonneg hscaleNonneg]
  calc
    |localMangoldtSum X theta x - mangoldtShortSum x theta| +
        (x / localTau X theta - x ^ theta)
        ≤ (8 / theta + 1) * (delta / J) * x ^ theta +
          (delta / J) * x ^ theta := add_le_add hreplace hscale
    _ = (8 / theta + 2) * (delta / J) * x ^ theta := by ring
    _ ≤ (8 / theta + 2) * (delta / J) * (2 * X ^ theta) := by
      gcongr
    _ = (2 * (8 / theta + 2) * (delta / J)) * X ^ theta := by ring
    _ ≤ (delta / 3) * X ^ theta := by
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hXPos.le theta)

/-- Exact algebraic triangle inequality relating the source discrepancy, the
local replacement, the explicit-formula remainder, and the literal full zero
sum. -/
theorem norm_shortDiscrepancy_le_entry_terms
    (J theta X x : ℝ) :
    |shortIntervalDiscrepancy x theta| ≤
      |localMangoldtSum X theta x - mangoldtShortSum x theta| +
      |x / localTau X theta - x ^ theta| +
      ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
          (localTau X theta) x‖ +
      ‖fullZeroIncrementSum (explicitFormulaHeight J theta X)
          (localTau X theta) x‖ := by
  have hid :
      ((shortIntervalDiscrepancy x theta : ℝ) : ℂ) =
        -((localMangoldtSum X theta x - mangoldtShortSum x theta : ℝ) : ℂ) +
        ((x / localTau X theta - x ^ theta : ℝ) : ℂ) +
        sharpExplicitFormulaError (explicitFormulaHeight J theta X)
          (localTau X theta) x +
        -fullZeroIncrementSum (explicitFormulaHeight J theta X)
          (localTau X theta) x := by
    rw [shortIntervalDiscrepancy, sharpExplicitFormulaError_physical_eq]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hid]
  calc
    ‖-((localMangoldtSum X theta x - mangoldtShortSum x theta : ℝ) : ℂ) +
        ((x / localTau X theta - x ^ theta : ℝ) : ℂ) +
        sharpExplicitFormulaError (explicitFormulaHeight J theta X)
          (localTau X theta) x +
        -fullZeroIncrementSum (explicitFormulaHeight J theta X)
          (localTau X theta) x‖
        ≤ ‖-((localMangoldtSum X theta x - mangoldtShortSum x theta : ℝ) : ℂ)‖ +
          ‖((x / localTau X theta - x ^ theta : ℝ) : ℂ)‖ +
          ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
            (localTau X theta) x‖ +
          ‖-fullZeroIncrementSum (explicitFormulaHeight J theta X)
            (localTau X theta) x‖ := by
              grw [norm_add_le, norm_add_le, norm_add_le]
    _ = _ := by
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- The source exceptional event on one multiplicative interval is eventually
contained in the literal full-zero event of equation (2.7).  This theorem
consumes the true discrepancy, the proved local replacement, and the exact
sharp explicit-formula predicate. -/
theorem eventually_localExceptionalSet_subset_equation27
    (hFormula : SharpTruncatedExplicitFormulaBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ}, 0 < J →
      ∀ {theta delta : ℝ}, 0 < theta → theta < 1 →
      0 < delta → delta < 1 →
      6 * (8 / theta + 2) ≤ (J : ℝ) →
      24 * C ≤ delta * J →
      ∀ᶠ X in atTop,
        localShortIntervalExceptionalSet J theta delta X ⊆
          equation27FullZeroLargeSet J theta delta X := by
  obtain ⟨C, hC, hFormulaSmall⟩ :=
    eventually_sharpExplicitFormulaError_physical_le_third hFormula
  refine ⟨C, hC, ?_⟩
  intro J hJ theta delta htheta hthetaUpper hdelta hdeltaOne
    hJLocal hJFormula
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have huOne : delta / (J : ℝ) ≤ 1 := by
    rw [div_le_one hJr]
    exact hdeltaOne.le.trans (by exact_mod_cast hJ)
  filter_upwards [eventually_local_replacement_total_le_third hJ htheta
      hthetaUpper.le hdelta hdeltaOne hJLocal,
      hFormulaSmall hJ htheta hthetaUpper hdelta hJFormula,
      eventually_ge_atTop 1] with X hLocal hExplicit hX x hx
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hxLower : X ≤ x := hx.1.1
  have hxUpper : x ≤ (1 + delta / (J : ℝ)) * X := hx.1.2.le
  have hxToTwo : x ≤ 2 * X := by
    have hfactor : 1 + delta / (J : ℝ) ≤ 2 := by linarith
    exact hxUpper.trans (mul_le_mul_of_nonneg_right hfactor hXPos.le)
  have hTriangle := norm_shortDiscrepancy_le_entry_terms
    (J : ℝ) theta X x
  have hLocalX := hLocal x hxLower hxUpper
  have hExplicitX := hExplicit x hxLower hxToTwo
  have hxPowLower : X ^ theta ≤ x ^ theta :=
    Real.rpow_le_rpow hXPos.le hxLower htheta.le
  refine ⟨hx.1, ?_⟩
  rw [div_localTau_self_eq_rpow hXPos]
  have hDiscrepancy : delta * x ^ theta ≤
      |shortIntervalDiscrepancy x theta| := hx.2
  have hDiscrepancyX : delta * X ^ theta ≤
      |shortIntervalDiscrepancy x theta| :=
    (mul_le_mul_of_nonneg_left hxPowLower hdelta.le).trans hDiscrepancy
  have hErrors :
      |localMangoldtSum X theta x - mangoldtShortSum x theta| +
          |x / localTau X theta - x ^ theta| +
        ‖sharpExplicitFormulaError (explicitFormulaHeight J theta X)
          (localTau X theta) x‖ ≤
        2 * ((delta / 3) * X ^ theta) := by
    linarith
  have hTotal :
      |shortIntervalDiscrepancy x theta| ≤
        2 * ((delta / 3) * X ^ theta) +
          ‖fullZeroIncrementSum (explicitFormulaHeight J theta X)
            (localTau X theta) x‖ := by
    linarith
  nlinarith

theorem equation27FullZeroLargeSet_subset_sourceInterval
    (J : ℕ) (theta delta X : ℝ) :
    equation27FullZeroLargeSet J theta delta X ⊆
      Ico X ((1 + delta / J) * X) := by
  intro x hx
  exact hx.1

theorem measure_equation27FullZeroLargeSet_ne_top
    (J : ℕ) (theta delta X : ℝ) :
    MeasureTheory.volume (equation27FullZeroLargeSet J theta delta X) ≠ ∞ := by
  apply ne_of_lt
  calc
    MeasureTheory.volume (equation27FullZeroLargeSet J theta delta X) ≤
        MeasureTheory.volume (Ico X ((1 + delta / J) * X)) :=
      MeasureTheory.measure_mono
        (equation27FullZeroLargeSet_subset_sourceInterval J theta delta X)
    _ < ∞ := measure_Ico_lt_top

/-- Event inclusion upgraded to the exact real-valued measures used in the
fixed-power interfaces. -/
theorem eventually_localExceptionalMeasure_le_equation27
    (hFormula : SharpTruncatedExplicitFormulaBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ}, 0 < J →
      ∀ {theta delta : ℝ}, 0 < theta → theta < 1 →
      0 < delta → delta < 1 →
      6 * (8 / theta + 2) ≤ (J : ℝ) →
      24 * C ≤ delta * J →
      ∀ᶠ X in atTop,
        localShortIntervalExceptionalMeasure J theta delta X ≤
          equation27FullZeroMeasure J theta delta X := by
  obtain ⟨C, hC, hSubset⟩ :=
    eventually_localExceptionalSet_subset_equation27 hFormula
  refine ⟨C, hC, ?_⟩
  intro J hJ theta delta htheta hthetaUpper hdelta hdeltaOne
    hJLocal hJFormula
  filter_upwards [hSubset hJ htheta hthetaUpper hdelta hdeltaOne
      hJLocal hJFormula] with X hX
  unfold localShortIntervalExceptionalMeasure equation27FullZeroMeasure
  apply ENNReal.toReal_mono
    (measure_equation27FullZeroLargeSet_ne_top J theta delta X)
  exact MeasureTheory.measure_mono hX

/-- The local genuine exceptional measure inherits every fixed-power bound
proved for the literal equation-(2.7) full-zero event. -/
theorem localExceptionalMeasure_fixedPowerBound_of_equation27
    (hFormula : SharpTruncatedExplicitFormulaBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ}, 0 < J →
      ∀ {theta delta xi : ℝ}, 0 < theta → theta < 1 →
      0 < delta → delta < 1 →
      6 * (8 / theta + 2) ≤ (J : ℝ) →
      24 * C ≤ delta * J →
      FixedPowerBound
        (fun X => equation27FullZeroMeasure J theta delta X) xi →
      FixedPowerBound
        (fun X => localShortIntervalExceptionalMeasure J theta delta X) xi := by
  obtain ⟨C, hC, hMeasure⟩ :=
    eventually_localExceptionalMeasure_le_equation27 hFormula
  refine ⟨C, hC, ?_⟩
  intro J hJ theta delta xi htheta hthetaUpper hdelta hdeltaOne
    hJLocal hJFormula hBound
  rcases hBound with ⟨D, hD, hEventually⟩
  refine ⟨D, hD, ?_⟩
  filter_upwards [hMeasure hJ htheta hthetaUpper hdelta hdeltaOne
      hJLocal hJFormula, hEventually] with X hMeasureX hBoundX
  calc
    |localShortIntervalExceptionalMeasure J theta delta X| =
        localShortIntervalExceptionalMeasure J theta delta X := by
          exact abs_of_nonneg ENNReal.toReal_nonneg
    _ ≤ equation27FullZeroMeasure J theta delta X := hMeasureX
    _ ≤ |equation27FullZeroMeasure J theta delta X| := le_abs_self _
    _ ≤ D * X ^ xi := hBoundX

end GafniTao
