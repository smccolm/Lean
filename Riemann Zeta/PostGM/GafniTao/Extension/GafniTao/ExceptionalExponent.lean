import GafniTao.ExceptionalCover

/-!
# Passing from fixed powers to the exceptional exponent

This file takes the exact global exceptional-set estimate proved after the
multiplicative cover and performs the extended-real limiting argument.  The
result is the `max (1-theta) ...` form of Gafni--Tao Theorem 1.3, conditional
only on the three still-open published analytic inputs.  In particular, no
continuity of the zero-density exponent is used.
-/

namespace GafniTao

/-- Real powers are order dense in `EReal`: bounding an extended-real value by
every real power strictly above `a` bounds it by `a` itself. -/
theorem ereal_le_of_le_coe_of_gt
    {x a : EReal} (h : ∀ xi : ℝ, a < (xi : EReal) → x ≤ (xi : EReal)) :
    x ≤ a := by
  apply le_of_not_gt
  intro hax
  obtain ⟨xi, haxi, hx⟩ := EReal.lt_iff_exists_real_btwn.mp hax
  exact (not_lt_of_ge (h xi haxi)) hx

/-- For a discrepancy threshold in `(0,1)`, the assembled source inputs give
the exact extended-real upper bound, rather than merely all its real
approximants. -/
theorem exceptionalExponentDelta_le_refined_max_of_source_inputs
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    exceptionalExponentDelta delta theta ≤
      max (((1 - theta : ℝ) : EReal))
        (refinedExceptionalUpperExponent theta) := by
  apply ereal_le_of_le_coe_of_gt
  intro xi hxi
  exact exceptionalExponentDelta_le
    (exceptionalMeasure_fixedPowerBound_of_source_inputs cutoff hFormula
      hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta hdeltaOne hxi)

/-- The restriction `delta < 1` is removed by literal antitonicity of the
exceptional sets. -/
theorem exceptionalExponentDelta_le_refined_max_of_source_inputs_all
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) :
    exceptionalExponentDelta delta theta ≤
      max (((1 - theta : ℝ) : EReal))
        (refinedExceptionalUpperExponent theta) := by
  by_cases hdeltaOne : delta < 1
  · exact exceptionalExponentDelta_le_refined_max_of_source_inputs cutoff
      hFormula hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta
        hdeltaOne
  · have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
    have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
    have hhalfDelta : (1 / 2 : ℝ) ≤ delta := by
      have : 1 ≤ delta := le_of_not_gt hdeltaOne
      linarith
    exact (exceptionalExponentDelta_anti hhalfDelta).trans
      (exceptionalExponentDelta_le_refined_max_of_source_inputs cutoff
        hFormula hDensity hZeroFree hC hc hthetaLower hthetaUpper hhalfPos
          hhalfOne)

/-- Conditional `max (1-theta, ...)` form of Gafni--Tao Theorem 1.3.  The
three parameters are exact, separately named upstream source statements;
this theorem performs the complete downstream exceptional-set deduction. -/
theorem gafniTaoTheorem13_max_conditional
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤
      max (((1 - theta : ℝ) : EReal))
        (refinedExceptionalUpperExponent theta) := by
  apply exceptionalExponent_le
  intro delta hdelta
  exact exceptionalExponentDelta_le_refined_max_of_source_inputs_all cutoff
    hFormula hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta

/-- Exact principal-form bound for one discrepancy threshold. -/
theorem exceptionalExponentDelta_le_refined_of_source_inputs
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    exceptionalExponentDelta delta theta ≤
      refinedExceptionalUpperExponent theta := by
  apply ereal_le_of_le_coe_of_gt
  intro xi hxi
  exact exceptionalExponentDelta_le
    (exceptionalMeasure_fixedPowerBound_of_source_inputs_exact cutoff hFormula
      hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta hdeltaOne hxi)

/-- Exact principal-form threshold bound for every positive discrepancy
parameter, using antitonicity only to remove the auxiliary `delta < 1`
restriction. -/
theorem exceptionalExponentDelta_le_refined_of_source_inputs_all
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta delta : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hdelta : 0 < delta) :
    exceptionalExponentDelta delta theta ≤
      refinedExceptionalUpperExponent theta := by
  by_cases hdeltaOne : delta < 1
  · exact exceptionalExponentDelta_le_refined_of_source_inputs cutoff
      hFormula hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta
        hdeltaOne
  · have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
    have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
    have hhalfDelta : (1 / 2 : ℝ) ≤ delta := by
      have : 1 ≤ delta := le_of_not_gt hdeltaOne
      linarith
    exact (exceptionalExponentDelta_anti hhalfDelta).trans
      (exceptionalExponentDelta_le_refined_of_source_inputs cutoff hFormula
        hDensity hZeroFree hC hc hthetaLower hthetaUpper hhalfPos hhalfOne)

/-- Conditional exact Gafni--Tao Theorem 1.3.  Its premises are the literal
upstream analytic inputs; the conclusion is the source infimum--supremum
formula, not the alternate max form. -/
theorem gafniTaoTheorem13_conditional
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤ refinedExceptionalUpperExponent theta := by
  apply exceptionalExponent_le
  intro delta hdelta
  exact exceptionalExponentDelta_le_refined_of_source_inputs_all cutoff
    hFormula hDensity hZeroFree hC hc hthetaLower hthetaUpper hdelta

end GafniTao
