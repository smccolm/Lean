import GafniTao.GeneralEnvelope
import GafniTao.PintzNearOneNative
import GafniTao.SharpPerronLowHeight

/-!
# Unconditional Gafni--Tao exponent theorems

This module discharges the remaining analytic parameters of the exact
Section 2 assembly with the kernel-checked sharp explicit formula, the proved
Pintz/Ford near-one package, and the frozen smooth cutoff.
-/

namespace GafniTao

noncomputable section

/-- Exact, unconditional Gafni--Tao Theorem 1.3 for the source range
`0 < theta < 1`. -/
theorem gafniTaoTheorem13_native
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤ refinedExceptionalUpperExponent theta := by
  obtain ⟨c, Tzero, Tdensity, hc, hZeroFree, hDensity⟩ :=
    exists_pintz_nearOne_log_density_native
  exact gafniTaoTheorem13_conditional
    (Classical.choice RiemannZeta.GuthMaynard.exists_gmSmoothCutoff)
    sharpTruncatedExplicitFormulaBound_native hDensity hZeroFree
    pintzNearOneDensityCoefficient_pos hc hthetaLower hthetaUpper

/-- Exact, unconditional ordinary second-moment Gafni--Tao Theorem 1.2. -/
theorem gafniTaoTheorem12_native
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤ ordinaryExceptionalUpperExponent theta :=
  (gafniTaoTheorem13_native hthetaLower hthetaUpper).trans
    (refinedExceptionalUpperExponent_le_ordinary theta)

/-- The source's alternate strict-upper-half formulation following Theorem
1.3.  This is stronger than merely adjoining a redundant maximum to the
full-strip formula. -/
theorem gafniTaoTheorem13_max_native
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤
      max (((1 - theta : ℝ) : EReal))
        (upperHalfRefinedExceptionalUpperExponent theta) :=
  (gafniTaoTheorem13_native hthetaLower hthetaUpper).trans
    (refinedExceptionalUpperExponent_le_upperHalf_max hthetaUpper)

/-- The source's alternate strict-upper-half ordinary second-moment
formulation. -/
theorem gafniTaoTheorem12_max_native
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤
      max (((1 - theta : ℝ) : EReal))
        (upperHalfOrdinaryExceptionalUpperExponent theta) :=
  (gafniTaoTheorem13_max_native hthetaLower hthetaUpper).trans
    (max_le_max_left _
      (upperHalfRefinedExceptionalUpperExponent_le_ordinary theta))

#print axioms gafniTaoTheorem13_native
#print axioms gafniTaoTheorem12_native

end

end GafniTao
