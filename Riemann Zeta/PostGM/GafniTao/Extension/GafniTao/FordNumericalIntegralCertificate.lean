import GafniTao.FordGapExplicitIdentity
import GafniTao.FordBernsteinPositivity

/-!
# Kernel-checked numerical integral certificate for Ford's estimate

This is the consumer of the exact source identity and of all eight Bernstein
positivity certificates.  It proves the numerical inequality for the original
source-defined polynomial majorant, and then for the normalized integral.
-/

namespace GafniTao

noncomputable section

theorem fordNumericalGap_nonneg
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGap := by
  rw [fordNumericalGap_eq_explicit]
  exact fordNumericalGapExplicit_nonneg hy0 hy

theorem fordNumericalPolynomialUpper_le_target
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    fordNumericalPolynomialUpper y ≤ (fordNumericalTarget : ℝ) := by
  have hden : 0 < 9 * y + 27 / 4 := by positivity
  rw [fordNumericalPolynomialUpper_eq_ratio hden.ne']
  apply (div_le_iff₀ (by simpa only [fordNumericalDenominator_eval] using hden)).2
  have hgap := fordNumericalGap_nonneg hy0 hy
  rw [fordNumericalGap_eval] at hgap
  rw [fordNumericalDenominator_eval]
  linarith

theorem fordNumericalPolynomialUpper_le_source_constant
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    fordNumericalPolynomialUpper y ≤ (108754 / 100000 : ℝ) := by
  simpa [fordNumericalTarget] using fordNumericalPolynomialUpper_le_target hy0 hy

theorem integral_fordNormalizedRatio_le_source_constant
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
      (108754 / 100000 : ℝ) :=
  (integral_fordNormalizedRatio_le_numericalPolynomialUpper hy0 hy).trans
    (fordNumericalPolynomialUpper_le_source_constant hy0 hy)

#print axioms fordNumericalGap_nonneg
#print axioms fordNumericalPolynomialUpper_le_source_constant
#print axioms integral_fordNormalizedRatio_le_source_constant

end

end GafniTao
