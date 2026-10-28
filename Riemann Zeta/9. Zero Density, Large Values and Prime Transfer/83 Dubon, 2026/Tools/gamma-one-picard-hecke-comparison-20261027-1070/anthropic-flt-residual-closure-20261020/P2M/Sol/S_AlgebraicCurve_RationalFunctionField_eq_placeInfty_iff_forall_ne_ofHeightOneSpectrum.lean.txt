import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : v = placeInfty K ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by
  constructor
  · rintro rfl
    exact AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K
  · intro h
    exact AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum h
      (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K)
