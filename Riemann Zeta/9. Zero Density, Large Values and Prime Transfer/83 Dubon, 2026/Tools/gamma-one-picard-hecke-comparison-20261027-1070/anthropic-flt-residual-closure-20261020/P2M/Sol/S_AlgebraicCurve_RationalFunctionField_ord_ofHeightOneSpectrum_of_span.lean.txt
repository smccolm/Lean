import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log w hp hw
    (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]
