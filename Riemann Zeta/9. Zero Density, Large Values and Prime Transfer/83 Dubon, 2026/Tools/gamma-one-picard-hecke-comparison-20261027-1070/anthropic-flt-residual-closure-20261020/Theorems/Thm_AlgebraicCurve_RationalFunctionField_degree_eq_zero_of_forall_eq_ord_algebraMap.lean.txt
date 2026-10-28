import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap {K : Type*} [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K), (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) → Divisor.degree D = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.solution
