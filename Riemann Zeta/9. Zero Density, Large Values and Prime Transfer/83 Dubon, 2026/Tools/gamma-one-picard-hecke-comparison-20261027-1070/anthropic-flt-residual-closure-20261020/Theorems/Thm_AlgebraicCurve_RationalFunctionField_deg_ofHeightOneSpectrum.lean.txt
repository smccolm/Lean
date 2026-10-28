import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum (K : Type*) [Field K] {w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)} {p : Polynomial K} (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum
