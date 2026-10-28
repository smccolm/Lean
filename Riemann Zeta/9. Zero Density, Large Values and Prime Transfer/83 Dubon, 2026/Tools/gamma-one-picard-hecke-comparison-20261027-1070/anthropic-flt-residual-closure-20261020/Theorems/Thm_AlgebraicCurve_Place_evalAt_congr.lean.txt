import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_congr
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
theorem AlgebraicCurve.Place.evalAt_congr {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (h : f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_congr.solution
