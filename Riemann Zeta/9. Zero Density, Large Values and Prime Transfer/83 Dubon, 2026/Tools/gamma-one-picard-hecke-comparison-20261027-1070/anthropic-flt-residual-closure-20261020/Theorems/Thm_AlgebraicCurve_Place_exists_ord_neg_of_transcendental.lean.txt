import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_neg_of_transcendental {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : ∃ v : Place K F, v.ord x < 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental.solution
