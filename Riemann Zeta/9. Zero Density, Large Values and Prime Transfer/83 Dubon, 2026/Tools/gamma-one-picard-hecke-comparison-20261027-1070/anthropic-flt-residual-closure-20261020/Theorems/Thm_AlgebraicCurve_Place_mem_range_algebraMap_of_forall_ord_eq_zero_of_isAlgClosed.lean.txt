import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
theorem AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (j : F) (hj : Transcendental K j) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.solution
