import Definitions.Def_ModularCurve_EMD
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_place_eq_of_induces
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve ModularCurve IsDedekindDomain WithZero
theorem ModularCurve.place_eq_of_induces {N : ℕ} [NeZero N]
    {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ)}
    {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (h : Induces ψ w) (h' : Induces ψ w') : w = w' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_place_eq_of_induces.solution
