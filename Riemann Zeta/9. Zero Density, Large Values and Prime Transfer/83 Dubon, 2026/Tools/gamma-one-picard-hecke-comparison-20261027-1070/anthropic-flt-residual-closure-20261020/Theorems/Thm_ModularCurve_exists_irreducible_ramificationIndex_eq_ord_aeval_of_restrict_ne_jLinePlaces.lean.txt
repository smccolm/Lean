import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open IntermediateField AlgebraicCurve
theorem ModularCurve.exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlace1728 →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceZero →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceInfty →
      ∃ p : Polynomial ℚ, Irreducible p ∧ p.Monic ∧ p.eval 0 ≠ 0 ∧ p.eval 1728 ≠ 0 ∧
        0 < w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) ∧
        (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) = w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces.solution
