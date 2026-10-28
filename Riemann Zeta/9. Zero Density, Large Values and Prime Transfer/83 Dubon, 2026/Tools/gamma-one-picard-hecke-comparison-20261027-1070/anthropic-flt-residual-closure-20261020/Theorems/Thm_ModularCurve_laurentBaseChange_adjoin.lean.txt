import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_adjoin
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

theorem ModularCurve.laurentBaseChange_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_adjoin.solution
