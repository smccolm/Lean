import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_HahnSeries_hasRamBound_C
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

open HahnSeries
theorem HahnSeries.hasRamBound_C {K : Type*} [Field K] {e : ℕ} (a : K) : HasRamBound e (C a : HahnSeries ℚ K) := by p2m_exact_reverting @_root_.P2MW.S_HahnSeries_hasRamBound_C.solution
