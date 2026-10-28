import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_minpoly_jqN_eq_toAdjoin

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.minpoly_jqN_eq_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h : PhiIrreducible data) : minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) = data.toAdjoin := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_minpoly_jqN_eq_toAdjoin.solution
