import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq

open ModularCurve IntermediateField
theorem ModularCurve.ModularPolynomialData.minpoly_jqN_eq {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hirr : ModularCurve.PhiIrreducible data) :
    minpoly (↥ℚ⟮ModularCurve.jq⟯) (ModularCurve.jqN N) = data.toAdjoin := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.solution
