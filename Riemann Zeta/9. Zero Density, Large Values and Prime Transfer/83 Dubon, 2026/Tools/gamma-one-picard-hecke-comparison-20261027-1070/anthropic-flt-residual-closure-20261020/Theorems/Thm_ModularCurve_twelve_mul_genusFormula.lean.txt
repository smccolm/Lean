import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_twelve_mul_genusFormula

open ModularCurve
theorem ModularCurve.twelve_mul_genusFormula (N : ℕ) : 12 * genusFormula N = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ) - 6 * (cuspCount N : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_twelve_mul_genusFormula.solution
