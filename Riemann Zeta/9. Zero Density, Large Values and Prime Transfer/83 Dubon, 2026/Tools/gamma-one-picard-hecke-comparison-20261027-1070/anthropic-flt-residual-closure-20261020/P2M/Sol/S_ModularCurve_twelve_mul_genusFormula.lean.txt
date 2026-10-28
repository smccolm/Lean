import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
namespace P2MW.S_ModularCurve_twelve_mul_genusFormula

open ModularCurve

theorem solution (N : ℕ) :
    12 * genusFormula N
      = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ)
        - 6 * (cuspCount N : ℚ) := by
  unfold genusFormula
  ring
