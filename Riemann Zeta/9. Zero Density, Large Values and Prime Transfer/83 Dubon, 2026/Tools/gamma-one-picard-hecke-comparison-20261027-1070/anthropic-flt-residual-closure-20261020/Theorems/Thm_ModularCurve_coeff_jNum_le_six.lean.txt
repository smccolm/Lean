import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_jNum_le_six

open ModularCurve Polynomial
theorem ModularCurve.coeff_jNum_le_six :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧ PowerSeries.coeff 2 jNum = 196884 ∧
      PowerSeries.coeff 3 jNum = 21493760 ∧ PowerSeries.coeff 4 jNum = 864299970 ∧
      PowerSeries.coeff 5 jNum = 20245856256 ∧ PowerSeries.coeff 6 jNum = 333202640600 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_jNum_le_six.solution
