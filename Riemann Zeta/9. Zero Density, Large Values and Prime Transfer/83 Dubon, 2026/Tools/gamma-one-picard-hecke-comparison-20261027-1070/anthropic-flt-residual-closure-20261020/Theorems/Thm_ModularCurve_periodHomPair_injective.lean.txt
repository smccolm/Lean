import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_ModularCurve_periodHomPair_injective

theorem ModularCurve.periodHomPair_injective (N : ℕ) [NeZero N] :
    Function.Injective (ModularCurve.periodHomPair N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodHomPair_injective.solution
