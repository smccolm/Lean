import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_card_primCosetReps_eq_dedekindPsi

theorem ModularCurve.card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (ModularCurve.primCosetReps N).card = ModularCurve.dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_primCosetReps_eq_dedekindPsi.solution
