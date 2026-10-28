import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_periodLatticeHeckeStable

theorem ModularCurve.periodLatticeHeckeStable (N : ℕ) [NeZero N] :
    ModularCurve.PeriodLatticeHeckeStable N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodLatticeHeckeStable.solution
