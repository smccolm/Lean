import Mathlib
import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_hasEquivariantPrimitive

theorem ModularCurve.exists_hasEquivariantPrimitive (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ F : UpperHalfPlane → ℂ, ModularCurve.HasEquivariantPrimitive N f F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_hasEquivariantPrimitive.solution
