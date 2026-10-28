import Definitions.Def_ModularCurve_CycSubRootBridgeN
import P2M.Util
import P2M.Sol.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd

open scoped Classical
theorem ModularCurve.TatePoint.fullKernelIsRootAt_of_odd (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelIsRootAt N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd.solution
