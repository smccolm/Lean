import Definitions.Def_ModularCurve_CycSubRootBridgeN
import P2M.Util
import P2M.Sol.S_ModularCurve_TatePoint_fullKernelDiscAt_of_odd

open scoped Classical
theorem ModularCurve.TatePoint.fullKernelDiscAt_of_odd (N : ℕ) [NeZero N] (hN : Odd N) : FullKernelDiscAt N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TatePoint_fullKernelDiscAt_of_odd.solution
