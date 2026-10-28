import Definitions.Def_ModularCurve_CycSubRootBridgeN
import P2M.Util
import P2M.Sol.S_ModularCurve_TatePoint_fullKernelDiscAt
attribute [-simp] WeierstrassCurve.veluPointMap2_zero

open scoped Classical
theorem ModularCurve.TatePoint.fullKernelDiscAt (N : ℕ) [NeZero N] : FullKernelDiscAt N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TatePoint_fullKernelDiscAt.solution
