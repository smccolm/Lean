import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_functionFieldGeneration_iff_full_eq

open ModularCurve IntermediateField
theorem ModularCurve.functionFieldGeneration_iff_full_eq (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq.solution
