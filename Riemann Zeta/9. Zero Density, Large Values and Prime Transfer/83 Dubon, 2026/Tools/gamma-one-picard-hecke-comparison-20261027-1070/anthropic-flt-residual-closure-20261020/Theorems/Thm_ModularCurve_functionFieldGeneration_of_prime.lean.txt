import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_functionFieldGeneration_of_prime

open ModularCurve IntermediateField
theorem ModularCurve.functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_functionFieldGeneration_of_prime.solution
