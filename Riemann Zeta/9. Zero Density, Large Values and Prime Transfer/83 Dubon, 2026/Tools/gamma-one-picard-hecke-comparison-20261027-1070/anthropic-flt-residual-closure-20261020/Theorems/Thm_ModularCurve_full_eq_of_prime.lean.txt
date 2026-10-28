import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_full_eq_of_prime

open ModularCurve IntermediateField
theorem ModularCurve.full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_full_eq_of_prime.solution
