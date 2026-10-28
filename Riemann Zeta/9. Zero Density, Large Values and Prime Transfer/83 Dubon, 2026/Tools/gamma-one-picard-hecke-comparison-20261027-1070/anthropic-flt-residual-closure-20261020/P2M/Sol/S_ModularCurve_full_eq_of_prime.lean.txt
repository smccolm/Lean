import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_functionFieldGeneration_of_prime
import P2M.Util
namespace P2MW.S_ModularCurve_full_eq_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (ModularCurve.functionFieldGeneration_iff_full_eq ℓ).mp (ModularCurve.functionFieldGeneration_of_prime hℓ)

end
