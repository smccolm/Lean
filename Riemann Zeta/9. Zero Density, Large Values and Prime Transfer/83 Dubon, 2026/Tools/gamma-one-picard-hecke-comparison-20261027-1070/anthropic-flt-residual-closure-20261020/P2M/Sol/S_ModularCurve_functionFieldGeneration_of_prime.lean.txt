import Definitions.Def_ModularCurve_X0
import P2M.Util
namespace P2MW.S_ModularCurve_functionFieldGeneration_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ :=by
  intro d hd hne
  haveI := hne
  rcases (Nat.dvd_prime hℓ).mp hd with rfl | rfl
  · rw [qExpand_one_apply]
    exact subset_adjoin ℚ _ (Set.mem_insert _ _)
  · exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end
