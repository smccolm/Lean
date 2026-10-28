import Definitions.Def_ModularCurve_X0
import P2M.Util
namespace P2MW.S_ModularCurve_functionFieldGeneration_iff_full_eq

open ModularCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N :=by
  constructor
  · intro hgen
    refine le_antisymm ?_ (modularFunctionField_le_full N)
    rw [modularFunctionFieldFull, adjoin_le_iff]
    rintro x ⟨d, hne, hdvd, rfl⟩
    exact hgen d hdvd hne
  · intro heq d hdvd hne
    haveI := hne
    show qExpand ℚ d jq ∈ modularFunctionField N
    rw [← heq]
    exact jqd_mem_full N hdvd

end
