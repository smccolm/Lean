import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import P2M.Util
namespace P2MW.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull

open ModularCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N) = IntermediateField.adjoin L {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = ModularCurve.jqNModC L d} := by
  rw [modularFunctionFieldFull, laurentBaseChange_adjoin]
  congr 1
  ext x
  simp only [Set.mem_image, divisorExpansions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨d, hd, hdvd, rfl⟩, rfl⟩
    exact ⟨d, hd, hdvd, (coeffEmb_jqN L d)⟩
  · rintro ⟨d, hd, hdvd, rfl⟩
    exact ⟨qExpand ℚ d jq, ⟨d, hd, hdvd, rfl⟩, coeffEmb_jqN L d⟩
