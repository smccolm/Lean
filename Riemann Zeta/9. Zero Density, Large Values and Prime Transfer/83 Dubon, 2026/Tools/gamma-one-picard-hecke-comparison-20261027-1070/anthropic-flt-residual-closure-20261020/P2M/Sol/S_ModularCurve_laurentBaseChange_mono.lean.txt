import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_laurentBaseChange_mono

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : ModularCurve.laurentBaseChange L F₀ ≤ ModularCurve.laurentBaseChange L F₁ :=
  by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)
