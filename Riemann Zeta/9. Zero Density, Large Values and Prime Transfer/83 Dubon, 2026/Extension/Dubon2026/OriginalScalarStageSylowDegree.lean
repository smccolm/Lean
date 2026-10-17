import Dubon2026.ArithmeticOriginalStageSubgroupClassH2
import Mathlib.GroupTheory.Sylow

/-! # The actual normalization stage has prime-power degree

The chosen Sylow fixed field gives the required prime-power extension
without a degree restriction on the original scalar stage. This supplies
the field-degree input for reusing DUB-17's proved prime-power invariants.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Retain the actual rational algebra of the original finite stage. -/
local instance originalScalarSylowDegreeFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- The original scalar stage over the actual Sylow fixed field has a
power of the coefficient prime as its degree, including degree one. -/
theorem originalScalarStage_sylow_fixedField_degree
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(L.val/ℚ)) :
    ∃ t : ℕ, Module.finrank (IntermediateField.fixedField (S : Subgroup Gal(L.val/ℚ))) L.val = p ^ t := by
  obtain ⟨t, ht⟩ := S.isPGroup'.exists_card_eq
  exact ⟨t, (IntermediateField.finrank_fixedField_eq_card (S : Subgroup Gal(L.val/ℚ))).trans ht⟩

end
end Dubon2026
