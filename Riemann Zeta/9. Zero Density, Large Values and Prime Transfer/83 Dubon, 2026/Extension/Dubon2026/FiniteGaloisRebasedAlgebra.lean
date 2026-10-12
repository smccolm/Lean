import Dubon2026.FiniteGaloisStageExtendScalars

/-! # The literal algebra structure of a rebased original finite stage -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)

/-- Both descriptions of the original E-algebra H have the same
literal algebra map and hence the same actual algebra structure. -/
theorem finiteGaloisStageExtendScalars_algebra_eq :
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    (inferInstance : Algebra E H) =
      (inferInstance : Algebra E (finiteGaloisStageExtendScalars E H hEH)) := by
  apply Algebra.algebra_ext
  intro x
  rfl

end
end Dubon2026
