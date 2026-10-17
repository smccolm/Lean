import Dubon2026.OriginalUnrestrictedKummerNormField

/-! # Realizing the original number field in the auxiliary arithmetic union

An actual embedding into the algebraically closed unrestricted union
identifies each original number field with its finite rational image.
This supplies the base realization for DUB-17's constructed Kummer norm
field. The proved literal norm descent returns its containment to the
original base, avoiding transport of the normalized cohomology system.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra unrestrictedArithmeticUnionClosed

/-- Every original number field has an actual finite rational image in
the unrestricted arithmetic union and its proved field isomorphism. -/
theorem originalNumberField_exists_unrestricted_arithmetic_realization
    (K : Type) [Field K] [NumberField K] :
    ∃ F : IntermediateField ℚ (rationalUnramifiedExtension 0),
      FiniteDimensional ℚ F ∧ Nonempty (K ≃ₐ[ℚ] F) := by
  let i : K →ₐ[ℚ] rationalUnramifiedExtension 0 := IsAlgClosed.lift
  let F := i.fieldRange
  let e : K ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField i
  exact ⟨F, Module.Finite.of_surjective e.toLinearMap e.surjective, ⟨e⟩⟩

end
end Dubon2026
