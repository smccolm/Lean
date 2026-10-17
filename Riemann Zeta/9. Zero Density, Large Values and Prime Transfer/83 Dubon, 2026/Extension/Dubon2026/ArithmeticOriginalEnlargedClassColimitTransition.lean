import Dubon2026.ArithmeticOriginalStageClassColimitNaturality

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union inclusion. -/
local instance originalEnlargedNaturalUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual finite-stage rational inclusions. -/
local instance originalEnlargedNaturalFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[ℚ] F.val)
  (hi : ∀ x : P, (i x : Ω) = (x.val : Ω))

include hi in
/-- The two original class transitions through the embedded stage and the
same enlarged scalar-criterion stage retain the initial class-colimit value. -/
theorem arithmeticOriginalEnlargedClassToColimit_transition
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField) :
    letI : Algebra P F.val := i.toAlgebra
    letI : Module P F.val := i.toAlgebra.toModule
    letI : SMul P F.val := i.toAlgebra.toSMul
    letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
    letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
    letI : Module F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toModule
    letI : SMul F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
    ∀ x : arithmeticClassesModOutsideStageRep ℚ Ω a ha P,
      (arithmeticOriginalStageClassToColimit Ω a ha L).hom
        ((originalRationalExceptionalClassTransition F.val L.val a ha).hom
          ((originalRationalExceptionalClassTransition P F.val a ha).hom x)) =
        (coefficientRepresentationColimitOf _
          (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) P).hom x := by
  letI : Algebra P F.val := i.toAlgebra
  letI : Module P F.val := i.toAlgebra.toModule
  letI : SMul P F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Module F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toModule
  letI : SMul F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  let j : P →ₐ[ℚ] L.val := (IntermediateField.inclusion hFL).comp i
  have hj : ∀ x : P, (j x : Ω) = (x.val : Ω) := hi
  letI : Algebra P L.val := j.toAlgebra
  letI : Module P L.val := j.toAlgebra.toModule
  letI : SMul P L.val := j.toAlgebra.toSMul
  letI : IsScalarTower ℚ P L.val := IsScalarTower.of_algHom j
  letI : IsScalarTower P F.val L.val := IsScalarTower.of_algebraMap_eq' rfl
  intro x
  rw [originalRationalExceptionalClassTransition_tower P F.val L.val]
  exact arithmeticOriginalStageClassToColimit_transition Ω a ha P L j hj x

end
end Dubon2026
