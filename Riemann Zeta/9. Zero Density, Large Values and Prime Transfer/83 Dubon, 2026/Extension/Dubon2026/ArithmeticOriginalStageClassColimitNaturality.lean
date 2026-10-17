import Dubon2026.ArithmeticOriginalStageClassColimit
import Dubon2026.OriginalRationalExceptionalClassTransitionTower

/-! # The scalar-stage class inclusion preserves the descended representative

The original ambient values identify the finite image embedding with the
actual intermediate-field inclusion. Original class base-change composition
and the colimit relation then give the exact coefficient square required
for DUB-17's enlarged-stage continuous cup comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union inclusion. -/
local instance originalStageNaturalUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual finite-stage rational inclusions. -/
local instance originalStageNaturalFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[ℚ] F.val)
  (hi : ∀ x : P, (i x : Ω) = (x.val : Ω))

include hi in
/-- The original class transition through the actual embedded scalar
stage has exactly the original finite-stage colimit value. -/
theorem arithmeticOriginalStageClassToColimit_transition :
    letI : Algebra P F.val := i.toAlgebra
    letI : Module P F.val := i.toAlgebra.toModule
    letI : SMul P F.val := i.toAlgebra.toSMul
    letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
    ∀ x : arithmeticClassesModOutsideStageRep ℚ Ω a ha P,
      (arithmeticOriginalStageClassToColimit Ω a ha F).hom
        ((originalRationalExceptionalClassTransition P F.val a ha).hom x) =
        (coefficientRepresentationColimitOf _
          (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) P).hom x := by
  letI : Algebra P F.val := i.toAlgebra
  letI : Module P F.val := i.toAlgebra.toModule
  letI : SMul P F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
  let M := originalUnramifiedStageInUnion a F
  let e := originalUnramifiedStageInUnionEquiv a F
  letI : Algebra F.val M := e.toAlgHom.toAlgebra
  letI : Module F.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul F.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ F.val M := IsScalarTower.of_algHom e.toAlgHom
  have hPM : P ≤ M := originalUnramifiedStageInUnion_contains_embedded a P F i hi
  letI : Algebra P M := (IntermediateField.inclusion hPM).toAlgebra
  letI : Module P M := (IntermediateField.inclusion hPM).toAlgebra.toModule
  letI : SMul P M := (IntermediateField.inclusion hPM).toAlgebra.toSMul
  letI : IsScalarTower ℚ P M := IsScalarTower.of_algHom (IntermediateField.inclusion hPM)
  letI : IsScalarTower P F.val M := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (hi x).symm)
  intro x
  rw [arithmeticOriginalStageClassToColimit_apply]
  change (coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) M).hom
      ((originalRationalExceptionalClassTransition F.val M a ha).hom
        ((originalRationalExceptionalClassTransition P F.val a ha).hom x)) = _
  rw [originalRationalExceptionalClassTransition_tower P F.val M]
  exact Module.DirectLimit.of_f (R := ℤ)
    (G := fun N => arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha N)
    (f := fun E N h => (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha E N h).hom.toLinearMap)
    (hij := hPM) (x := x)

end
end Dubon2026
