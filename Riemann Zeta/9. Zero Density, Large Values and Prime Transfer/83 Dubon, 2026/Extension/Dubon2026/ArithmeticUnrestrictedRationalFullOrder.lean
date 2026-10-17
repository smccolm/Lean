import Dubon2026.ArithmeticMixedDegreeFullOrderClass
import Dubon2026.OriginalDegreeOneClassReindex

/-! # The unrestricted full-order class over the original rational base

The arithmetic bottom field is genuinely isomorphic to the rationals. The
proved original class-cohomology reindexing returns the constructed mixed-degree
class to the rational base with the same upper field and coefficient group.
This is the base comparison required for DUB-17's actual enlarged stage.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Every original finite Galois field in the unrestricted union has a
constructed full-order class over the actual rational base. -/
theorem rationalArithmeticUnrestricted_rational_exists_full_order_class
    (H : IntermediateField ℚ (rationalUnramifiedExtension 0))
    [FiniteDimensional ℚ H] [IsGalois ℚ H] :
    ∃ x : groupCohomology (originalIdeleClassRep ℚ H) 2,
      addOrderOf x = Module.finrank ℚ H := by
  let F : IntermediateField ℚ (rationalUnramifiedExtension 0) := ⊥
  have hFH : F ≤ H := bot_le
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  have hd : Module.finrank ℚ F = 1 := IntermediateField.finrank_bot
  have hs : Function.Surjective (algebraMap ℚ F) :=
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := ℚ) (E := F)).mp hd).2
  obtain ⟨u, hu⟩ := rationalArithmeticUnrestricted_exists_full_order_class F H hFH
  let e := (originalSurjectiveBaseClassCohomologyIso ℚ F H hs 2).toLinearEquiv
  letI : Module.Free ℚ F := Module.Free.of_divisionRing ℚ F
  letI : Module.Free F H := Module.Free.of_divisionRing F H
  have ht := Module.finrank_mul_finrank ℚ F H
  rw [hd, one_mul] at ht
  exact ⟨e.symm u, (e.symm.toAddEquiv.addOrderOf_eq u).trans (hu.trans ht)⟩

end
end Dubon2026
