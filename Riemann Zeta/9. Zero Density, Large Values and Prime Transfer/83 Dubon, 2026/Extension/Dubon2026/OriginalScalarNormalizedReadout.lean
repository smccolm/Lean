import Dubon2026.OriginalScalarRealizedNormalization
import Dubon2026.OriginalScalarFixedClassRealization
import Dubon2026.OriginalInfiniteKernelInvariantChoice

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup
variable (a : 𝓞 ℚ)

/-- Retain the original finite stage's displayed rational algebra. -/
local instance scalarNormalizedReadoutFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Preserve the displayed rational algebra on the fixed-field image. -/
local instance scalarNormalizedReadoutIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Choose the proved canonical invariant of the exact realized Sylow
fixed-field extension. This choice retains its original idele-total formula. -/
def originalScalarRealizedClassInvariant
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) :
    originalScalarFixedFieldRealizedClassH2 (AlgebraicClosure ℚ) a L
      (S : Subgroup Gal(L.val/ℚ)) →+ AddCircle (1 : ℚ) :=
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let M := originalUnramifiedStageInUnion a L
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  originalInfiniteKernelClassInvariant F M
    (originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)))
    (originalScalarSylowRealization_infinite_kernel_class_system a L p hpa S)

/-- The chosen normalized invariant detects the actual realized class. -/
theorem originalScalarRealizedClassInvariant_injective
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) :
    Function.Injective (originalScalarRealizedClassInvariant a L p hpa S) :=
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let M := originalUnramifiedStageInUnion a L
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  originalInfiniteKernelClassInvariant_injective F M
    (originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)))
    (originalScalarSylowRealization_infinite_kernel_class_system a L p hpa S)

/-- The chosen normalized invariant is the same canonical original-prime
total on every original idele class with zero infinite coordinates. -/
theorem originalScalarRealizedClassInvariant_total
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) :
    let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    let M := originalUnramifiedStageInUnion a L
    let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
    letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
    letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
    ∀ v : groupCohomology (originalFullIdeleRep F M) 2,
      (∀ w : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 F M w v = 0) →
      originalScalarRealizedClassInvariant a L p hpa S
        ((groupCohomology.functor ℤ Gal(M/F) 2).map (originalFullClassRepHom F M) v) =
      originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)) v :=
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let M := originalUnramifiedStageInUnion a L
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  originalInfiniteKernelClassInvariant_total F M
    (originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)))
    (originalScalarSylowRealization_infinite_kernel_class_system a L p hpa S)

end
end Dubon2026
