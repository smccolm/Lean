import Dubon2026.OriginalScalarNormalizedReadout
import Dubon2026.OriginalInfiniteKernelOddTotal
import Dubon2026.OriginalScalarRealizedOddDegree

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
local instance scalarRealizedOddTotalFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Preserve the displayed rational algebra on the fixed-field image. -/
local instance scalarRealizedOddTotalIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- At the actual odd-prime Sylow realization the canonical class
invariant equals the original idele total on every idele H2 class.
The infinite-coordinate condition follows from the proved odd degree. -/
theorem originalScalarRealizedClassInvariant_total_of_odd
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) (hp2 : p ≠ 2) :
    let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    let M := originalUnramifiedStageInUnion a L
    let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
    letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
    letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
    ∀ v : groupCohomology (originalFullIdeleRep F M) 2,
      originalScalarRealizedClassInvariant a L p hpa S
        ((groupCohomology.functor ℤ Gal(M/F) 2).map (originalFullClassRepHom F M) v) =
      originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)) v := by
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let M := (originalUnramifiedStageInUnion a L).toIntermediateField
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let eK := originalScalarFixedFieldInUnionEquiv (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  letI : FiniteDimensional ℚ F := eK.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional ℚ M := (originalUnramifiedStageInUnion a L).finiteDimensional
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion hFM)
  letI : FiniteDimensional F M := FiniteDimensional.right ℚ F M
  letI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  have hn := originalScalarSylowRealization_odd_degree a L p S hp2
  exact originalInfiniteKernelClassInvariant_total_of_odd F M
    (originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ)))
    (originalScalarSylowRealization_infinite_kernel_class_system a L p hpa S) hn

end
end Dubon2026
