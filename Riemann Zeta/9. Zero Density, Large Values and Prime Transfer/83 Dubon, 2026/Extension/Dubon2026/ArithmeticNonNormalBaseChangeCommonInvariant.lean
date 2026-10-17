import Dubon2026.ArithmeticRelativeStageIdeleBaseChange
import Dubon2026.ArithmeticOrbitCommonRepresentativeTowers
import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.ArithmeticOrbitCommonPrimeDegree
import Dubon2026.OriginalFullIdeleInvariantNonNormalBaseChange

/-! # The actual local coordinate under nonnormal fixed-field restriction

This is the coordinate identity required to compare the source's rational
local pairing sum with the normalized total over its Sylow fixed field.
The same finite Galois upper stage derives completion finiteness; normality
of the lower fixed field is not assumed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra

attribute [local instance] arithmeticRelativeStageIdeleAddCommGroup
  originalCompletionCarryFinite originalCompletionCarryGalois

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]
  (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a)

/-- The original normalized invariant of the actual arithmetic base-changed idele class scales by the genuine local base degree; all prime and scalar-tower premises are derived. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_commonInvariant_in_galois_overfield
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL) :
    rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp E M hEM σ
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) =
      rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ •
        rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x := by
  letI : NumberField K := NumberField.of_module_finite ℚ K
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField L := NumberField.of_module_finite ℚ L
  letI : NumberField M := NumberField.of_module_finite ℚ M
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  letI : Module K L := Algebra.toModule
  letI : SMul K L := ((IntermediateField.inclusion hKL).toAlgebra).toSMul
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algHom (IntermediateField.inclusion hKL)
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (IntermediateField.inclusion (hKE.trans hEM))
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  letI : Module L M := Algebra.toModule
  letI : SMul L M := ((IntermediateField.inclusion hLM).toAlgebra).toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois K L := hGalKL
  letI : IsGalois K M := hGalKM
  letI : IsGalois E M := hGalEM
  letI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  letI : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  letI : FiniteDimensional E M := FiniteDimensional.right ℚ E M
  exact @originalFullIdeleCompletionInvariant_baseChange_in_galois_overfield K E L M
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p hp L (QuotientGroup.mk σ)) (rationalArithmeticOrbitPrime a p hp M (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ)
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K L hKL σ)
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K M (hKE.trans hEM) σ)
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp E M hEM σ)
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp L M hLM σ)
    (rationalPrimeLocalClosure p hp) inferInstance
    (arithmeticOrbitCompletionClosureAlgebra a p hp K (QuotientGroup.mk σ))
    (arithmeticOrbitCompletionClosureAlgebra a p hp E (QuotientGroup.mk σ))
    (arithmeticOrbitCompletionClosureAlgebra a p hp L (QuotientGroup.mk σ))
    (arithmeticOrbitCompletionClosureAlgebra a p hp M (QuotientGroup.mk σ))
    (rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp K E hKE σ)
    (rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp K L hKL σ)
    (rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp K M (hKE.trans hEM) σ)
    (rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp E M hEM σ)
    (rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp L M hLM σ)
    (arithmeticOrbitCompletionSourceGalois a p hp K (QuotientGroup.mk σ))
    inferInstance ⊥ (@DiscreteTopology.mk _ ⊥ rfl) ⊥ (@DiscreteTopology.mk _ ⊥ rfl) x


end
end Dubon2026
