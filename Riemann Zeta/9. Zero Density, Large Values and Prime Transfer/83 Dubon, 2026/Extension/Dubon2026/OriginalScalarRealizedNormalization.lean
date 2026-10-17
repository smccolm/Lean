import Dubon2026.OriginalScalarRealizedTotal

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
local instance scalarRealizedNormalizationFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Preserve the displayed rational algebra on the fixed-field image. -/
local instance scalarRealizedNormalizationIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- The actual realized Sylow fixed-field extension has the proved
canonical class invariant system on its zero-infinite part. The prime-power
degree, field realization and Galois hypotheses are derived from the same
original scalar stage; no normalization certificate is supplied. -/
theorem originalScalarSylowRealization_infinite_kernel_class_system
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a) (S : Sylow p Gal(L.val/ℚ)) :
    let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    let M := originalUnramifiedStageInUnion a L
    let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
    letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
    letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
    OriginalInfiniteKernelClassInvariantSystem F M
      (originalScalarRealizedIdeleTotal a L (S : Subgroup Gal(L.val/ℚ))) := by
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
  obtain ⟨t, ht⟩ := originalScalarSylowRealization_exists_prime_power_degree
    (AlgebraicClosure ℚ) a L p S
  exact rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system
    a F M hFM p t (Fact.out : p.Prime) hpa ht

end
end Dubon2026
