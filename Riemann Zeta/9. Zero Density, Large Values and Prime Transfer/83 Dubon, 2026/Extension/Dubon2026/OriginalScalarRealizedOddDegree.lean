import Dubon2026.OriginalScalarRealizedNormalization

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
local instance scalarRealizedOddDegreeFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Preserve the displayed rational algebra on the fixed-field image. -/
local instance scalarRealizedOddDegreeIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- The same actual realized Sylow extension has odd degree for an
odd coefficient prime, including the degree-one case. -/
theorem originalScalarSylowRealization_odd_degree
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(L.val/ℚ)) (hp2 : p ≠ 2) :
    let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    let M := originalUnramifiedStageInUnion a L
    let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
    letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
    letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
    letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
    Odd (Module.finrank F M) := by
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  let M := originalUnramifiedStageInUnion a L
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L (S : Subgroup Gal(L.val/ℚ))
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  obtain ⟨t, ht⟩ := originalScalarSylowRealization_exists_prime_power_degree
    (AlgebraicClosure ℚ) a L p S
  exact (congrArg Odd ht).mpr ((Fact.out : p.Prime).odd_of_ne_two hp2).pow

end
end Dubon2026
