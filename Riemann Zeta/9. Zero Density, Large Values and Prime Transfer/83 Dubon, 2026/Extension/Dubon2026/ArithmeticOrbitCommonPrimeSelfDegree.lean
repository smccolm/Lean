import Dubon2026.ArithmeticOrbitCommonPrimeDegreeCard

/-! # The local base degree for vertical arithmetic inflation

When the finite base field is unchanged, its original decomposition group
is trivial. The proved completion-degree formula therefore gives local
degree one. This removes the degree factor in DUB-17's same-base canonical
idele-total comparison, without identifying completions by an assumed map.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The actual common-representative completion degree is one when the arithmetic base is unchanged. -/
theorem rationalArithmeticOrbitCommonPrimeDegree_self
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    (σ : rationalArithmeticGaloisGroup a) :
    rationalArithmeticOrbitCommonPrimeDegree a p hp F F le_rfl σ = 1 := by
  have hA : (IntermediateField.inclusion (le_refl F)).toAlgebra = Algebra.id F := by
    ext x
    rfl
  have h := rationalArithmeticOrbitCommonPrimeDegree_eq_decomposition_card
    (hGal := by rw [hA]; infer_instance) a p hp F F le_rfl σ
  rw [hA] at h
  exact h.trans Nat.card_unique

end
end Dubon2026
