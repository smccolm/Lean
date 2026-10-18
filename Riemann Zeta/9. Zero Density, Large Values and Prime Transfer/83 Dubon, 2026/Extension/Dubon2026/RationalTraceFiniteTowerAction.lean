import Dubon2026.FiniteCoefficientGaloisTowerDescent
import Dubon2026.RationalTraceOriginalLocalAction

/-! The literal descended trace action at a larger original arithmetic field
is the restriction of the action at the original coefficient field. This
feeds DUB-17's constructed relation-extension stage without assuming a
coefficient identification. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F N : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hFN : F.toIntermediateField ≤ N.toIntermediateField)
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)

/-- The actual trace representation at the larger stage is precisely
the original finite action restricted along the literal Galois map. -/
theorem rationalTraceOriginalFiniteRepresentation_restrict :
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : Module F N := Algebra.toModule
    letI : SMul F N := Algebra.toSMul
    letI : IsScalarTower ℚ F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
    (rationalTraceOriginalFiniteRep a q σ N
      (finiteStageCoefficientKernel_mono (rationalArithmeticTraceZeroIntegerRep a q σ)
        F N hFN hker)).ρ =
      (rationalTraceOriginalFiniteRep a q σ F hker).ρ.comp
        (AlgEquiv.restrictNormalHom F : Gal(N/ℚ) →* Gal(F/ℚ)) := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Module F N := Algebra.toModule
  letI : SMul F N := Algebra.toSMul
  letI : IsScalarTower ℚ F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  apply MonoidHom.ext
  intro u
  apply LinearMap.ext
  intro x
  exact finiteStageCoefficientRepresentation_restrict
    (rationalArithmeticTraceZeroIntegerRep a q σ) F N hFN hker u x

end
end Dubon2026
