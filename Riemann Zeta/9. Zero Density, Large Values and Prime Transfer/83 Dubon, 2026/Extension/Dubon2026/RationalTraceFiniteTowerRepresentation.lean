import Dubon2026.RationalTraceFiniteTowerAction

/-! Retain the actual bundled trace coefficient at the larger finite field
used by the S-unit correction. This lets its relation morphism feed the
original trace-dual H1 construction on DUB-17's reverse localization chain. -/
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

/-- The actual larger-field trace coefficient is the same bundled
representation as the restriction used by the finite S-unit correction. -/
theorem rationalTraceOriginalFinite_tower_representation :
    letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
    letI : Module F N := Algebra.toModule
    letI : SMul F N := Algebra.toSMul
    letI : IsScalarTower ℚ F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
    rationalTraceOriginalFiniteRep a q σ N
      (finiteStageCoefficientKernel_mono (rationalArithmeticTraceZeroIntegerRep a q σ)
        F N hFN hker) =
      Rep.res (AlgEquiv.restrictNormalHom F : Gal(N/ℚ) →* Gal(F/ℚ))
        (rationalTraceOriginalFiniteRep a q σ F hker) := by
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Module F N := Algebra.toModule
  letI : SMul F N := Algebra.toSMul
  letI : IsScalarTower ℚ F N := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  exact congrArg (fun ρ : Representation ℤ Gal(N/ℚ)
    (rationalArithmeticTraceZeroIntegerRep a q σ) => Rep.of ρ)
      (rationalTraceOriginalFiniteRepresentation_restrict a q σ F N hFN hker)

end
end Dubon2026
