import Dubon2026.ArithmeticClassCocycleRelationRepresentative
import Dubon2026.ArithmeticRelationClassGaloisDescent

/-! # The original degree-one class cocycle reaches the finite relation module

Compose the actual free-cover coboundary construction with finite lattice
descent. The output retains both the original continuous cocycle and the
literal finite-stage relation values. This is the required entry into
DUB-17's finite scalar relation criterion; local pairing remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance finiteClassRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance finiteClassRelationStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance finiteClassRelationHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- An actual continuous class Hom cocycle has a finite-Galois relation
representative preserving its original free-cover lift and class values. -/
theorem arithmeticClassHomCocycle_exists_finite_relation_representative
    [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      (∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom (c.val g)) ∧
      ∃ N : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          letI : Module P N := Algebra.toModule
          letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
          letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
          let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
          ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha N,
            ∀ r, (coefficientRepresentationColimitOf _
              (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) N).hom (η.hom r) =
                φ.hom ((originalRelationGroupChange τ B).hom r) := by
  obtain ⟨v, φ, hφ, hv⟩ := arithmeticClassHomCocycle_exists_relation_representative Ω a ha P B c
  exact ⟨v, φ, hφ, hv,
    arithmeticRelationClassHom_exists_finite_relation_descent ℚ Ω a ha P B φ⟩

end
end Dubon2026
