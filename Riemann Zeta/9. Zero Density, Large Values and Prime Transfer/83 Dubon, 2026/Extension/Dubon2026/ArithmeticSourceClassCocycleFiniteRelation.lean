import Dubon2026.ArithmeticClassCocycleFiniteRelation
import Dubon2026.ArithmeticSourceClassHomComparison

/-! # Actual source-class cocycles reach the finite relation criterion

Apply the literal original source-to-full-class comparison to the given
source Hom cocycle, then consume the constructed free-cover lift and
finite relation descent. This closes the source-entry and representative
obligations on this part of DUB-17's reverse-localization chain. It does
not yet identify the finite scalar obstruction with local cup pairings.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Use the original arithmetic union inclusion. -/
local instance sourceFiniteRelationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Use the actual finite stage inclusion. -/
local instance sourceFiniteRelationStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

/-- The original source-class Hom at the actual finite coefficient stage. -/
abbrev arithmeticFiniteCoefficientSourceClassHom :=
  arithmeticSourceClassHomRep ℚ Ω a ha (Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ)) B)

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]

/-- Integer scalar multiplication on the original discrete Hom is continuous. -/
local instance sourceFiniteRelationHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
      (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual original source-class Hom cocycle yields a finite-Galois
relation representative through the literal source-class comparison. -/
theorem arithmeticSourceClassHomCocycle_exists_finite_relation_representative
    [Finite B]
    (c : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
    ∃ v : arithmeticRelationFreeClassHom Ω a ha P B, ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[ℤ] C from v).comp X.f.hom.toLinearMap ∧
      (∀ g, (arithmeticRelationFreeClassHom Ω a ha P B).ρ g v - v =
        (originalInternalHomPrecomposition C X.g).hom
          ((arithmeticSourceClassHomComparison ℚ Ω a ha (Rep.res π B)).hom (c.val g))) ∧
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
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let T := arithmeticFiniteCoefficientClassHom Ω a ha P B
  letI : TopologicalSpace T := ⊥
  letI : DiscreteTopology T := ⟨rfl⟩
  letI : @ContinuousSMul ℤ T T.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ T T.hV2.toSMul _ _ continuous_of_discreteTopology
  let f : arithmeticFiniteCoefficientSourceClassHom Ω a ha P B ⟶ T :=
    arithmeticSourceClassHomComparison ℚ Ω a ha (Rep.res π B)
  let d := continuousCoefficientCocycleOneMap
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B) T f.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply f) c
  exact arithmeticClassHomCocycle_exists_finite_relation_representative Ω a ha P B d

end
end Dubon2026
