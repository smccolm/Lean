import Dubon2026.ArithmeticSourceIdeleGlobalDescent
import Dubon2026.ArithmeticSourceIdeleCupImage
import Dubon2026.OriginalSPlaceFullClassImage
import Dubon2026.ArithmeticClassesModOutsideStages
import Dubon2026.ArithmeticSourceHomContinuity

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Preserve the original arithmetic union's rational inclusion. -/
local instance sourceIdeleCupDescentUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual rational algebra on the finite Galois field. -/
local instance sourceIdeleCupDescentFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain the same rational algebra on its underlying intermediate field. -/
local instance sourceIdeleCupDescentIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) × A => A.ρ z.1 z.2))
  [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticSourceIdeleHomRep ℚ Ω a ha A)] [DiscreteTopology (arithmeticSourceIdeleHomRep ℚ Ω a ha A)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupDescentConsumerLocalInstance1 : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupDescentConsumerLocalInstance2 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupDescentConsumerLocalInstance3 : @ContinuousSMul ℤ (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceIdeleHomRep ℚ Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSourceIdeleHomRep ℚ Ω a ha A).hV2.toSMul _ _ continuous_of_discreteTopology


/-- The actual continuous source-idele evaluation cup descends to a finite
Galois source cocycle whose class image has the specified full-idele H2
representative. Both the stage and cocycle are constructed from the inputs. -/
theorem arithmeticSourceIdeleCup_exists_finite_full_class_image
    (f : continuousRepresentationCocyclesOne A)
    (y : continuousRepresentationCocyclesOne (arithmeticSourceIdeleHomRep ℚ Ω a ha A)) :
    let cup := continuousOneCocycleCup A (arithmeticSourceIdeleHomRep ℚ Ω a ha A) (arithmeticSPlaceColimitRep ℚ Ω a ha)
      (originalInternalHomEvaluation A (arithmeticSPlaceColimitRep ℚ Ω a ha))
      (originalInternalHomEvaluation_equivariant A (arithmeticSPlaceColimitRep ℚ Ω a ha)) continuous_of_discreteTopology
      (arithmeticSourceIdeleHomAction_continuous ℚ Ω a ha A hA) f y
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha)
      let hS := originalExceptionalIntegerSupport_galoisStable F ℚ a ha
      ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha F),
        (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
          (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
            (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) F).hom
              (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) = cup.val (g, h)) ∧
        (groupCohomology.functor ℤ Gal(F/ℚ) 2).map (arithmeticSourceClassStageComparison ℚ Ω a ha F)
          ((groupCohomology.functor ℤ Gal(F/ℚ) 2).map (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha F)
            (groupCohomology.H2π _ d)) =
        (groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalIdeleClassesModOutsideRepHom ℚ F S hS)
          ((groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalFullClassRepHom ℚ F)
            ((groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalSPlaceFullIdeleInclusion ℚ F S hS)
              (groupCohomology.H2π _ d))) := by
  intro cup
  obtain ⟨F, d, hd⟩ := arithmeticSourceIdeleContinuousTwoCocycle_exists_finite_descent ℚ Ω a ha cup
  letI : NumberField F := NumberField.of_module_finite ℚ F
  refine ⟨F, d, hd, ?_⟩
  exact originalSPlaceFullIdele_H2_class_comparison ℚ F _ _ (groupCohomology.H2π _ d)

end
end Dubon2026
