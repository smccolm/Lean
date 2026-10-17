import Dubon2026.ArithmeticSourceIdeleFiniteClassValues
import Dubon2026.ArithmeticSourceIdeleGlobalDescent

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceIdeleClassDescentUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance sourceIdeleClassDescentFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance sourceIdeleClassDescentIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleClassDescentLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The constructed finite source-idele cocycle retains both its original
values and their images under the exact class-colimit comparison used by
the scalar relation. This gives the finite representative needed to compare
the two obstruction images at a common enlarged stage. -/
theorem arithmeticSourceIdeleTwoCocycle_exists_finite_class_values
    (c : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha F),
        (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
          (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
            (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) F).hom
              (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) = c.val (g, h)) ∧
        (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
          (coefficientRepresentationColimitOf (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
            (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F).hom
              ((arithmeticSourceClassStageComparison ℚ Ω a ha F).hom
                ((arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha F).hom
                  (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)))) =
          (arithmeticSourceIdeleToFullClassColimit Ω a ha).hom (c.val (g, h))) := by
  obtain ⟨F, d, hd⟩ := arithmeticSourceIdeleContinuousTwoCocycle_exists_finite_descent ℚ Ω a ha c
  refine ⟨F, d, hd, ?_⟩
  intro g h
  exact (arithmeticSourceIdeleToFullClassColimit_of Ω a ha F
    (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h))).symm.trans
      (congrArg (arithmeticSourceIdeleToFullClassColimit Ω a ha).hom (hd g h))

end
end Dubon2026
