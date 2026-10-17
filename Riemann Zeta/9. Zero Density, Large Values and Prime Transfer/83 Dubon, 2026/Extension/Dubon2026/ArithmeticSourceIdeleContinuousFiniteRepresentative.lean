import Dubon2026.ArithmeticSourceIdeleClassDescent
import Dubon2026.ArithmeticSourceIdeleContinuousCup
import Dubon2026.ArithmeticClassStageContinuousCocycle

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the actual rational inclusion of the arithmetic union. -/
local instance sourceIdeleContinuousRepresentativeUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Retain the actual rational structure of each finite Galois stage. -/
local instance sourceIdeleContinuousRepresentativeFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Retain its underlying intermediate field's rational structure. -/
local instance sourceIdeleContinuousRepresentativeIntermediateAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable [TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleContinuousFiniteRepresentativeLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha)
    (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleContinuousFiniteRepresentativeLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- The finite source representative constructed from an actual continuous
idele cocycle has precisely its continuous full-class image. The original
idele values are retained along with this equality of continuous H2 classes. -/
theorem arithmeticSourceIdeleContinuousH2_exists_finite_class_representative
    (c : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha F),
        (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
          (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
            (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) F).hom
              (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) = c.val (g, h)) ∧
        arithmeticSourceIdeleContinuousH2ToClasses Ω a ha (Submodule.Quotient.mk c) =
          Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle ℚ Ω a ha F
            (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(F/ℚ))
              (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha F ≫
                arithmeticSourceClassStageComparison ℚ Ω a ha F) d)) := by
  obtain ⟨F, d, hd, hc⟩ := arithmeticSourceIdeleTwoCocycle_exists_finite_class_values Ω a ha c
  refine ⟨F, d, hd, ?_⟩
  apply congrArg (continuousRepresentationCoboundariesTwo
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)).mkQ
  apply Subtype.ext
  apply Subtype.ext
  funext gh
  exact (hc gh.1 gh.2).symm

end
end Dubon2026
