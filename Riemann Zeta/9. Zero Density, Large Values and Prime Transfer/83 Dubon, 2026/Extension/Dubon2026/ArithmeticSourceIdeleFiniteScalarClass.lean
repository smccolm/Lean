import Dubon2026.ArithmeticSourceIdeleScalarImage
import Dubon2026.ArithmeticSourceIdeleContinuousFiniteRepresentative
import Dubon2026.ArithmeticClassStageCommonEquality
import Dubon2026.ArithmeticSourceScalarFiniteAlgebraicObstruction
import Dubon2026.ArithmeticSourceIdeleFiniteClassWitness

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleFiniteScalarComparisonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleFiniteScalarComparisonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteScalarClassLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteScalarClassLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteScalarClassLocalInstance3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleFiniteScalarClassLocalInstance4 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology



/-- Retain the original rational inclusion on underlying arithmetic fields. -/
local instance sourceIdeleFiniteScalarIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'


/-- The actual source-idele cup has a finite original idele representative
whose class agrees, at a constructed common arithmetic field, with a
representative of the exact scalar-stage algebraic obstruction. Every field,
cocycle, and comparison witness is constructed from the original inputs. -/
theorem arithmeticSourceIdeleCup_exists_common_finite_scalar_class [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)) :
    let c := arithmeticSourceIdeleCocycleQuotient Ω a ha P B z
    ∀ (r : ArithmeticSourceClassRelationData Ω a ha P B c)
      (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
      (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
      (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
      (hi : ∀ x : r.stage, (i x : Ω) = (x.val : Ω))
      (y : arithmeticSourceScalarStageContinuousH1 Ω a ha P B c r F i L hFL),
      ∃ w : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω a ha),
        (Submodule.Quotient.mk w : arithmeticSourceIdeleContinuousH2 Ω a ha) =
          arithmeticSourceIdeleContinuousCupClass Ω a ha P B z
            (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y) ∧
        ∃ E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
          ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E),
            (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
              (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω a ha)
                (arithmeticGlobalSPlaceStageTransition ℚ Ω a ha) E).hom
                  (d (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) = w.val (g, h)) ∧
            ∃ s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L),
              groupCohomology.H2π _ s =
                (originalRelationExtensionObstruction
                  (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)
                  (arithmeticOriginalStageClassRep Ω a ha L)
                  (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL)).hom
                    (arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL y) ∧
              ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
                ∃ hEM : E ≤ M, ∃ hLM : originalUnramifiedStageInUnion a L ≤ M,
                  groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E M hEM
                    (groupCohomology.mapCocycles₂
                      (A := ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)
                      (B := arithmeticClassesModOutsideStageRep ℚ Ω a ha E)
                      (MonoidHom.id Gal(E/ℚ))
                      (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
                        arithmeticSourceClassStageComparison ℚ Ω a ha E) d)) =
                  groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
                    (originalUnramifiedStageInUnion a L) M hLM
                    (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)) := by
  intro c r F i L hFL hi y
  let cup := arithmeticSourceIdeleContinuousCupClass Ω a ha P B z
    (arithmeticSourceScalarContinuousH1Inflation Ω a ha P B c r F i L hFL hi y)
  let C := arithmeticOriginalStageClassRep Ω a ha L
  letI scalarTopology : TopologicalSpace C := ⊥
  letI scalarDiscrete : DiscreteTopology C := ⟨rfl⟩
  letI : @ContinuousSMul ℤ C C.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ C C.hV2.toSMul _ _ continuous_of_discreteTopology
  let x := arithmeticSourceScalarStageContinuousObstruction Ω a ha P B c r F i L hFL y
  have hux := (arithmeticSourceIdeleCup_scalar_obstruction_image Ω a ha P B z r F i L hFL hi y).trans
    (arithmeticSourceScalarContinuousObstruction_eq_finite_inflation Ω a ha P B c r F i L hFL y)
  have hcomparison := @arithmeticSourceIdeleH2_exists_common_finite_class
    Ω omegaField omegaAlgebra a ha stageDecidableEq sourceTopology sourceDiscrete
      targetTopology targetDiscrete L scalarTopology scalarDiscrete cup x hux
  refine hcomparison.elim ?_
  intro w hw
  refine ⟨w, hw.1, ?_⟩
  refine hw.2.elim ?_
  intro E hE
  refine hE.elim ?_
  intro d hd
  refine ⟨E, d, hd.1, ?_⟩
  refine hd.2.elim ?_
  intro s hs
  refine ⟨s, ?_, hs.2⟩
  exact hs.1.trans (arithmeticSourceScalarStageContinuousObstruction_toAlgebraic Ω a ha P B c r F i L hFL y)

end
end Dubon2026
