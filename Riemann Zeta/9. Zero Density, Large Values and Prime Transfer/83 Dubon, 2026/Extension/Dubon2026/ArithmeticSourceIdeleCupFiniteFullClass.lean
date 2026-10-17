import Dubon2026.ArithmeticSourceIdeleFiniteScalarClass
import Dubon2026.ArithmeticFiniteSourceScalarAnnihilator
import Dubon2026.OriginalRelationObstructionSylowDetection

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [omegaField : Field Ω] [omegaAlgebra : Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceIdeleFullScalarConsumerComparisonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceIdeleFullScalarConsumerComparisonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω a ha)] [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω a ha)]
  [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)] [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupFiniteFullClassLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω a ha) (arithmeticSPlaceColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupFiniteFullClassLocalInstance2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupFiniteFullClassLocalInstance3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)]
/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleCupFiniteFullClassLocalInstance4 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology



/-- Retain the original rational inclusion on underlying arithmetic fields. -/
local instance sourceIdeleFullScalarConsumerIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'


/-- The constructed finite arithmetic field is a number field. -/
local instance sourceFullScalarConsumerNumberField
    (M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) : NumberField M :=
  NumberField.of_module_finite ℚ M

/-- The actual source cup constructs a finite full-idele class whose
full-class image is killed by the coefficient prime and vanishes exactly
with the original scalar obstruction. All comparison witnesses and the
common finite field are constructed; no lifting or equality premise is supplied. -/
theorem arithmeticSourceIdeleCup_exists_finite_full_scalar_class [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)) (p : ℕ) (hB : ∀ b : B, p • b = 0) :
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
            ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
              ∃ hEM : E ≤ M,
                let cM := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
                  (arithmeticSourceIdeleFiniteFullH2Transition Ω a ha E M hEM d)
                originalUnramifiedStageInUnion a L ≤ M ∧ p • cM = 0 ∧
                  (cM = 0 ↔ (originalRelationExtensionObstruction
                    (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)
                    (arithmeticOriginalStageClassRep Ω a ha L)
                    (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL)).hom
                      (arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL y) = 0) := by
  intro c r F i L hFL hi y
  have hcomparison := arithmeticSourceIdeleCup_exists_common_finite_scalar_class Ω a ha P B z r F i L hFL hi y
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
  refine hs.2.elim ?_
  intro M hM
  refine hM.elim ?_
  intro hEM hrest
  refine hrest.elim ?_
  intro hLM hcmp
  have hpScalar := originalRelationExtensionObstruction_nsmul_zero
    (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)
    (arithmeticOriginalStageClassRep Ω a ha L) p hB
    (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL)
    (arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL y)
  have hps : p • groupCohomology.H2π _ s = 0 :=
    (congrArg (fun v => p • v) hs.1).trans hpScalar
  have hpFull := arithmeticSourceIdeleFiniteFullClass_nsmul_zero Ω a ha E M hEM L hLM d s hcmp p hps
  have hzero := arithmeticSourceIdeleFiniteFullClass_zero_iff_scalar Ω a ha E M hEM L hLM d s hcmp
  refine ⟨M, hEM, hLM, hpFull, ?_⟩
  constructor
  · intro hz
    exact hs.1.symm.trans (hzero.mp hz)
  · intro hz
    exact hzero.mpr (hs.1.trans hz)

/-- Construct the source relation as well as the finite full-idele class,
its prime annihilator and its exact scalar-obstruction zero test. -/
theorem arithmeticSourceIdeleCocycle_exists_finite_full_scalar_class [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω a ha P B)) (p : ℕ) (hB : ∀ b : B, p • b = 0) :
    let c := arithmeticSourceIdeleCocycleQuotient Ω a ha P B z
    ∃ r : ArithmeticSourceClassRelationData Ω a ha P B c,
    ∀ (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : r.stage →ₐ[ℚ] F.val)
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
            ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
              ∃ hEM : E ≤ M,
                let cM := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
                  (arithmeticSourceIdeleFiniteFullH2Transition Ω a ha E M hEM d)
                originalUnramifiedStageInUnion a L ≤ M ∧ p • cM = 0 ∧
                  (cM = 0 ↔ (originalRelationExtensionObstruction
                    (arithmeticSourceScalarStageCoefficient Ω a ha P B c r F i L hFL)
                    (arithmeticOriginalStageClassRep Ω a ha L)
                    (arithmeticSourceScalarStageRelationTransport Ω a ha P B c r F i L hFL)).hom
                      (arithmeticSourceScalarStageH1ToAlgebraic Ω a ha P B c r F i L hFL y) = 0) := by
  intro c
  obtain ⟨r⟩ := arithmeticSourceClassRelationData_nonempty Ω a ha P B c
  refine ⟨r, ?_⟩
  exact arithmeticSourceIdeleCup_exists_finite_full_scalar_class Ω a ha P B z p hB r

end
end Dubon2026
