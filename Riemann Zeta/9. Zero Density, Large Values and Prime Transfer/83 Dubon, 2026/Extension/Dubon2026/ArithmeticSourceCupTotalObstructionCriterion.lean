import Dubon2026.ArithmeticSourceIdeleCupFiniteFullClass
import Dubon2026.ArithmeticCommonStagePrimeClassZero

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
local notation "Ω₀" => AlgebraicClosure ℚ
variable (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union's rational inclusion. -/
local instance sourceCupTotalCriterionComparisonUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω₀) a).algebra'

variable [stageDecidableEq : DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a))

/-- Retain the original finite Galois stage's rational inclusion. -/
local instance sourceCupTotalCriterionComparisonFiniteAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable
  [sourceTopology : TopologicalSpace (arithmeticSPlaceColimitRep ℚ Ω₀ a ha)] [sourceDiscrete : DiscreteTopology (arithmeticSPlaceColimitRep ℚ Ω₀ a ha)]
  [targetTopology : TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha)] [targetDiscrete : DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha)]
  [TopologicalSpace (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B)] [DiscreteTopology (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B)]

/-- The continuous action on the original discrete coefficient. -/
local instance sourceCupTotalCriterionContinuous1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep ℚ Ω₀ a ha) (arithmeticSPlaceColimitRep ℚ Ω₀ a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep ℚ Ω₀ a ha) (arithmeticSPlaceColimitRep ℚ Ω₀ a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The continuous action on the original discrete coefficient. -/
local instance sourceCupTotalCriterionContinuous2 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha) (arithmeticClassesModOutsideColimitRep ℚ Ω₀ a ha).hV2.toSMul _ _ continuous_of_discreteTopology
/-- The continuous action on the original discrete coefficient. -/
local instance sourceCupTotalCriterionContinuous3 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B) (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology


variable [TopologicalSpace (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B)]
  [DiscreteTopology (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B)]
/-- The continuous action on the original discrete coefficient. -/
local instance sourceCupTotalCriterionContinuous4 : @ContinuousSMul ℤ (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B)
    (arithmeticFiniteCoefficientSourceClassHom Ω₀ a ha P B).hV2.toSMul _ _ continuous_of_discreteTopology



/-- Retain the original rational inclusion on underlying arithmetic fields. -/
local instance sourceCupTotalCriterionIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'


/-- The constructed finite arithmetic field is a number field. -/
local instance sourceCupTotalCriterionNumberField
    (M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a)) : NumberField M :=
  NumberField.of_module_finite ℚ M

/-- The original source cocycle constructs the finite idele representative
and common field. Zero of its canonical total kills the original scalar
obstruction, with the coefficient annihilator and Sylow detection derived. -/
theorem arithmeticSourceIdeleCocycle_exists_finite_total_obstruction_criterion [Finite B]
    (z : continuousRepresentationCocyclesOne (arithmeticFiniteCoefficientSourceIdeleHom Ω₀ a ha P B)) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a) (hB : ∀ b : B, p • b = 0) :
    let c := arithmeticSourceIdeleCocycleQuotient Ω₀ a ha P B z
    ∃ r : ArithmeticSourceClassRelationData Ω₀ a ha P B c,
    ∀ (F : OriginalUnramifiedGaloisStage (Ω := Ω₀) a) (i : r.stage →ₐ[ℚ] F.val)
      (L : OriginalUnramifiedGaloisStage (Ω := Ω₀) a)
      (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
      (hi : ∀ x : r.stage, (i x : Ω₀) = (x.val : Ω₀))
      (y : arithmeticSourceScalarStageContinuousH1 Ω₀ a ha P B c r F i L hFL),
      ∃ w : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep ℚ Ω₀ a ha),
        (Submodule.Quotient.mk w : arithmeticSourceIdeleContinuousH2 Ω₀ a ha) =
          arithmeticSourceIdeleContinuousCupClass Ω₀ a ha P B z
            (arithmeticSourceScalarContinuousH1Inflation Ω₀ a ha P B c r F i L hFL hi y) ∧
        ∃ E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a),
          ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω₀ a ha E),
            (∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω₀) a / ℚ),
              (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep ℚ Ω₀ a ha)
                (arithmeticGlobalSPlaceStageTransition ℚ Ω₀ a ha) E).hom
                  (d (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) = w.val (g, h)) ∧
            ∃ M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω₀) a),
              ∃ hEM : E ≤ M,
                let uM := arithmeticSourceIdeleFiniteFullH2Transition Ω₀ a ha E M hEM d
                originalUnramifiedStageInUnion a L ≤ M ∧
                  (arithmeticCommonStageRationalIdeleTotal a M uM = 0 → (originalRelationExtensionObstruction
                    (arithmeticSourceScalarStageCoefficient Ω₀ a ha P B c r F i L hFL)
                    (arithmeticOriginalStageClassRep Ω₀ a ha L)
                    (arithmeticSourceScalarStageRelationTransport Ω₀ a ha P B c r F i L hFL)).hom
                      (arithmeticSourceScalarStageH1ToAlgebraic Ω₀ a ha P B c r F i L hFL y) = 0) := by
  intro c
  have hfull := arithmeticSourceIdeleCocycle_exists_finite_full_scalar_class Ω₀ a ha P B z p hB
  refine hfull.elim ?_
  intro r hr
  refine ⟨r, ?_⟩
  intro F i L hFL hi y
  have hrepresentative := hr F i L hFL hi y
  refine hrepresentative.elim ?_
  intro w hw
  refine ⟨w, hw.1, ?_⟩
  refine hw.2.elim ?_
  intro E hE
  refine hE.elim ?_
  intro d hd
  refine ⟨E, d, hd.1, ?_⟩
  refine hd.2.elim ?_
  intro M hM
  refine hM.elim ?_
  intro hEM hm
  refine ⟨M, hEM, hm.1, ?_⟩
  intro htotal
  have hzero := arithmeticCommonStageIdele_class_zero_of_total_zero a M p hp2 hpa
    (arithmeticSourceIdeleFiniteFullH2Transition Ω₀ a ha E M hEM d) hm.2.1 htotal
  exact hm.2.2.mp hzero

end
end Dubon2026
