import Dubon2026.ArithmeticSUnitFiniteStageInclusion
import Dubon2026.ArithmeticSUnitTwoCocycleFiniteDescent
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Actual finite-stage inflation for continuous arithmetic S-unit H2

The source finite S-unit action and original coefficient inclusion define
inflation on the existing continuous cohomology quotient. Exact cocycle
descent then supplies a finite-stage representative for every original class.
Injectivity of the filtered colimit requires separate coboundary descent.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

section Global
variable [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

local instance : @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
    (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Continuous H2 of the actual arithmetic S-unit coefficient. -/
abbrev ArithmeticSUnitContinuousH2 :=
  ContinuousRepresentationH2 (originalArithmeticSUnitRepresentation K Ω a ha)
    (originalArithmeticSUnitAction_continuous K Ω a ha)

end Global

variable (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

section Finite
variable [TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F)]
  [DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F)]

local instance : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitFiniteStageRep K Ω a ha F).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The actual finite Galois S-unit action is continuous with its discrete coefficient topology. -/
theorem arithmeticSUnitFiniteStageAction_continuous :
    Continuous (fun z : Gal(F/K) × arithmeticSUnitFiniteStageRep K Ω a ha F =>
      (arithmeticSUnitFiniteStageRep K Ω a ha F).ρ z.1 z.2) := continuous_of_discreteTopology

/-- Continuous H2 of the original finite-stage S-unit coefficient. -/
abbrev ArithmeticSUnitFiniteStageH2 :=
  ContinuousRepresentationH2 (arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitFiniteStageAction_continuous K Ω a ha F)

variable [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

local instance : @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
    (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Actual Galois restriction followed by the original S-unit inclusion gives continuous finite-stage H2 inflation. -/
def arithmeticSUnitFiniteStageH2Inflation :
    ArithmeticSUnitFiniteStageH2 K Ω a ha F →ₗ[ℤ] ArithmeticSUnitContinuousH2 K Ω a ha := by
  let j : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom F
  have hj : Continuous j := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  let φ := (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom.toLinearMap
  let hF := arithmeticSUnitFiniteStageAction_continuous K Ω a ha F
  let hΓ := originalArithmeticSUnitAction_continuous K Ω a ha
  exact (continuousCoefficientH2Map
    (restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha F) j)
    (originalArithmeticSUnitRepresentation K Ω a ha) φ continuous_of_discreteTopology
    (Rep.hom_comm_apply (arithmeticSUnitFiniteStageInclusion K Ω a ha F))
    (restrictedCoefficientAction_continuous (arithmeticSUnitFiniteStageRep K Ω a ha F) j hj hF)
    hΓ).comp (continuousRepresentationH2Restriction (arithmeticSUnitFiniteStageRep K Ω a ha F) hF j hj)

/-- Finite-stage inflation retains actual restriction in both variables and the literal original S-unit inclusion. -/
theorem arithmeticSUnitFiniteStageH2Inflation_mk
    (c : continuousRepresentationCocyclesTwo (arithmeticSUnitFiniteStageRep K Ω a ha F)) :
    arithmeticSUnitFiniteStageH2Inflation K Ω a ha F (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha F)
          (AlgEquiv.restrictNormalHom F :
            Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)))
        (originalArithmeticSUnitRepresentation K Ω a ha)
        (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply (arithmeticSUnitFiniteStageInclusion K Ω a ha F))
        (continuousRepresentationCocycleTwoRestriction (arithmeticSUnitFiniteStageRep K Ω a ha F)
          (AlgEquiv.restrictNormalHom F :
            Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))
          (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) c)) := rfl

end Finite

variable [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

local instance arithmeticSUnitContinuousSMul :
    @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
      (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

private theorem cocycle_finiteStage_preimage
    (c : continuousRepresentationCocyclesTwo (originalArithmeticSUnitRepresentation K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
      letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
      ∃ y : ArithmeticSUnitFiniteStageH2 K Ω a ha F,
        arithmeticSUnitFiniteStageH2Inflation K Ω a ha F y = Submodule.Quotient.mk c := by
  have hstage := originalArithmeticSUnitTwoCocycle_exists_finiteField K Ω a ha c
  let F := hstage.choose
  have hvalues := hstage.choose_spec.1
  have hperiod := hstage.choose_spec.2
  letI : NumberField F := NumberField.of_module_finite K F
  have hdescent :=
    originalArithmeticSUnitTwoCocycle_exists_finite_descent K Ω a ha F c.val hvalues hperiod
  let f := hdescent.choose
  have hf := hdescent.choose_spec.1
  have hfactor := hdescent.choose_spec.2
  letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
  letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha F)
      (arithmeticSUnitFiniteStageRep K Ω a ha F).hV2.toSMul inferInstance inferInstance :=
    ⟨continuous_of_discreteTopology⟩
  letI := numberFieldSUnitGaloisAction K F (arithmeticSUnitFiniteStageSupport K Ω a ha F)
    (originalExceptionalIntegerSupport_galoisStable F K a ha)
  let cF : continuousRepresentationCocyclesTwo (arithmeticSUnitFiniteStageRep K Ω a ha F) :=
    ⟨groupCohomology.cocyclesOfIsMulCocycle₂ hf, continuous_of_discreteTopology⟩
  refine ⟨F, Submodule.Quotient.mk cF, ?_⟩
  rw [arithmeticSUnitFiniteStageH2Inflation_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext z
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F
    (f (AlgEquiv.restrictNormalHom F z.1, AlgEquiv.restrictNormalHom F z.2))).trans
      (congrArg Units.val (hfactor z.1 z.2))


/-- Every actual continuous arithmetic S-unit H2 class is the literal inflation of a constructed finite Galois S-unit class. -/
theorem arithmeticSUnitContinuousH2_exists_finiteStage
    (x : ArithmeticSUnitContinuousH2 K Ω a ha) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
      letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
      ∃ y : ArithmeticSUnitFiniteStageH2 K Ω a ha F,
        arithmeticSUnitFiniteStageH2Inflation K Ω a ha F y = x := by
  induction x using Submodule.Quotient.induction_on with
  | H c => exact cocycle_finiteStage_preimage K Ω a ha c

end
end Dubon2026
