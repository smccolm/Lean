import Dubon2026.ArithmeticGlobalSourceStages
import Dubon2026.CoefficientRepresentationColimit

/-! # Continuous arithmetic Galois actions on the original source colimits

The fixed-support ES, JS and CS coefficient colimits carry their original
arithmetic Galois actions. Continuity follows from actual finite Galois
restriction, with discrete coefficients. These are the coefficient actions
needed for the DUB-17 source arithmetic duality sequence.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual arithmetic action on the original S-unit coefficient colimit. -/
abbrev arithmeticSUnitCoefficientColimitRep :=
  coefficientRepresentationColimit (arithmeticGlobalSUnitStageRep K Ω a ha)
    (arithmeticGlobalSUnitStageTransition K Ω a ha)

/-- The actual arithmetic action on the original S-place idele coefficient colimit. -/
abbrev arithmeticSPlaceColimitRep :=
  coefficientRepresentationColimit (arithmeticGlobalSPlaceStageRep K Ω a ha)
    (arithmeticGlobalSPlaceStageTransition K Ω a ha)

/-- The actual arithmetic action on the original S-place class coefficient colimit. -/
abbrev arithmeticSPlaceClassColimitRep :=
  coefficientRepresentationColimit (arithmeticGlobalSPlaceClassStageRep K Ω a ha)
    (arithmeticGlobalSPlaceClassStageTransition K Ω a ha)

omit [NumberField K]
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
private theorem restricted_finiteStage_continuous
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (A : Rep ℤ Gal(F/K)) [TopologicalSpace A] [DiscreteTopology A] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A =>
      (restrictedCoefficientRep A (AlgEquiv.restrictNormalHom F :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))).ρ z.1 z.2) :=
  restrictedCoefficientAction_continuous A _
    (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) continuous_of_discreteTopology

/-- The genuine arithmetic action on the discrete original S-unit colimit is jointly continuous. -/
theorem arithmeticSUnitCoefficientColimitAction_continuous
    [TopologicalSpace (arithmeticSUnitCoefficientColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticSUnitCoefficientColimitRep K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSUnitCoefficientColimitRep K Ω a ha =>
      (arithmeticSUnitCoefficientColimitRep K Ω a ha).ρ z.1 z.2) := by
  letI : ∀ F, TopologicalSpace (arithmeticGlobalSUnitStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalSUnitStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  exact coefficientRepresentationColimit_continuous _ _
    (fun F => restricted_finiteStage_continuous K Ω a F (arithmeticSUnitFiniteStageRep K Ω a ha F))

/-- The genuine arithmetic action on the discrete original S-place idele colimit is jointly continuous. -/
theorem arithmeticSPlaceColimitAction_continuous
    [TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSPlaceColimitRep K Ω a ha =>
      (arithmeticSPlaceColimitRep K Ω a ha).ρ z.1 z.2) := by
  letI : ∀ F, TopologicalSpace (arithmeticGlobalSPlaceStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalSPlaceStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  exact coefficientRepresentationColimit_continuous _ _
    (fun F => restricted_finiteStage_continuous K Ω a F (ArithmeticSPlaceFiniteStageRep K Ω a ha F))

/-- The genuine arithmetic action on the discrete original S-place class colimit is jointly continuous. -/
theorem arithmeticSPlaceClassColimitAction_continuous
    [TopologicalSpace (arithmeticSPlaceClassColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticSPlaceClassColimitRep K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSPlaceClassColimitRep K Ω a ha =>
      (arithmeticSPlaceClassColimitRep K Ω a ha).ρ z.1 z.2) := by
  letI : ∀ F, TopologicalSpace (arithmeticGlobalSPlaceClassStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalSPlaceClassStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  exact coefficientRepresentationColimit_continuous _ _
    (fun F => restricted_finiteStage_continuous K Ω a F (ArithmeticSPlaceClassFiniteStageRep K Ω a ha F))

end
end Dubon2026
