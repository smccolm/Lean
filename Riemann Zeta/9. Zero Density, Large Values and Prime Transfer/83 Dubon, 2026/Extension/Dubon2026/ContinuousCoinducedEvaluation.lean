import Dubon2026.ContinuousCoinducedShapiroMaps
import Dubon2026.ContinuousCohomologyRestriction
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Evaluation in the original continuous Shapiro comparison

Restriction to the original subgroup followed by evaluation at the original
identity gives the reverse H1 and H2 maps. Existing restriction and coefficient
maps preserve their actual continuous witnesses. The inverse identities are proved
in ContinuousCoinducedShapiroH1Equiv and ContinuousCoinducedShapiroH2Equiv
for the local duality argument serving DUB-17.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- Evaluate the original coinduced coefficient at the original identity. -/
def coinducedIdentityEvaluation :
    restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype →ₗ[R]
      restrictedCoefficientRep A S.subtype where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual evaluation map is equivariant for the original subgroup. -/
theorem coinducedIdentityEvaluation_equivariant (s : S)
    (f : Rep.coind S.subtype (Rep.res S.subtype A)) :
    coinducedIdentityEvaluation A S
      ((restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype).ρ s f) =
      (restrictedCoefficientRep A S.subtype).ρ s (coinducedIdentityEvaluation A S f) := by
  change f.val (1 * (s : G)) = A.ρ (s : G) (f.val 1)
  simpa only [one_mul, mul_one] using f.property s 1

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- The genuine reverse H1 map is original subgroup restriction followed by
the original identity evaluation coefficient map. -/
def continuousCoinducedEvaluationH1 :
    ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) →ₗ[R]
    ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) :=
  (continuousCoefficientH1Map
    (restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype)
    (restrictedCoefficientRep A S.subtype) (coinducedIdentityEvaluation A S)
    continuous_of_discreteTopology (coinducedIdentityEvaluation_equivariant A S)
    (restrictedCoefficientAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A))
      S.subtype continuous_subtype_val (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).comp
    (continuousRepresentationH1Restriction (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) S.subtype continuous_subtype_val)

/-- The genuine reverse H2 map uses the same original restriction and evaluation,
including actual continuous one-cochain boundary witnesses. -/
def continuousCoinducedEvaluationH2 :
    ContinuousRepresentationH2 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) →ₗ[R]
    ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) :=
  (continuousCoefficientH2Map
    (restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype)
    (restrictedCoefficientRep A S.subtype) (coinducedIdentityEvaluation A S)
    continuous_of_discreteTopology (coinducedIdentityEvaluation_equivariant A S)
    (restrictedCoefficientAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A))
      S.subtype continuous_subtype_val (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).comp
    (continuousRepresentationH2Restriction (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) S.subtype continuous_subtype_val)

/-- Original H1 representatives are restricted and evaluated at the same identity. -/
theorem continuousCoinducedEvaluationH1_mk
    (c : continuousRepresentationCocyclesOne (Rep.coind S.subtype (Rep.res S.subtype A))) :
    continuousCoinducedEvaluationH1 A S hA hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleOneMap
        (restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype)
        (restrictedCoefficientRep A S.subtype) (coinducedIdentityEvaluation A S)
        continuous_of_discreteTopology (coinducedIdentityEvaluation_equivariant A S)
        (continuousRepresentationCocycleOneRestriction
          (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype continuous_subtype_val c)) := rfl

/-- Original H2 representatives undergo the identical restriction and evaluation. -/
theorem continuousCoinducedEvaluationH2_mk
    (c : continuousRepresentationCocyclesTwo (Rep.coind S.subtype (Rep.res S.subtype A))) :
    continuousCoinducedEvaluationH2 A S hA hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype)
        (restrictedCoefficientRep A S.subtype) (coinducedIdentityEvaluation A S)
        continuous_of_discreteTopology (coinducedIdentityEvaluation_equivariant A S)
        (continuousRepresentationCocycleTwoRestriction
          (Rep.coind S.subtype (Rep.res S.subtype A)) S.subtype continuous_subtype_val c)) := rfl

end
end Dubon2026
