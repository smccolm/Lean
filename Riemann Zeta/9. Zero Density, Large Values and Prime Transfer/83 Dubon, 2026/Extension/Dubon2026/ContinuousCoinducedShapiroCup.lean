import Dubon2026.CoinducedShapiroCupCochains
import Dubon2026.ContinuousCoinducedShapiroH2Equiv
import Dubon2026.ContinuousCupCorestriction

/-! # The actual continuous Shapiro cup/corestriction comparison

The exact original cochain equality descends through the already constructed
continuous quotients. This removes the induced-module cup compatibility
obligation on DUB-17's finite-module local duality dependency chain.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k)
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [ContinuousSMul k (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul k (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [ContinuousSMul k (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hD : Continuous (fun z : G × characterDualCoefficientRep A χ =>
    (characterDualCoefficientRep A χ).ρ z.1 z.2))
  (hC : Continuous (fun z : G × coefficientCharacterRep χ =>
    (coefficientCharacterRep χ).ρ z.1 z.2)) (hS : IsOpen (S : Set G))

/-- The original cup of both continuous Shapiro classes equals actual
corestriction of their original subgroup cup, with the actual induced dual pairing. -/
theorem continuousCoinducedShapiroH1_cup
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
        S.subtype continuous_subtype_val hD)) :
    continuousH1Cup (Rep.coind S.subtype (Rep.res S.subtype A))
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (coefficientCharacterRep χ) (coinducedCharacterPairing A S χ)
      (coinducedCharacterPairing_equivariant A S χ) continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S hD hS) hC
      (continuousCoinducedShapiroH1 A hA S hS x)
      (continuousCoinducedShapiroH1 (characterDualCoefficientRep A χ) hD S hS y) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ) hC S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
        (restrictedCoefficientRep (coefficientCharacterRep χ) S.subtype)
        (characterDualEvaluation A χ) (fun g a ℓ => characterDualEvaluation_equivariant A χ g a ℓ)
        continuous_of_discreteTopology
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ)
          S.subtype continuous_subtype_val hD)
        (restrictedCoefficientAction_continuous (coefficientCharacterRep χ)
          S.subtype continuous_subtype_val hC) x y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      rw [continuousCoinducedShapiroH1_mk, continuousCoinducedShapiroH1_mk,
        continuousH1Cup_mk, continuousH1Cup_mk, continuousRepresentationH2Corestriction_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact coinducedShapiroCup_cochain A S χ c.val u.val

end
end Dubon2026
