import Dubon2026.CoinducedEvaluationTwoHomotopy
import Dubon2026.ContinuousCoinducedShapiroH1Equiv

/-! # The genuine continuous H2 Shapiro equivalence

Both inverse identities use explicit continuous original cochains and the
actual subgroup-coordinate representatives. This discharges the H2 comparison
in the induced-module dependency of DUB-17's local duality argument.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- Actual evaluation after the actual H2 Shapiro lift is the identity on the
original continuous subgroup cohomology quotient. -/
theorem continuousCoinducedEvaluationH2_shapiro
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)) :
    continuousCoinducedEvaluationH2 A S hA hS (continuousCoinducedShapiroH2 A hA S hS x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoinducedShapiroH2_mk, continuousCoinducedEvaluationH2_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨⟨coefficientConjugationTwoHomotopy (restrictedCoefficientRep A S.subtype) c.val
      (coinducedSubgroupCoordinate S 1),
      coefficientConjugationTwoHomotopy_continuous (restrictedCoefficientRep A S.subtype)
        c.val c.property (coinducedSubgroupCoordinate S 1)⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedEvaluation_shapiroTwo_sub A S c.val).symm

/-- The original continuous H2 Shapiro equivalence, with both actual inverse
identities proved by continuous original coboundary witnesses. -/
def continuousCoinducedShapiroH2Equiv :
    ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≃ₗ[R]
    ContinuousRepresentationH2 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) :=
  { continuousCoinducedShapiroH2 A hA S hS with
    invFun := continuousCoinducedEvaluationH2 A S hA hS
    left_inv := continuousCoinducedEvaluationH2_shapiro A S hA hS
    right_inv := continuousCoinducedShapiroH2_evaluation A hA S hS }

/-- The actual original continuous H2 Shapiro map is bijective. -/
theorem continuousCoinducedShapiroH2_bijective :
    Function.Bijective (continuousCoinducedShapiroH2 A hA S hS) :=
  (continuousCoinducedShapiroH2Equiv A S hA hS).bijective

end
end Dubon2026
