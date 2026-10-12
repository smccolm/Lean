import Dubon2026.CoinducedShapiroOneHomotopy

/-! # The genuine continuous H1 Shapiro equivalence

The opposite composite accounts for the actual identity-coset representative.
Together with the proved coinduced prism, this gives both actual inverse
identities required by the H1 comparison in DUB-17's local duality dependency.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- Evaluation of the original lift differs from the original subgroup cocycle
by the coboundary at the actual identity-coset representative. -/
theorem coinducedEvaluation_shapiroOne_sub
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    (fun s : S => (coinducedShapiroOne A S c (s : G)).val 1) - c.val =
      groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype)
        (c (coinducedSubgroupCoordinate S 1)) := by
  funext s
  let r := coinducedSubgroupCoordinate S 1
  have h₁ := (groupCohomology.mem_cocycles₁_iff _).mp c.property s r
  have h₂ := (groupCohomology.mem_cocycles₁_iff _).mp c.property r (r⁻¹ * (s * r))
  rw [mul_inv_cancel_left] at h₂
  have he := h₂.symm.trans h₁
  change (coinducedShapiroOne A S c (s : G)).val 1 - c s = A.ρ (s : G) (c r) - c r
  rw [coinducedShapiroOne_apply, one_mul, coinducedSubgroupCoordinate_subgroup]
  change A.ρ (r : G) (c (r⁻¹ * (s * r))) - c s = A.ρ (s : G) (c r) - c r
  apply sub_eq_zero.mp
  calc
    _ = (A.ρ (r : G) (c (r⁻¹ * (s * r))) + c r) -
      (A.ρ (s : G) (c r) + c s) := by abel
    _ = 0 := sub_eq_zero.mpr he

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- Actual evaluation after the actual H1 Shapiro lift is the identity on the
original continuous subgroup cohomology quotient. -/
theorem continuousCoinducedEvaluationH1_shapiro
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)) :
    continuousCoinducedEvaluationH1 A S hA hS (continuousCoinducedShapiroH1 A hA S hS x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoinducedShapiroH1_mk, continuousCoinducedEvaluationH1_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨c.val (coinducedSubgroupCoordinate S 1), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedEvaluation_shapiroOne_sub A S c.val).symm

/-- The original continuous H1 Shapiro equivalence, with both actual inverse
identities proved by original coboundary witnesses. -/
def continuousCoinducedShapiroH1Equiv :
    ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≃ₗ[R]
    ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) :=
  { continuousCoinducedShapiroH1 A hA S hS with
    invFun := continuousCoinducedEvaluationH1 A S hA hS
    left_inv := continuousCoinducedEvaluationH1_shapiro A S hA hS
    right_inv := continuousCoinducedShapiroH1_evaluation A S hA hS }

/-- The actual original continuous H1 Shapiro map is bijective. -/
theorem continuousCoinducedShapiroH1_bijective :
    Function.Bijective (continuousCoinducedShapiroH1 A hA S hS) :=
  (continuousCoinducedShapiroH1Equiv A S hA hS).bijective

end
end Dubon2026
