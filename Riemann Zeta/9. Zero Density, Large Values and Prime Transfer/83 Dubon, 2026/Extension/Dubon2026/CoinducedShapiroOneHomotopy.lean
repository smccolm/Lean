import Dubon2026.CoinducedShapiroCoordinateValues

/-! # The original H1 Shapiro/evaluation composite is the identity

An explicit original coinduced zero-cochain realizes the homogeneous edge
prism. It gives the actual continuous H1 inverse identity, one of the comparison
obligations needed in DUB-17's finite-module local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The actual original coinduced zero-cochain in the edge prism homotopy. -/
def coinducedShapiroOneHomotopy
    (c : G → Rep.coind S.subtype (Rep.res S.subtype A)) :
    Rep.coind S.subtype (Rep.res S.subtype A) :=
  ⟨fun t => coinducedHomogeneousOne A S c t (coinducedSubgroupCoordinate S t), by
    intro s t
    change coinducedHomogeneousOne A S c ((s : G) * t)
      (coinducedSubgroupCoordinate S ((s : G) * t)) =
      A.ρ (s : G) (coinducedHomogeneousOne A S c t (coinducedSubgroupCoordinate S t))
    rw [coinducedSubgroupCoordinate_mul]
    exact coinducedHomogeneousOne_equivariant A S c s t (coinducedSubgroupCoordinate S t)⟩

/-- The actual lifted evaluation differs from the original cocycle by the
original coboundary of the explicit coinduced zero-cochain. -/
theorem coinducedShapiroOne_evaluation_sub
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A))) :
    coinducedShapiroOne A S (fun s : S => (c (s : G)).val 1) - c.val =
      groupCohomology.d₀₁ (Rep.coind S.subtype (Rep.res S.subtype A))
        (coinducedShapiroOneHomotopy A S c) := by
  funext g
  apply Subtype.ext
  funext t
  change (coinducedShapiroOne A S (fun s : S => (c (s : G)).val 1) g).val t - (c g).val t =
    coinducedHomogeneousOne A S c (t * g) (coinducedSubgroupCoordinate S (t * g)) -
      coinducedHomogeneousOne A S c t (coinducedSubgroupCoordinate S t)
  rw [coinducedShapiroOne_evaluation_value]
  have hc := coinducedHomogeneousOne_prism A S c t (t * g)
    (coinducedSubgroupCoordinate S t) (coinducedSubgroupCoordinate S (t * g))
  have ho : coinducedHomogeneousOne A S c t (t * g) = (c g).val t := by
    simp only [coinducedHomogeneousOne, inv_mul_cancel_left]
  rw [ho] at hc
  exact hc.symm

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- The actual H1 Shapiro map after actual restriction/evaluation is the
identity on the original continuous cohomology quotient. -/
theorem continuousCoinducedShapiroH1_evaluation
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS)) :
    continuousCoinducedShapiroH1 A hA S hS (continuousCoinducedEvaluationH1 A S hA hS x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoinducedEvaluationH1_mk, continuousCoinducedShapiroH1_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨coinducedShapiroOneHomotopy A S c.val, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroOne_evaluation_sub A S c.val).symm

end
end Dubon2026
