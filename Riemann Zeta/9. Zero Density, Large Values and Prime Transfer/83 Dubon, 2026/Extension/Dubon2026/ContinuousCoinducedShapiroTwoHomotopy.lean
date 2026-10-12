import Dubon2026.CoinducedShapiroTwoHomotopy

/-! # The continuous original H2 Shapiro prism

Finite coset reconstruction proves continuity of the explicit original
one-cochain. It therefore gives a boundary in the actual continuous H2
quotient, as required by DUB-17's induced-module local duality comparison.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]

include hA hS in
/-- The explicit original degree-two prism is a continuous coinduced one-cochain. -/
theorem coinducedShapiroTwoHomotopy_continuous
    (c : G × G → Rep.coind S.subtype (Rep.res S.subtype A)) (hc : Continuous c) :
    Continuous (coinducedShapiroTwoHomotopy A S c) := by
  have hr : Continuous (coinducedCosetReconstruct A S) := continuous_of_discreteTopology
  have hv : Continuous (fun g => coinducedCosetValues A S (coinducedShapiroTwoHomotopy A S c g)) := by
    apply continuous_pi
    intro q
    induction q using QuotientGroup.induction_on with
    | H t =>
      have hp : Continuous (fun g : G => (coinducedSubgroupCoordinate S (t⁻¹ * g) : G)) :=
        continuous_subtype_val.comp ((coinducedSubgroupCoordinate_continuous S hS).comp
          (continuous_const.mul continuous_id))
      have h₁ := coinducedHomogeneousTwo_continuous A hA S hS c hc
        (fun _ : G => t⁻¹) (fun _ : G => (coinducedSubgroupCoordinate S t⁻¹ : G))
        (fun g : G => (coinducedSubgroupCoordinate S (t⁻¹ * g) : G))
        continuous_const continuous_const hp
      have h₂ := coinducedHomogeneousTwo_continuous A hA S hS c hc
        (fun _ : G => t⁻¹) (fun g : G => t⁻¹ * g)
        (fun g : G => (coinducedSubgroupCoordinate S (t⁻¹ * g) : G))
        continuous_const (continuous_const.mul continuous_id) hp
      have ha : Continuous (A.ρ t) := continuous_of_discreteTopology
      exact ha.comp (h₁.sub h₂)
  exact (hr.comp hv).congr (fun g => coinducedCosetReconstruct_values A S _)

variable [TopologicalSpace R] [ContinuousSMul R A]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- The actual H2 Shapiro map after evaluation is the identity, with the
continuous original prism as its genuine quotient-boundary witness. -/
theorem continuousCoinducedShapiroH2_evaluation
    (x : ContinuousRepresentationH2 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS)) :
    continuousCoinducedShapiroH2 A hA S hS (continuousCoinducedEvaluationH2 A S hA hS x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoinducedEvaluationH2_mk, continuousCoinducedShapiroH2_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨⟨coinducedShapiroTwoHomotopy A S c.val,
      coinducedShapiroTwoHomotopy_continuous A hA S hS c.val c.property⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroTwo_evaluation_sub A S c.val).symm

end
end Dubon2026
