import Dubon2026.FiniteCoinducedCoefficientUnit
import Dubon2026.ContinuousCohomologyRestrictionEffacement

/-! # Actual finite coefficient embeddings efface low-degree classes

The existing period subgroups and the genuine continuous Shapiro equivalences
give injective finite coefficient embeddings killing each actual H1/H2 class.
This supplies concrete finite effacements for the exact-sequence argument in
DUB-17's local duality route; it asserts no higher-degree vanishing or duality.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [DiscreteTopology R]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep.{0} R G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]

/-- The actual finite coinduced coefficient carries its discrete topology. -/
local instance finiteEffacementCoefficientTopology (S : Subgroup G) :
    TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A)) := ⊥

/-- The chosen original coinduced coefficient topology is discrete. -/
local instance finiteEffacementCoefficientDiscrete (S : Subgroup G) :
    DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A)) := ⟨rfl⟩

/-- All actual discrete coefficient scalar actions used here are continuous. -/
local instance finiteEffacementScalarContinuous (X : Type) [AddCommGroup X] [Module R X]
    [TopologicalSpace X] [DiscreteTopology X] : ContinuousSMul R X :=
  ⟨continuous_of_discreteTopology⟩

/-- The original compact group has finitely many cosets of each chosen open normal subgroup. -/
local instance finiteEffacementCosets (U : OpenNormalSubgroup G) : Finite (G ⧸ U.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen

variable (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Each original H1 class is killed by an actual injective coefficient map
into a finite module with its proved continuous coinduced action. -/
theorem continuousH1_exists_finite_coinduced_effacement (x : ContinuousRepresentationH1 A hA) :
    ∃ U : OpenNormalSubgroup G,
      Finite (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A)) ∧
      Function.Injective (finiteCoinducedCoefficientUnit A U.toSubgroup) ∧
      continuousCoefficientH1Map A (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A))
        (finiteCoinducedCoefficientUnit A U.toSubgroup) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A U.toSubgroup) hA
        (finiteCoinducedCoefficientAction_continuous A U.toSubgroup hA U.isOpen) x = 0 := by
  obtain ⟨U, hU⟩ := continuousH1_exists_openNormal_restriction_zero A hA x
  haveI : ContinuousSMul R (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A)) :=
    ⟨continuous_of_discreteTopology⟩
  refine ⟨U, coinducedCoefficient_finite A U.toSubgroup,
    finiteCoinducedCoefficientUnit_injective A U.toSubgroup, ?_⟩
  apply (continuousCoinducedShapiroH1Equiv A U.toSubgroup hA U.isOpen).symm.injective
  change continuousCoinducedEvaluationH1 A U.toSubgroup hA U.isOpen _ =
    continuousCoinducedEvaluationH1 A U.toSubgroup hA U.isOpen 0
  rw [map_zero, continuousCoinducedEvaluationH1_unit]
  exact hU

/-- Each original H2 class is killed by an actual finite injective coefficient
embedding, using continuous original boundaries and the genuine H2 inverse. -/
theorem continuousH2_exists_finite_coinduced_effacement (x : ContinuousRepresentationH2 A hA) :
    ∃ U : OpenNormalSubgroup G,
      Finite (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A)) ∧
      Function.Injective (finiteCoinducedCoefficientUnit A U.toSubgroup) ∧
      continuousCoefficientH2Map A (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A))
        (finiteCoinducedCoefficientUnit A U.toSubgroup) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A U.toSubgroup) hA
        (finiteCoinducedCoefficientAction_continuous A U.toSubgroup hA U.isOpen) x = 0 := by
  obtain ⟨U, hU⟩ := continuousH2_exists_openNormal_restriction_zero A hA x
  haveI : ContinuousSMul R (Rep.coind U.toSubgroup.subtype (Rep.res U.toSubgroup.subtype A)) :=
    ⟨continuous_of_discreteTopology⟩
  refine ⟨U, coinducedCoefficient_finite A U.toSubgroup,
    finiteCoinducedCoefficientUnit_injective A U.toSubgroup, ?_⟩
  apply (continuousCoinducedShapiroH2Equiv A U.toSubgroup hA U.isOpen).symm.injective
  change continuousCoinducedEvaluationH2 A U.toSubgroup hA U.isOpen _ =
    continuousCoinducedEvaluationH2 A U.toSubgroup hA U.isOpen 0
  rw [map_zero, continuousCoinducedEvaluationH2_unit]
  exact hU

end
end Dubon2026
