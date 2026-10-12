import Dubon2026.ContinuousCoinducedShapiroH2Equiv

/-! # The original finite-index restriction/coinduction embedding

The pinned adjunction unit embeds the original coefficient module. Its actual
H1/H2 maps become the original restriction under the proved continuous
Shapiro evaluation. This is the finite-coefficient effacement interface used
in DUB-17's exact-sequence local duality route.
-/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The original restriction/coinduction unit, using the pinned adjunction. -/
def finiteCoinducedCoefficientUnit : A →ₗ[R] Rep.coind S.subtype (Rep.res S.subtype A) :=
  (Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)).hom.toLinearMap

/-- The original unit intertwines the actual coefficient and coinduced actions. -/
theorem finiteCoinducedCoefficientUnit_equivariant (g : G) (a : A) :
    finiteCoinducedCoefficientUnit A S (A.ρ g a) =
      (Rep.coind S.subtype (Rep.res S.subtype A)).ρ g (finiteCoinducedCoefficientUnit A S a) :=
  Rep.hom_comm_apply (Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)) g a

/-- Original identity evaluation recovers the same coefficient from its unit image. -/
theorem finiteCoinducedCoefficientUnit_evaluate (a : A) :
    (finiteCoinducedCoefficientUnit A S a).val 1 = a := by
  change A.ρ 1 a = a
  rw [map_one, Module.End.one_apply]

/-- The actual finite-index adjunction unit is injective on original coefficients. -/
theorem finiteCoinducedCoefficientUnit_injective :
    Function.Injective (finiteCoinducedCoefficientUnit A S) := by
  intro a b he
  have ht := congrArg (fun f : Rep.coind S.subtype (Rep.res S.subtype A) => f.val 1) he
  exact (finiteCoinducedCoefficientUnit_evaluate A S a).symm.trans
    (ht.trans (finiteCoinducedCoefficientUnit_evaluate A S b))

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- Under actual Shapiro evaluation, the original unit map in continuous H1
is exactly restriction to the same original subgroup. -/
theorem continuousCoinducedEvaluationH1_unit (x : ContinuousRepresentationH1 A hA) :
    continuousCoinducedEvaluationH1 A S hA hS
      (continuousCoefficientH1Map A (Rep.coind S.subtype (Rep.res S.subtype A))
        (finiteCoinducedCoefficientUnit A S) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A S) hA
        (finiteCoinducedCoefficientAction_continuous A S hA hS) x) =
      continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoefficientH1Map_mk, continuousCoinducedEvaluationH1_mk,
      continuousRepresentationH1Restriction_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact finiteCoinducedCoefficientUnit_evaluate A S (c.val (g : G))

/-- The same original coefficient unit in continuous H2 becomes actual
subgroup restriction under the genuine Shapiro evaluation map. -/
theorem continuousCoinducedEvaluationH2_unit (x : ContinuousRepresentationH2 A hA) :
    continuousCoinducedEvaluationH2 A S hA hS
      (continuousCoefficientH2Map A (Rep.coind S.subtype (Rep.res S.subtype A))
        (finiteCoinducedCoefficientUnit A S) continuous_of_discreteTopology
        (finiteCoinducedCoefficientUnit_equivariant A S) hA
        (finiteCoinducedCoefficientAction_continuous A S hA hS) x) =
      continuousRepresentationH2Restriction A hA S.subtype continuous_subtype_val x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousCoefficientH2Map_mk, continuousCoinducedEvaluationH2_mk,
      continuousRepresentationH2Restriction_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact finiteCoinducedCoefficientUnit_evaluate A S (c.val (z.1, z.2))

end
end Dubon2026
