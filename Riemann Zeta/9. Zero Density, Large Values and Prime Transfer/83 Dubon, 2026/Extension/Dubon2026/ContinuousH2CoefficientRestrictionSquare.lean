import Dubon2026.ContinuousCohomologyRestriction
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Literal coefficient squares on continuous H2

This same-cocycle identity transports the constructed finite relation
square to continuous H2 in DUB-17's source-cup comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (π : G →* H) (hπ : Continuous π)
  (A C : Rep.{0} R H) (B D : Rep.{0} R G)
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace D] [DiscreteTopology D] [ContinuousSMul R D]
  (hA : Continuous (fun z : H × A => A.ρ z.1 z.2))
  (hC : Continuous (fun z : H × C => C.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

/-- The literal finite/global coefficient square gives equality of the
actual continuous H2 images, preserving the original cocycles. -/
theorem continuousH2_coefficient_restriction_square
    (α : Rep.res π A ⟶ B) (η : A ⟶ C) (j : Rep.res π C ⟶ D) (φ : B ⟶ D)
    (hs : (Rep.resFunctor π).map η ≫ j = α ≫ φ)
    (x : ContinuousRepresentationH2 A hA) :
    continuousCoefficientH2Map B D φ.hom.toLinearMap continuous_of_discreteTopology
      (Rep.hom_comm_apply φ) hB hD
      (continuousCoefficientH2Map (Rep.res π A) B α.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply α)
        (restrictedCoefficientAction_continuous A π hπ hA) hB
        (continuousRepresentationH2Restriction A hA π hπ x)) =
    continuousCoefficientH2Map (Rep.res π C) D j.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply j)
      (restrictedCoefficientAction_continuous C π hπ hC) hD
      (continuousRepresentationH2Restriction C hC π hπ
        (continuousCoefficientH2Map A C η.hom.toLinearMap
          continuous_of_discreteTopology (Rep.hom_comm_apply η) hA hC x)) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg (fun z : continuousRepresentationCocyclesTwo D =>
      (Submodule.Quotient.mk z : ContinuousRepresentationH2 D hD))
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact congrArg (fun m : Rep.res π A ⟶ D => m.hom (c.val (π z.1, π z.2))) hs.symm

end
end Dubon2026
