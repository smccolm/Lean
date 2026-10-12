import Dubon2026.ContinuousCharacterDualCupNaturality
import Dubon2026.ContinuousH1GroupReindex
import Dubon2026.ContinuousH2GroupReindex
import Dubon2026.ContinuousCupRestriction
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! # Original character-dual cups under the actual group identification

This comparison retains the original coefficient values and continuous
quotients. It transports the split local-field pairing to its actual Galois
fixing subgroup in the DUB-17 induced-module duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G H : Type} [Field k] [Group G] [Group H]

/-- Restricting the original character dual identifies its actual linear
functionals with the dual of the restricted original coefficient. -/
def characterDualRestrictionEquiv (A : Rep.{0} k G) (χ : G →* k) (j : H →* G) :
    restrictedCoefficientRep (characterDualCoefficientRep A χ) j ≃ₗ[k]
      characterDualCoefficientRep (restrictedCoefficientRep A j) (χ.comp j) :=
  LinearEquiv.refl _ _

/-- The literal functional identification preserves the restricted dual
action because the original group homomorphism preserves inverses. -/
theorem characterDualRestrictionEquiv_equivariant (A : Rep.{0} k G) (χ : G →* k) (j : H →* G)
    (g : H) (ℓ : restrictedCoefficientRep (characterDualCoefficientRep A χ) j) :
    characterDualRestrictionEquiv A χ j
      ((restrictedCoefficientRep (characterDualCoefficientRep A χ) j).ρ g ℓ) =
      (characterDualCoefficientRep (restrictedCoefficientRep A j) (χ.comp j)).ρ g
        (characterDualRestrictionEquiv A χ j ℓ) := by
  apply LinearMap.ext
  intro a
  change χ (j g) * ℓ (A.ρ ((j g)⁻¹) a) = χ (j g) * ℓ (A.ρ (j g⁻¹) a)
  rw [map_inv j]

variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)

/-- The original dual H1 under group reindexing, including the actual
identification of its restricted character-dual action. -/
def continuousCharacterDualH1GroupEquiv :
    ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ) ≃+
      ContinuousRepresentationH1
        (characterDualCoefficientRep (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom))
        (finiteCharacterDualAction_continuous (restrictedCoefficientRep A j.toMonoidHom)
          (χ.comp j.toMonoidHom) (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)
          (hχ.comp hj)) :=
  (continuousH1GroupEquiv (characterDualCoefficientRep A χ) j hj hji
    (finiteCharacterDualAction_continuous A χ hA hχ)).trans
    (continuousH1AdditiveCoefficientEquiv _ _ (characterDualRestrictionEquiv A χ j.toMonoidHom).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology
      (characterDualRestrictionEquiv_equivariant A χ j.toMonoidHom) _ _)

/-- The genuine character-dual cup commutes with the original continuous
group equivalences, so no pairing comparison is assumed on the fixing field. -/
theorem continuousCharacterDualH1Cup_groupEquiv
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)
      (continuousCharacterDualH1Cup A χ hχ hA x y) =
    continuousCharacterDualH1Cup (restrictedCoefficientRep A j.toMonoidHom)
      (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)
      (continuousH1GroupEquiv A j hj hji hA x)
      (continuousCharacterDualH1GroupEquiv A χ hχ hA j hj hji y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change χ (j z.1) * u.val (j z.2) (A.ρ ((j z.1)⁻¹) (c.val (j z.1))) =
        χ (j z.1) * u.val (j z.2) (A.ρ (j z.1⁻¹) (c.val (j z.1)))
      rw [map_inv j]

include hji in
/-- Injectivity in the original coefficient argument follows from the actual
reindexed pairing, using the proved original cup comparison and both H1 equivalences. -/
theorem continuousCharacterDualH1Cup_left_injective_of_groupEquiv
    (h : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA))) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA) := by
  intro x y heq
  apply (continuousH1GroupEquiv A j hj hji hA).injective
  apply h
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (continuousCharacterDualH1GroupEquiv A χ hχ hA j hj hji).surjective z
  exact (continuousCharacterDualH1Cup_groupEquiv A χ hχ hA j hj hji x z).symm.trans
    ((congrArg (continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)) (DFunLike.congr_fun heq z)).trans
      (continuousCharacterDualH1Cup_groupEquiv A χ hχ hA j hj hji y z))

include hji in
/-- Injectivity in the original dual argument likewise follows from the
actual reindexed pairing, retaining the original dual coefficient action. -/
theorem continuousCharacterDualH1Cup_right_injective_of_groupEquiv
    (h : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH1Cup A χ hχ hA).flip := by
  intro x y heq
  apply (continuousCharacterDualH1GroupEquiv A χ hχ hA j hj hji).injective
  apply h
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (continuousH1GroupEquiv A j hj hji hA).surjective z
  exact (continuousCharacterDualH1Cup_groupEquiv A χ hχ hA j hj hji z x).symm.trans
    ((congrArg (continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)) (DFunLike.congr_fun heq z)).trans
      (continuousCharacterDualH1Cup_groupEquiv A χ hχ hA j hj hji z y))

end
end Dubon2026
