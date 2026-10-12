import Dubon2026.ContinuousCharacterDualCupGroupEquiv
import Dubon2026.ContinuousCharacterDualH2Pairing
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv

/-! # The actual H2/H0 endpoint under original group identification

The original invariants keep their values, and the original dual H2 is
transported through its actual restricted dual action. Their pairing identity
moves the local split endpoint to the genuine fixing subgroup in DUB-17.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G H : Type} [Field k] [Group G] [Group H]

/-- An actual group isomorphism identifies the original invariant spaces,
with the literal identity on the original coefficient values. -/
def coefficientInvariantGroupEquiv (A : Rep.{0} k G) (j : H ≃* G) :
    A.ρ.invariants ≃ₗ[k] (restrictedCoefficientRep A j.toMonoidHom).ρ.invariants where
  toFun w := ⟨w.val, fun h => w.property (j h)⟩
  invFun w := ⟨w.val, fun g => by
    have h : A.ρ (j (j.symm g)) w.val = w.val := w.property (j.symm g)
    rwa [j.apply_symm_apply] at h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H ≃* G) (hj : Continuous j) (hji : Continuous j.symm)


/-- Actual character-dual H2 under group reindexing, including the original
restricted dual-action identification on its actual coefficient functions. -/
def continuousCharacterDualH2GroupEquiv :
    ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ) ≃+
      ContinuousRepresentationH2
        (characterDualCoefficientRep (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom))
        (finiteCharacterDualAction_continuous (restrictedCoefficientRep A j.toMonoidHom)
          (χ.comp j.toMonoidHom) (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)
          (hχ.comp hj)) :=
  (continuousH2GroupEquiv (characterDualCoefficientRep A χ) j hj hji
    (finiteCharacterDualAction_continuous A χ hA hχ)).trans
    (continuousH2AdditiveCoefficientEquiv _ _ (characterDualRestrictionEquiv A χ j.toMonoidHom).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology
      (characterDualRestrictionEquiv_equivariant A χ j.toMonoidHom) _ _)

/-- The original H2/invariant pairing commutes with the genuine group
identifications on all three original objects. -/
theorem continuousCharacterDualH2InvariantPairing_groupEquiv
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)
      (continuousCharacterDualH2InvariantPairing A χ hχ hA x w) =
    continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A j.toMonoidHom)
      (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)
      (continuousCharacterDualH2GroupEquiv A χ hχ hA j hj hji x)
      (coefficientInvariantGroupEquiv A j w) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

include hji in
/-- The actual reindexed endpoint detects the original dual H2 argument,
using the invariant and H2 equivalences and the proved original pairing identity. -/
theorem continuousCharacterDualH2InvariantPairing_left_injective_of_groupEquiv
    (h : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA))) :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA) := by
  intro x y heq
  apply (continuousCharacterDualH2GroupEquiv A χ hχ hA j hj hji).injective
  apply h
  apply LinearMap.ext
  intro w
  obtain ⟨w, rfl⟩ := (coefficientInvariantGroupEquiv A j).surjective w
  exact (continuousCharacterDualH2InvariantPairing_groupEquiv A χ hχ hA j hj hji x w).symm.trans
    ((congrArg (continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)) (DFunLike.congr_fun heq w)).trans
      (continuousCharacterDualH2InvariantPairing_groupEquiv A χ hχ hA j hj hji y w))

include hji in
/-- The opposite original invariant argument is detected through the same
actual reindexed endpoint, without an assumed invariant-pairing comparison. -/
theorem continuousCharacterDualH2InvariantPairing_right_injective_of_groupEquiv
    (h : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A j.toMonoidHom) (χ.comp j.toMonoidHom) (hχ.comp hj)
      (restrictedCoefficientAction_continuous A j.toMonoidHom hj hA)).flip) :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip := by
  intro w v heq
  apply (coefficientInvariantGroupEquiv A j).injective
  apply h
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (continuousCharacterDualH2GroupEquiv A χ hχ hA j hj hji).surjective x
  exact (continuousCharacterDualH2InvariantPairing_groupEquiv A χ hχ hA j hj hji x w).symm.trans
    ((congrArg (continuousH2GroupEquiv (coefficientCharacterRep χ) j hj hji
      (coefficientCharacterAction_continuous χ hχ)) (DFunLike.congr_fun heq x)).trans
      (continuousCharacterDualH2InvariantPairing_groupEquiv A χ hχ hA j hj hji x v))

end
end Dubon2026
