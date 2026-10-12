import Dubon2026.ContinuousCharacterDualCupNaturality
import Dubon2026.ContinuousInvariantH2Pairing

/-! # The actual character-dual H2 pairing with original invariants

Bilinearize the existing original coefficient-evaluation H2 maps. This is the
H0/H2 endpoint of the finite-module exact-sequence duality argument needed for
DUB-17; no endpoint nondegeneracy is assumed by its construction.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The original dual H2 class evaluates bilinearly against actual invariant
coefficients, via the original equivariant evaluation H2 map. -/
def continuousCharacterDualH2InvariantPairing :
    ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ) →ₗ[k]
      A.ρ.invariants →ₗ[k] ContinuousRepresentationH2 (coefficientCharacterRep χ)
        (coefficientCharacterAction_continuous χ hχ) where
  toFun x := {
    toFun w := continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w x
    map_add' u v := by
      induction x using Submodule.Quotient.induction_on with
      | _ c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        funext z
        change c.val z (u.val + v.val) = c.val z u.val + c.val z v.val
        exact map_add (c.val z) u.val v.val
    map_smul' r u := by
      induction x using Submodule.Quotient.induction_on with
      | _ c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        funext z
        change c.val z (r • u.val) = r • c.val z u.val
        exact map_smul (c.val z) r u.val }
  map_add' x y := by
    apply LinearMap.ext
    intro w
    exact map_add (continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w) x y
  map_smul' r x := by
    apply LinearMap.ext
    intro w
    exact map_smul (continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w) r x

/-- The actual endpoint pairing is exactly the original invariant evaluation
on the same H2 quotient, with no change of cocycles or coboundaries. -/
theorem continuousCharacterDualH2InvariantPairing_apply
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA x w =
    continuousInvariantRightH2Map (characterDualCoefficientRep A χ) A
      (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
      (fun g ℓ a => characterDualEvaluation_equivariant A χ g a ℓ)
      continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ)
      (coefficientCharacterAction_continuous χ hχ) w x := rfl

end
end Dubon2026
