import Dubon2026.ContinuousCharacterBidualCup
import Dubon2026.ContinuousCharacterDualH2Naturality
import Dubon2026.ContinuousCharacterH2DualInvariantPairing

/-! # Original invariant coefficients under actual character biduality

Restrict the proved coefficient evaluation equivalence to actual invariants.
The two original H2 evaluation pairings agree under this identification,
allowing the effacement theorem to detect the dual H2 endpoint needed for
DUB-17's global-duality sequence without a new coefficient model.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  (A : Rep.{0} k G) [Finite A] (χ : G →* k)

/-- Actual bidual evaluation identifies the original invariant subspaces. -/
def characterBidualInvariantEquiv :
    A.ρ.invariants ≃ₗ[k] (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ).ρ.invariants :=
  { coefficientInvariantLinearMap A (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)
      (characterBidualCoefficientEquiv A χ).toLinearMap (characterBidualCoefficientEquiv_equivariant A χ) with
    invFun w := ⟨(characterBidualCoefficientEquiv A χ).symm w.val, fun g => by
      apply (characterBidualCoefficientEquiv A χ).injective
      rw [characterBidualCoefficientEquiv_equivariant, LinearEquiv.apply_symm_apply]
      exact w.property g⟩
    left_inv w := Subtype.ext ((characterBidualCoefficientEquiv A χ).symm_apply_apply w.val)
    right_inv w := Subtype.ext ((characterBidualCoefficientEquiv A χ).apply_symm_apply w.val) }

variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hχ : Continuous χ) (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Both original H2/invariant evaluation conventions coincide through
actual bidual evaluation, on the same original dual H2 class. -/
theorem continuousCharacterH2DualInvariantPairing_bidual
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : A.ρ.invariants) :
    continuousCharacterH2DualInvariantPairing (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) x (characterBidualInvariantEquiv A χ w) =
      continuousCharacterDualH2InvariantPairing A χ hχ hA x w := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
