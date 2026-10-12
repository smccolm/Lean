import Dubon2026.ContinuousCoinducedCharacterDualH2
import Dubon2026.CoinducedShapiroInvariantPairing
import Dubon2026.ContinuousCoinducedCharacterDualShapiro

/-! # Actual continuous Shapiro compatibility for the H2/H0 endpoint

The original induced character-dual H2 evaluation equals scalar corestriction
of the original subgroup evaluation, under genuine H2 and invariant
identifications. This supplies the induced endpoint comparison needed by
DUB-17's finite-module local-duality exact-sequence argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))


/-- The genuine induced H2/H0 pairing is exactly the original scalar
corestriction of the subgroup endpoint pairing, with all original objects retained. -/
theorem continuousCoinducedShapiroH2Invariant_pairing
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep (characterDualCoefficientRep A χ) S.subtype)
      (restrictedCoefficientAction_continuous (characterDualCoefficientRep A χ) S.subtype
        continuous_subtype_val (finiteCharacterDualAction_continuous A χ hA hχ)))
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS
        (continuousCoinducedShapiroH2 (characterDualCoefficientRep A χ)
          (finiteCharacterDualAction_continuous A χ hA hχ) S hS x))
      (coinducedInvariantEquiv A S w) =
    continuousRepresentationH2Corestriction (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) S hS
      (continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
        (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x w) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    have hp := coinducedShapiroTwoZero_pairing A S χ c.val w.val z.1 z.2
    rw [coinducedShapiroZero_invariant A S w] at hp
    exact hp

end
end Dubon2026
