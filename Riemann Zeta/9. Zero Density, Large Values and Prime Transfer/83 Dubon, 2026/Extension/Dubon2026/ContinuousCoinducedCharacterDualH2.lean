import Dubon2026.ContinuousCoinducedCharacterDualH1
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv
import Dubon2026.ContinuousCharacterDualH2Pairing

/-! # The actual induced character-dual H2 and invariant evaluation

The same original coefficient equivalence descends to actual H2 and preserves
its evaluation against original invariants. This supplies the dual H2 side
of the induced endpoint in DUB-17's finite-module local-duality argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite

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


/-- The actual induced-dual H2 is identified with the original character dual
of the induced module through its same literal coset pairing. -/
def continuousCoinducedCharacterDualH2Equiv :
    ContinuousRepresentationH2
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS) ≃+
      ContinuousRepresentationH2
        (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
        (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
          (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ) :=
  continuousH2AdditiveCoefficientEquiv _ _ (coinducedCharacterDualEquiv A S χ).toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (coinducedCharacterDualEquiv_equivariant A S χ) _ _


/-- The original induced dual H2 identification preserves actual invariant
evaluation, retaining the original coefficient map and continuous quotient. -/
theorem continuousCoinducedCharacterDualH2Equiv_pairing
    (y : ContinuousRepresentationH2
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS))
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants) :
    continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS y) w =
    continuousInvariantRightH2Map
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (Rep.coind S.subtype (Rep.res S.subtype A)) (coefficientCharacterRep χ)
      (coinducedCharacterPairing A S χ).flip
      (fun g ℓ a => coinducedCharacterPairing_equivariant A S χ g a ℓ)
      continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) w y := by
  induction y using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
