import Dubon2026.ContinuousCoinducedShapiroCup
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousCharacterDualCupNaturality

/-! # The original continuous H1 of the induced character dual

The proved coefficient dual equivalence descends through the original H1
quotients. Its exact cup compatibility connects induced-module nondegeneracy
to the split local pairing in the DUB-17 finite-module duality argument.
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

/-- The original coinduced dual H1 is equivalent to the actual character dual
of the original coinduced coefficient module, through its literal coset pairing. -/
def continuousCoinducedCharacterDualH1Equiv :
    ContinuousRepresentationH1
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS) ≃+
      ContinuousRepresentationH1
        (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
        (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
          (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ) :=
  continuousH1AdditiveCoefficientEquiv _ _ (coinducedCharacterDualEquiv A S χ).toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (coinducedCharacterDualEquiv_equivariant A S χ) _ _

/-- The actual induced character-dual H1 equivalence preserves original cup
values, with no assumed cohomological pairing or nondegeneracy comparison. -/
theorem continuousCoinducedCharacterDualH1Equiv_cup
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (y : ContinuousRepresentationH1
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)) :
    continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x
      (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS y) =
    continuousH1Cup (Rep.coind S.subtype (Rep.res S.subtype A))
      (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))
      (coefficientCharacterRep χ) (coinducedCharacterPairing A S χ)
      (coinducedCharacterPairing_equivariant A S χ) continuous_of_discreteTopology
      (finiteCoinducedCoefficientAction_continuous A S hA hS)
      (finiteCoinducedCoefficientAction_continuous (characterDualCoefficientRep A χ) S
        (finiteCharacterDualAction_continuous A χ hA hχ) hS)
      (coefficientCharacterAction_continuous χ hχ) x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      change _ = Submodule.Quotient.mk _
      rw [continuousCoinducedCharacterDualH1Equiv, continuousH1AdditiveCoefficientEquiv_mk,
        continuousCharacterDualH1Cup_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change characterDualEvaluation (Rep.coind S.subtype (Rep.res S.subtype A)) χ
        (c.val z.1)
        ((characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ).ρ z.1
          (coinducedCharacterDualEquiv A S χ (u.val z.2))) = _
      rw [← coinducedCharacterDualEquiv_equivariant]
      rfl

end
end Dubon2026
