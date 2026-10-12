import Dubon2026.ContinuousCharacterDualH2Pairing
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousCupSkewSymmetry

/-! # Actual character biduality and the original continuous H1 cup

The pinned evaluation equivalence intertwines the original twice-twisted
dual action. Its genuine H1 identification and the original skew cup identity
transfer the proved left annihilator to the right one in DUB-17 local duality.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) [Finite A]
  (χ : G →* k)

/-- The actual twice character-valued dual is identified by original evaluation. -/
def characterBidualCoefficientEquiv : A ≃ₗ[k]
    characterDualCoefficientRep (characterDualCoefficientRep A χ) χ := Module.evalEquiv k A

/-- Evaluation intertwines the original bidual action; the two character
factors cancel by the original group inverse, not by a changed coefficient action. -/
theorem characterBidualCoefficientEquiv_equivariant (g : G) (a : A) :
    characterBidualCoefficientEquiv A χ (A.ρ g a) =
      (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ).ρ g
        (characterBidualCoefficientEquiv A χ a) := by
  apply LinearMap.ext
  intro ℓ
  change ℓ (A.ρ g a) = χ g * (χ g⁻¹ * ℓ (A.ρ (g⁻¹)⁻¹ a))
  rw [inv_inv, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

variable [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A]
  (hχ : Continuous χ)
  [Finite (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  [DiscreteTopology (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Original continuous H1 classes and their actual bidual classes are
identified by evaluation on original coefficients and original boundaries. -/
def continuousCharacterBidualH1Equiv : ContinuousRepresentationH1 A hA ≃+
    ContinuousRepresentationH1 (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)
      (finiteCharacterDualAction_continuous (characterDualCoefficientRep A χ) χ
        (finiteCharacterDualAction_continuous A χ hA hχ) hχ) :=
  continuousH1AdditiveCoefficientEquiv A (characterDualCoefficientRep (characterDualCoefficientRep A χ) χ)
    (characterBidualCoefficientEquiv A χ).toAddEquiv continuous_of_discreteTopology
    continuous_of_discreteTopology (characterBidualCoefficientEquiv_equivariant A χ) _ _

/-- Under actual bidual evaluation, the dual module's original H1 cup is
the negative original cup with its two H1 arguments exchanged. -/
theorem continuousCharacterDualH1Cup_bidual
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) :
    continuousCharacterDualH1Cup (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) y (continuousCharacterBidualH1Equiv A χ hχ hA x) =
      -continuousCharacterDualH1Cup A χ hχ hA x y := by
  have hp : continuousCharacterDualH1Cup (characterDualCoefficientRep A χ) χ hχ
      (finiteCharacterDualAction_continuous A χ hA hχ) y (continuousCharacterBidualH1Equiv A χ hχ hA x) =
      continuousH1Cup (characterDualCoefficientRep A χ) A (coefficientCharacterRep χ)
        (characterDualEvaluation A χ).flip (fun g u a => characterDualEvaluation_equivariant A χ g a u)
        continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ) hA
        (coefficientCharacterAction_continuous χ hχ) y x := by
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      induction x using Submodule.Quotient.induction_on with
      | _ c =>
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        apply Subtype.ext
        funext z
        change ((characterDualCoefficientRep (characterDualCoefficientRep A χ) χ).ρ z.1
          (characterBidualCoefficientEquiv A χ (c.val z.2))) (u.val z.1) =
          (u.val z.1) (A.ρ z.1 (c.val z.2))
        rw [← characterBidualCoefficientEquiv_equivariant]
        rfl
  exact hp.trans (continuousH1Cup_skew (characterDualCoefficientRep A χ) A
    (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
    (fun g u a => characterDualEvaluation_equivariant A χ g a u)
    continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ) hA
    (coefficientCharacterAction_continuous χ hχ) y x)

end
end Dubon2026
