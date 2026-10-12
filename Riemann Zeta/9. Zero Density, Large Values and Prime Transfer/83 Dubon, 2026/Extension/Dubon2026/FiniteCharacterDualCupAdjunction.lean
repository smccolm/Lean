import Dubon2026.FiniteCharacterDualActionContinuity
import Dubon2026.ContinuousConnectingCupAdjunction

/-! # Cup adjunction for the genuine finite character-dual sequence

The original coefficient sequence determines its own exact character-valued
dual, evaluation pairings and continuous actions. The actual connecting-map
adjunction thus has no independently supplied dual-exactness or pairing-
compatibility premises. This serves DUB-17's finite-module local duality.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Scalar multiplication is continuous on each actual discrete coefficient. -/
local instance characterDualSequenceContinuousSMul (X : Type) [AddCommGroup X] [Module k X]
    [TopologicalSpace X] [DiscreteTopology X] : ContinuousSMul k X :=
  ⟨continuous_of_discreteTopology⟩

variable (A B C : Rep.{0} k G)
  [Finite B] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  [TopologicalSpace (characterDualCoefficientRep C χ)]
  [DiscreteTopology (characterDualCoefficientRep C χ)]
  (φ : A →ₗ[k] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[k] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- The original continuous connecting map is adjoint to the connecting map of
its genuine character dual. Dual exactness, equivariance, joint continuity and
the evaluation identities are all derived from the original sequence. -/
theorem finiteCharacterDualConnecting_adjunction
    (x : ContinuousRepresentationH1 C hC)
    (w : (characterDualCoefficientRep A χ).ρ.invariants) :
    let U := characterDualCoefficientRep C χ
    let V := characterDualCoefficientRep B χ
    let W := characterDualCoefficientRep A χ
    let D := coefficientCharacterRep χ
    let hU := finiteCharacterDualAction_continuous C χ hC hχ
    let hV := finiteCharacterDualAction_continuous B χ hB hχ
    let hD := coefficientCharacterAction_continuous χ hχ
    continuousInvariantRightH2Map A W D (characterDualEvaluation A χ)
      (characterDualEvaluation_equivariant A χ) continuous_of_discreteTopology hA hD w
      (continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC x) =
      continuousH1Cup C U D (characterDualEvaluation C χ)
        (characterDualEvaluation_equivariant C χ) continuous_of_discreteTopology hC hU hD x
        (continuousCoefficientInvariantConnectingMap U V W
          (characterDualCoefficientMap B C χ ψ)
          (characterDualCoefficientMap_injective B C χ ψ hψ)
          (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
          (characterDualCoefficientMap A B χ φ)
          (characterDualCoefficientMap_surjective A B χ φ hφ)
          (characterDualCoefficientMap_equivariant A B χ φ hφρ)
          (characterDualCoefficientSequence_exact A B C χ φ ψ hExact) hU hV w) := by
  exact continuousConnectingCup_adjunction A B C
    (characterDualCoefficientRep C χ) (characterDualCoefficientRep B χ)
    (characterDualCoefficientRep A χ) (coefficientCharacterRep χ)
    φ hφ hφρ ψ hψ hψρ hExact
    (characterDualCoefficientMap B C χ ψ)
    (characterDualCoefficientMap_injective B C χ ψ hψ)
    (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
    (characterDualCoefficientMap A B χ φ)
    (characterDualCoefficientMap_surjective A B χ φ hφ)
    (characterDualCoefficientMap_equivariant A B χ φ hφρ)
    (characterDualCoefficientSequence_exact A B C χ φ ψ hExact)
    (characterDualEvaluation A χ) (characterDualEvaluation B χ) (characterDualEvaluation C χ)
    (characterDualEvaluation_equivariant A χ) (characterDualEvaluation_equivariant B χ)
    (characterDualEvaluation_equivariant C χ)
    (characterDualEvaluation_precompose A B χ φ)
    (fun b u => (characterDualEvaluation_precompose B C χ ψ b u).symm)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    hA hB hC (finiteCharacterDualAction_continuous C χ hC hχ)
    (finiteCharacterDualAction_continuous B χ hB hχ)
    (coefficientCharacterAction_continuous χ hχ) x w

end
end Dubon2026
