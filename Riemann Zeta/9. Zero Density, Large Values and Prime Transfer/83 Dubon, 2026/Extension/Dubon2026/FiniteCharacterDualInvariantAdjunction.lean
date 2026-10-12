import Dubon2026.ContinuousCharacterDualH2Pairing
import Dubon2026.ContinuousCupSkewSymmetry

/-! # The signed original H0/H1 character-dual adjunction

Apply the proved connecting identity to the original reversed dual sequence,
then use genuine continuous cup skew-symmetry. This is the missing signed
edge in the direct finite-module H1 annihilator proof serving DUB-17.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] characterDualSequenceContinuousSMul

variable (A B C : Rep.{0} k G)
  [Finite A] [Finite B] [Finite C]
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

/-- The actual dual H1-to-H2 connecting map is adjoint, with its proved
negative sign, to the original invariant-to-H1 connecting map. -/
theorem finiteCharacterDualInvariantConnecting_adjunction
    (y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)) (w : C.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing C χ hχ hC
      (continuousCoefficientConnectingMap
        (characterDualCoefficientRep C χ) (characterDualCoefficientRep B χ)
        (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap B C χ ψ)
        (characterDualCoefficientMap_injective B C χ ψ hψ)
        (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
        (characterDualCoefficientMap A B χ φ)
        (characterDualCoefficientMap_surjective A B χ φ hφ)
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (characterDualCoefficientSequence_exact A B C χ φ ψ hExact)
        (finiteCharacterDualAction_continuous C χ hC hχ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) y) w =
      -continuousCharacterDualH1Cup A χ hχ hA
        (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB w) y := by
  have ha := continuousConnectingCup_adjunction
    (characterDualCoefficientRep C χ) (characterDualCoefficientRep B χ)
    (characterDualCoefficientRep A χ) A B C (coefficientCharacterRep χ)
    (characterDualCoefficientMap B C χ ψ)
    (characterDualCoefficientMap_injective B C χ ψ hψ)
    (characterDualCoefficientMap_equivariant B C χ ψ hψρ)
    (characterDualCoefficientMap A B χ φ)
    (characterDualCoefficientMap_surjective A B χ φ hφ)
    (characterDualCoefficientMap_equivariant A B χ φ hφρ)
    (characterDualCoefficientSequence_exact A B C χ φ ψ hExact)
    φ hφ hφρ ψ hψ hψρ hExact
    (characterDualEvaluation C χ).flip (characterDualEvaluation B χ).flip (characterDualEvaluation A χ).flip
    (fun g u c => characterDualEvaluation_equivariant C χ g c u)
    (fun g v b => characterDualEvaluation_equivariant B χ g b v)
    (fun g z a => characterDualEvaluation_equivariant A χ g a z)
    (fun u b => (characterDualEvaluation_precompose B C χ ψ b u).symm)
    (fun v a => characterDualEvaluation_precompose A B χ φ a v)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (finiteCharacterDualAction_continuous C χ hC hχ)
    (finiteCharacterDualAction_continuous B χ hB hχ)
    (finiteCharacterDualAction_continuous A χ hA hχ) hA hB
    (coefficientCharacterAction_continuous χ hχ) y w
  exact ha.trans (continuousH1Cup_skew (characterDualCoefficientRep A χ) A
    (coefficientCharacterRep χ) (characterDualEvaluation A χ).flip
    (fun g u a => characterDualEvaluation_equivariant A χ g a u)
    continuous_of_discreteTopology (finiteCharacterDualAction_continuous A χ hA hχ) hA
    (coefficientCharacterAction_continuous χ hχ) y
    (continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB w))

end
end Dubon2026
