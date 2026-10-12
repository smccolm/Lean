import Dubon2026.FiniteCharacterDualInvariantAdjunction
import Dubon2026.ContinuousCharacterDualH2Naturality
import Dubon2026.ContinuousInvariantConnectingExactness
import Dubon2026.ContinuousConnectingH2Exactness
import Dubon2026.LowDegreeDualityAnnihilatorDescent

/-! # Descent through the original continuous low-degree sequence

All three exactness edges and both naturality identities are supplied by
proved original continuous cohomology. The signed cup adjunction supplies
the last edge. Only the middle-module pairings and quotient endpoint
surjectivity remain, to be discharged by the constructed local induced
module and the proved arbitrary invariant-functional realization for DUB-17.
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

variable (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
  (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)

include hφ hψ hφρ hψρ hExact in
/-- The actual original H1 pairing is injective when the original middle
H1 and H2 endpoint maps are injective and the quotient H2 endpoint is
surjective. Exactness and all cohomological adjunctions are derived. -/
theorem continuousCharacterDualH1_left_injective_of_exact
    (h₁ : Function.Injective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₂ : Function.Injective ((continuousCharacterDualH2InvariantPairing B χ hχ hB).compr₂ e₂.toLinearMap))
    (h₃ : Function.Surjective ((continuousCharacterDualH2InvariantPairing C χ hχ hC).compr₂ e₂.toLinearMap)) :
    Function.Injective ((continuousCharacterDualH1Cup A χ hχ hA).compr₂ e₂.toLinearMap) := by
  let U := characterDualCoefficientRep C χ
  let V := characterDualCoefficientRep B χ
  let W := characterDualCoefficientRep A χ
  let hU := finiteCharacterDualAction_continuous C χ hC hχ
  let hV := finiteCharacterDualAction_continuous B χ hB hχ
  let hW := finiteCharacterDualAction_continuous A χ hA hχ
  let ι := characterDualCoefficientMap B C χ ψ
  let hι := characterDualCoefficientMap_injective B C χ ψ hψ
  let hιρ := characterDualCoefficientMap_equivariant B C χ ψ hψρ
  let π := characterDualCoefficientMap A B χ φ
  let hπ := characterDualCoefficientMap_surjective A B χ φ hφ
  let hπρ := characterDualCoefficientMap_equivariant A B χ φ hφρ
  let hD := characterDualCoefficientSequence_exact A B C χ φ ψ hExact
  let i := continuousCoefficientH1Map A B φ continuous_of_discreteTopology hφρ hA hB
  let iD := continuousCoefficientH1Map V W π continuous_of_discreteTopology hπρ hV hW
  let δ := continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
  let j := coefficientInvariantLinearMap B C ψ hψρ
  let δD := continuousCoefficientConnectingMap U V W ι hι hιρ π hπ hπρ hD hU hV hW
  let jD := continuousCoefficientH2Map U V ι continuous_of_discreteTopology hιρ hU hV
  apply lowDegreeDuality_left_injective
    ((continuousCharacterDualH1Cup A χ hχ hA).compr₂ e₂.toLinearMap)
    ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap)
    ((continuousCharacterDualH2InvariantPairing C χ hχ hC).compr₂ e₂.toLinearMap)
    ((continuousCharacterDualH2InvariantPairing B χ hχ hB).compr₂ e₂.toLinearMap)
    i iD δ j δD jD ?_ ?_ ?_ ?_ ?_ ?_ h₁ h₂ h₃
  · ext x
    exact continuousInvariantConnecting_mem_range_iff A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      continuous_of_discreteTopology x
  · ext w
    change (∃ b, j b = w) ↔ δ w = 0
    rw [continuousInvariantConnecting_eq_zero_iff A B C φ hφ hφρ ψ hψ hψρ hExact hA hB]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, congrArg Subtype.val hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, Subtype.ext hb⟩
  · exact continuousConnectingH2_range_eq_ker U V W ι hι continuous_of_discreteTopology hιρ π hπ hπρ hD hU hV hW
  · intro x y
    exact congrArg e₂ (continuousCharacterDualH1Cup_naturality A χ hχ hA B hB φ hφρ x y).symm
  · intro z b
    exact congrArg e₂ (continuousCharacterDualH2InvariantPairing_naturality B C ψ hψρ χ hχ hB hC z b)
  · intro y w
    exact (congrArg e₂ (finiteCharacterDualInvariantConnecting_adjunction A B C χ hχ φ hφ hφρ
      ψ hψ hψρ hExact hA hB hC y w)).trans (map_neg e₂ _)

end
end Dubon2026
