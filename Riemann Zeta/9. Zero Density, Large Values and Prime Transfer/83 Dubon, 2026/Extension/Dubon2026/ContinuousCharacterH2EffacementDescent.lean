import Dubon2026.ContinuousCharacterH2DualInvariantPairing
import Dubon2026.LowDegreeH2AnnihilatorDescent
import Dubon2026.ContinuousConnectingH1Exactness
import Dubon2026.ContinuousConnectingH2Exactness
import Dubon2026.ContinuousInvariantConnectingExactness

/-! # Detect original H2 classes through an actual coefficient effacement

The original continuous exactness and cup adjunction discharge every diagram
edge in the low-degree H2 argument. Proved local H1 perfectness will supply
the two remaining coefficient-pairing inputs, while actual finite effacement
supplies the coefficient sequence. This serves DUB-17's local H0/H2 endpoint.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep.{0} k G) [Finite B] [Finite C]
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
  (e₂ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k)

include hφ hψ hψρ hExact in
/-- Every genuinely effaced original H2 class annihilating all actual dual
invariants is zero, once the two narrower original H1 duality inputs hold. -/
theorem continuousCharacterH2_left_zero_of_effacement
    (hQ : Function.Surjective ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap))
    (hR : Function.Injective ((continuousCharacterDualH1Cup C χ hχ hC).compr₂ e₂.toLinearMap))
    (x : ContinuousRepresentationH2 A hA)
    (hx : continuousCoefficientH2Map A B φ continuous_of_discreteTopology hφρ hA hB x = 0)
    (hann : ∀ w, e₂ (continuousCharacterH2DualInvariantPairing A χ hχ hA x w) = 0) : x = 0 := by
  obtain ⟨u, rfl⟩ := (continuousConnectingH2_mem_range_iff A B C φ hφ
    continuous_of_discreteTopology hφρ ψ hψ hψρ hExact hA hB hC x).mpr hx
  let U := characterDualCoefficientRep C χ
  let V := characterDualCoefficientRep B χ
  let W := characterDualCoefficientRep A χ
  let hU := finiteCharacterDualAction_continuous C χ hC hχ
  let hV := finiteCharacterDualAction_continuous B χ hB hχ
  let ι := characterDualCoefficientMap B C χ ψ
  let hι := characterDualCoefficientMap_injective B C χ ψ hψ
  let hιρ := characterDualCoefficientMap_equivariant B C χ ψ hψρ
  let π := characterDualCoefficientMap A B χ φ
  let hπ := characterDualCoefficientMap_surjective A B χ φ hφ
  let hπρ := characterDualCoefficientMap_equivariant A B χ φ hφρ
  let hD := characterDualCoefficientSequence_exact A B C χ φ ψ hExact
  let j := continuousCoefficientH1Map B C ψ continuous_of_discreteTopology hψρ hB hC
  let δ := continuousCoefficientConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB hC
  let jD := continuousCoefficientH1Map U V ι continuous_of_discreteTopology hιρ hU hV
  let δD := continuousCoefficientInvariantConnectingMap U V W ι hι hιρ π hπ hπρ hD hU hV
  apply lowDegreeH2_connecting_left_zero
    ((continuousCharacterH2DualInvariantPairing A χ hχ hA).compr₂ e₂.toLinearMap)
    ((continuousCharacterDualH1Cup B χ hχ hB).compr₂ e₂.toLinearMap)
    ((continuousCharacterDualH1Cup C χ hχ hC).compr₂ e₂.toLinearMap)
    j δ jD δD ?_ ?_ ?_ ?_ hQ hR u hann
  · exact continuousConnectingH1_range_eq_ker A B C φ hφ continuous_of_discreteTopology
      hφρ ψ hψ hψρ hExact hA hB hC
  · ext z
    exact continuousInvariantConnecting_mem_range_iff U V W ι hι hιρ π hπ hπρ hD hU hV
      continuous_of_discreteTopology z
  · intro b z
    exact congrArg e₂ (continuousCharacterDualH1Cup_naturality B χ hχ hB C hC ψ hψρ b z)
  · intro v w
    exact congrArg e₂ (finiteCharacterDualConnecting_adjunction A B C χ hχ
      φ hφ hφρ ψ hψ hψρ hExact hA hB hC v w)

end
end Dubon2026
