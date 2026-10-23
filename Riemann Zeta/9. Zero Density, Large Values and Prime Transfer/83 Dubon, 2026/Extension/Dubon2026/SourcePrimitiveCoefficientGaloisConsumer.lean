import Dubon2026.SourceRankTwoCoefficientSpecialization

/-! DUB-17/18 -> primitive specialization -> consume together the
continuous rank-two Hecke realization and its prescribed continuous
coefficient character. The conclusion retains the actual vector action,
all eigenvalues and the spanning property after coefficient change. -/
namespace Dubon2026
noncomputable section
open Matrix

theorem specialize_continuous_rankTwo_hecke
    {K T E F V G I : Type*} [CommRing K] [CommRing T] [CommRing E] [CommRing F]
    [Algebra K T] [Algebra K E] [Algebra ℚ F] [Algebra ℚ E]
    [TopologicalSpace T] [TopologicalSpace E] [TopologicalSpace G]
    [AddCommMonoid V] [Module K V] [Group G]
    (χ : I → T) (a : I → F) (u : I → Module.End K V) (r : G →* Module.End K V)
    (hr : ∃ (e : V ≃ₗ[K] (Fin 2 → T)) (ρ : G →* GeneralLinearGroup (Fin 2) T),
      (∀ i x, e (u i x) = fun j => χ i * e x j) ∧ Continuous ρ ∧
      ∀ g x, (ρ g).val *ᵥ e x = e (r g x))
    (hχ : ∃ (τ : F →ₐ[ℚ] E) (κ : T →ₐ[K] E), Continuous κ ∧ ∀ i, κ (χ i) = τ (a i)) :
    ∃ (τ : F →ₐ[ℚ] E) (π : V →ₗ[K] (Fin 2 → E))
      (ρ : G →* GeneralLinearGroup (Fin 2) E),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ i x, π (u i x) = fun j => τ (a i) * π x j) ∧
      ∀ g x, (ρ g).val *ᵥ π x = π (r g x) := by
  obtain ⟨e, ρ, hact, hρ, he⟩ := hr
  obtain ⟨τ, κ, hκ, hvals⟩ := hχ
  let π := (rankTwoCoefficientMap κ).comp e.toLinearMap
  refine ⟨τ, π, rankTwoCoefficientGaloisRep κ ρ,
    rankTwoCoefficientGaloisRep_continuous κ ρ hκ hρ,
    rankTwoCoefficientMap_span κ e, ?_, ?_⟩
  · intro i x
    exact (congrArg (rankTwoCoefficientMap κ) (hact i x)).trans
      ((rankTwoCoefficientMap_smul κ _ (e x)).trans
        (congrArg (fun c : E => fun j => c * π x j) (hvals i)))
  · intro g x
    exact (rankTwoCoefficientGaloisRep_action κ ρ g (e x)).trans
      (congrArg (rankTwoCoefficientMap κ) (he g x))

end
end Dubon2026
