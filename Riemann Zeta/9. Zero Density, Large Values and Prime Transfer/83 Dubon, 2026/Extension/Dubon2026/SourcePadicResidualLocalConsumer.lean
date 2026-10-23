import Dubon2026.SourcePadicResidualRealizationConsumer

/-! DUB-17/18 -> actual residual association -> unpack the constructed
local coefficient structure before instantiating the concrete Fourier
field. This performs the local-field and residual assembly once over an
abstract field and retains all source equations without extra premises. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open Matrix
variable (p : ℕ) [Fact p.Prime]
variable (E : Type) [Field E] [Algebra ℚ_[p] E] [Algebra ℚ E]
variable {F V G I : Type*} [Field F] [Algebra ℚ F]
variable [AddCommGroup V] [Module ℚ_[p] V]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
private local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

theorem padic_source_local_integral_residual_realization
    (a : I → F) (u : I → Module.End ℚ_[p] V) (η : G →* Module.End ℚ_[p] V)
    (hsrc : ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) ∧
      ∃ (τ : F →ₐ[ℚ] E) (π : V →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : G →* GeneralLinearGroup (Fin 2) E) (L : Submodule 𝒪[E] (Fin 2 → E)),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ i x, π (u i x) = (fun j => τ (a i) * π x j)) ∧
      (∀ g x, (ρ g).val *ᵥ π x = π (η g x)) ∧
      Submodule.span E (L : Set (Fin 2 → E)) = ⊤ ∧
      Module.Free 𝒪[E] L ∧ Module.Finite 𝒪[E] L ∧ Module.finrank 𝒪[E] L = 2 ∧
      ∀ g v, v ∈ L → (ρ g).val *ᵥ v ∈ L) :
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      letI : TopologicalSpace 𝓀[E] :=
        inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) ∧
      Finite 𝓀[E] ∧ DiscreteTopology 𝓀[E] ∧ CharP 𝓀[E] p ∧
      ∃ (τ : F →ₐ[ℚ] E) (π : V →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : G →* GeneralLinearGroup (Fin 2) E)
        (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
        (ρint : G →* GeneralLinearGroup (Fin 2) 𝒪[E])
        (ρres : G →* GeneralLinearGroup (Fin 2) 𝓀[E]),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ i x, π (u i x) = (fun j => τ (a i) * π x j)) ∧
        (∀ g x, (ρ g).val *ᵥ π x = π (η g x)) ∧
        Continuous ρint ∧ Continuous ρres ∧
        (∀ g i j, (ρres g).val i j = IsLocalRing.residue 𝒪[E] ((ρint g).val i j)) ∧
        ∀ g v, (ρint g).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ g).val *ᵥ v) := by
  obtain ⟨t, v, ha, hl, hm, hv, h⟩ := hsrc
  letI := t
  letI := v
  letI := ha
  letI := hl
  letI := hm
  letI := hv
  exact ⟨t, v, ha, hl, hm, hv, padic_source_integral_residual_realization p E a u η h⟩

end
end Dubon2026
