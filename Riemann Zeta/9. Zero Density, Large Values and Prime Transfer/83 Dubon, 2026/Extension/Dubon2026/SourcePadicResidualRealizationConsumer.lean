import Dubon2026.SourceStableLatticeResidualRealization
import Dubon2026.SourcePadicResidueCharacteristic

/-! DUB-17/18 -> modular residual association -> assemble the actual
finite characteristic-p reduction. Keep the original specialization,
prime eigenvalues and Galois intertwining, and derive continuous integral
and residual representations with exact coefficient and basis comparison.
Only the earlier rational realization and its constructed lattice enter. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open Matrix
variable (p : ℕ) [Fact p.Prime]
variable (E : Type) [Field E] [Algebra ℚ_[p] E] [Algebra ℚ E]
variable [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E]
variable [IsNonarchimedeanLocalField E]
private local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
private local instance : TopologicalSpace 𝓀[E] :=
  inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))
variable [(ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E)]
variable {F V G I : Type*} [Field F] [Algebra ℚ F]
variable [AddCommGroup V] [Module ℚ_[p] V]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem padic_source_integral_residual_realization
    (a : I → F) (u : I → Module.End ℚ_[p] V) (η : G →* Module.End ℚ_[p] V)
    (hsrc : ∃ (τ : F →ₐ[ℚ] E) (π : V →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : G →* GeneralLinearGroup (Fin 2) E) (L : Submodule 𝒪[E] (Fin 2 → E)),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ i x, π (u i x) = (fun j => τ (a i) * π x j)) ∧
      (∀ g x, (ρ g).val *ᵥ π x = π (η g x)) ∧
      Submodule.span E (L : Set (Fin 2 → E)) = ⊤ ∧
      Module.Free 𝒪[E] L ∧ Module.Finite 𝒪[E] L ∧ Module.finrank 𝒪[E] L = 2 ∧
      ∀ g v, v ∈ L → (ρ g).val *ᵥ v ∈ L) :
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
  obtain ⟨τ, π, ρ, L, hc, hs, hu, he, hspan, hfree, hfinite, hrank, hL⟩ := hsrc
  obtain ⟨e, ρint, ρres, hci, hcr, hres, hfield⟩ :=
    stableLattice_integral_residual_realization ρ hc L hspan hfree hfinite hrank hL
  exact ⟨(localCoefficientResidue_finite_discrete E).1,
    (localCoefficientResidue_finite_discrete E).2, padicCoefficientResidue_charP p E,
    τ, π, ρ, e, ρint, ρres, hc, hs, hu, he, hci, hcr, hres, hfield⟩

end
end Dubon2026
