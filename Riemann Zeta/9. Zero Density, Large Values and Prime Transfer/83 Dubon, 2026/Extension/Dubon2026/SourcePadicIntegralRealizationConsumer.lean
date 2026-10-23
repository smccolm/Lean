import Dubon2026.SourcePadicSpecializationLattice
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units

/-! DUB-17/18 -> actual primitive residual association -> assemble the
local coefficient topology and stable integral lattice with the original
Fourier eigenvalues and Galois intertwining. The input is a rational
specialization; no integral lattice, freeness or residual representation
is assumed. The actual primitive Tate consumer supplies this input. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct ValuativeRel
open Matrix
variable (p : ℕ) [Fact p.Prime]
variable (E : Type) [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
variable [Algebra ℚ E]
variable {F M G I : Type*} [Field F] [Algebra ℚ F]
variable [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
variable [Group G] [TopologicalSpace G]

theorem padic_realization_with_stable_lattice
    (a : I → F) (u : I → Module.End ℤ_[p] M) (η : G →* Module.End ℤ_[p] M)
    (hsrc : letI : TopologicalSpace E := moduleTopology ℚ_[p] E
      ∃ (τ : F →ₐ[ℚ] E) (π : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : G →* GeneralLinearGroup (Fin 2) E),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ i z, π ((u i).baseChange ℚ_[p] z) = (fun j => τ (a i) * π z j)) ∧
        ∀ g z, (ρ g).val *ᵥ π z = π ((η g).baseChange ℚ_[p] z)) :
    letI : ValuativeRel ℚ_[p] :=
      ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) ∧
      ∃ (τ : F →ₐ[ℚ] E) (π : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : G →* GeneralLinearGroup (Fin 2) E) (L : Submodule 𝒪[E] (Fin 2 → E)),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ i z, π ((u i).baseChange ℚ_[p] z) = (fun j => τ (a i) * π z j)) ∧
        (∀ g z, (ρ g).val *ᵥ π z = π ((η g).baseChange ℚ_[p] z)) ∧
        Submodule.span E (L : Set (Fin 2 → E)) = ⊤ ∧
        Module.Free 𝒪[E] L ∧ Module.Finite 𝒪[E] L ∧ Module.finrank 𝒪[E] L = 2 ∧
        ∀ g v, v ∈ L → (ρ g).val *ᵥ v ∈ L := by
  letI : ValuativeRel ℚ_[p] :=
    ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
  obtain ⟨t, v, ha, hl, hm, hv⟩ := padicFiniteCoefficient_local_structure p E
  letI := t
  letI := v
  letI := ha
  letI := hl
  letI := hm
  letI := hv
  have ht := eq_moduleTopology ℚ_[p] E
  obtain ⟨τ, π, ρ, hc, hs, hu, he⟩ := hsrc
  have hc' : Continuous ρ := by
    exact ht.symm ▸ hc
  obtain ⟨L, _, hspan, hfree, hfinite, hrank, hstable⟩ :=
    padicSpecialization_stable_lattice p E π hs η ρ he
  exact ⟨t, v, ha, hl, hm, hv, τ, π, ρ, L, hc', hs, hu, he,
    hspan, hfree, hfinite, hrank, hstable⟩

end
end Dubon2026
