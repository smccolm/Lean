import Dubon2026.ContinuousRepresentationCocycles

/-! The algebraic kernel-translation step in DUB-17 dual Selmer detection.
An invariant linear functional separates a cocycle value from the relevant
coboundary range. A translate by an element acting trivially on coefficients
then supplies a detecting element in the same prescribed subgroup. This is
the dimension-independent algebraic part of the auxiliary-prime source
decomposition; existence of the kernel value and invariant functional remains
an arithmetic residual-image obligation. -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  (A : Rep R G) (c : groupCohomology.cocycles₁ A)

/-- A functional fixed by the chosen action annihilates its coboundary
range, so a nonzero value of that functional proves nonmembership. -/
theorem cocycle_value_notMem_range_of_fixed_functional
    (g τ : G) (ℓ : A →ₗ[R] R)
    (hℓ : ∀ x : A, ℓ (A.ρ g x) = ℓ x) (hc : ℓ (c τ) ≠ 0) :
    c τ ∉ LinearMap.range (A.ρ g - 1) := by
  rintro ⟨x, hx⟩
  apply hc
  rw [← hx]
  change ℓ (A.ρ g x - x) = 0
  rw [map_sub, hℓ, sub_self]

/-- Either the original element or its translate by an actual coefficient
kernel element detects the cocycle. Both remain in the specified subgroup;
the exact two possibilities are retained for residual-image regularity. -/
theorem cocycle_exists_detecting_kernel_translate
    (H : Subgroup G) (g τ : G) (hg : g ∈ H) (hτ : τ ∈ H)
    (hρτ : A.ρ τ = 1) (hcτ : c τ ∉ LinearMap.range (A.ρ g - 1)) :
    ∃ σ : G, σ ∈ H ∧ (σ = g ∨ σ = τ * g) ∧
      c σ ∉ LinearMap.range (A.ρ σ - 1) := by
  classical
  by_cases hcg : c g ∈ LinearMap.range (A.ρ g - 1)
  · have hρ : A.ρ (τ * g) = A.ρ g := by rw [map_mul, hρτ, one_mul]
    have hc : c (τ * g) = c τ + c g := by
      have h : c (τ * g) = A.ρ τ (c g) + c τ :=
        (groupCohomology.mem_cocycles₁_iff _).mp c.property τ g
      rw [hρτ, Module.End.one_apply] at h
      exact h.trans (add_comm _ _)
    refine ⟨τ * g, H.mul_mem hτ hg, Or.inr rfl, ?_⟩
    rw [hρ, hc]
    intro hm
    exact hcτ (by simpa only [add_sub_cancel_right] using Submodule.sub_mem _ hm hcg)
  · exact ⟨g, hg, Or.inl rfl, hcg⟩

/-- The invariant functional supplies the non-coboundary premise of the
kernel-translation construction; that premise is not separately assumed. -/
theorem cocycle_exists_detecting_of_kernel_functional
    (H : Subgroup G) (g τ : G) (hg : g ∈ H) (hτ : τ ∈ H)
    (hρτ : A.ρ τ = 1) (ℓ : A →ₗ[R] R)
    (hℓ : ∀ x : A, ℓ (A.ρ g x) = ℓ x) (hc : ℓ (c τ) ≠ 0) :
    ∃ σ : G, σ ∈ H ∧ (σ = g ∨ σ = τ * g) ∧
      c σ ∉ LinearMap.range (A.ρ σ - 1) :=
  cocycle_exists_detecting_kernel_translate A c H g τ hg hτ hρτ
    (cocycle_value_notMem_range_of_fixed_functional A c g τ ℓ hℓ hc)

end
end Dubon2026
