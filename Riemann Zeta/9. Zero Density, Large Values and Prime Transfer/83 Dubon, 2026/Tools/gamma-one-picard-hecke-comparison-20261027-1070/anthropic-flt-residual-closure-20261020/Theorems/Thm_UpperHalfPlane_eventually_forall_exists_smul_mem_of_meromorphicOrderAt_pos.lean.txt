import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {U : Set ℍ} (hU : IsOpen U)
    (hfib : ∀ τ : ℍ, 0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t₀) (τ : ℂ) →
      ∃ γ ∈ Γ, γ • τ ∈ U) :
    ∀ᶠ t in 𝓝 t₀, ∀ τ : ℍ,
      0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) →
        ∃ γ ∈ Γ, γ • τ ∈ U := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_eventually_forall_exists_smul_mem_of_meromorphicOrderAt_pos.solution
