import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_exists_residue_cuspForm_div_sub

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.exists_residue_cuspForm_div_sub
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ)
    (hsimple : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≤ 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ c : ℍ → ℂ,
      (∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ),
          f (ofComplex z) / (F (ofComplex z) - t) = c τ / (z - τ) + g z) ∧
      (∀ γ ∈ Γ, ∀ τ : ℍ, c (γ • τ) = c τ) ∧
      (∀ τ : ℍ, c τ ≠ 0 →
        0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)) ∧
      ∀ S : Finset ℍ, (∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ) →
        (∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') →
        ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_exists_residue_cuspForm_div_sub.solution
