import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant.solution
