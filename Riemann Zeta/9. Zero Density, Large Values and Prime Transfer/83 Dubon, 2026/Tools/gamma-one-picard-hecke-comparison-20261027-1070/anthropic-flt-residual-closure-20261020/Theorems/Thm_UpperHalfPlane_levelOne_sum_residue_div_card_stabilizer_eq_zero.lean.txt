import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero
    (ω : ℍ → ℂ) (c : ℍ → ℂ) (S : Finset ℍ)
    (hΓ : ∀ γ : SL(2, ℤ), ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∃ δ : ℝ, 0 < δ ∧ ω =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z)
    (hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ : SL(2, ℤ), γ • σ = τ)
    (hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ : SL(2, ℤ), γ • σ = σ' → σ = σ') :
    ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer SL(2, ℤ) σ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_levelOne_sum_residue_div_card_stabilizer_eq_zero.solution
