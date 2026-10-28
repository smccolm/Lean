import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
    (Γ : Subgroup SL(2, ℤ)) (m : ℍ → ℤ) (ω : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∃ (F : ℍ → ℂ) (χ : Γ → ℂ),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (m τ : WithTop ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue.solution
