import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_eq_const_of_norm_multiplier_eq_one
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hF : DifferentiableOn ℂ (fun z : ℂ => F (ofComplex z)) {z : ℂ | 0 < z.im})
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ C : ℂ, ∀ τ : ℍ, F τ = C := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one.solution
