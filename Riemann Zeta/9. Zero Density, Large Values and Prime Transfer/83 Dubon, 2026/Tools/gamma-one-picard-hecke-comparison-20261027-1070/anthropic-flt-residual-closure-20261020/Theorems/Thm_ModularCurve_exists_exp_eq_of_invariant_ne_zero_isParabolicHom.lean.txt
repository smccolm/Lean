import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom

open UpperHalfPlane Filter
open scoped MatrixGroups Topology Real

theorem ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom
    (Γ : Subgroup SL(2, ℤ)) (Φ : ℂ → ℂ)
    (hΦ : ∀ τ : ℍ, ContDiffAt ℝ 1 Φ τ) (hne : ∀ τ : ℍ, Φ τ ≠ 0)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) :
    ∃ (L : ℂ → ℂ) (m : Additive Γ →+ ℤ),
      ModularCurve.Period.IsParabolicHom Γ m ∧
      (∀ τ : ℍ, ContDiffAt ℝ 1 L τ) ∧
      (∀ τ : ℍ, HasFDerivAt L ((Φ τ)⁻¹ • fderiv ℝ Φ τ) τ) ∧
      (∀ τ : ℍ, Complex.exp (L τ) = Φ τ) ∧
      (∀ (γ : Γ) (τ : ℍ), L (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        L τ + 2 * π * Complex.I * (m (Additive.ofMul γ) : ℂ)) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, Tendsto (fun τ : ℍ => L ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.solution
