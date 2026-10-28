import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_invariant_untwist_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Φ : ℂ → ℂ,
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        Φ =ᶠ[𝓝 (τ : ℂ)] fun z =>
          (z - τ) ^ ((meromorphicOrderAt (fun w : ℂ => F (ofComplex w)) (τ : ℂ)).untop₀ : ℤ) *
            Ψ z) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) ∧
      (∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
        fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0)) ∧
      (∀ᵐ z : ℂ, 0 < z.im → Φ z ≠ 0 ∧ DifferentiableAt ℝ Φ z ∧
        fderiv ℝ Φ z 1 = Φ z *
          (deriv (fun w : ℂ => F (ofComplex w)) z / F (ofComplex z) -
            2 * Real.pi * Complex.I * ((k (ofComplex z)).re : ℂ)) ∧
        fderiv ℝ Φ z Complex.I = Φ z *
          (Complex.I * (deriv (fun w : ℂ => F (ofComplex w)) z / F (ofComplex z)) +
            2 * Real.pi * Complex.I * ((k (ofComplex z)).im : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp.solution
