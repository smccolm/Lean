import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
    (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
    (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
    (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
    (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)
    (g : CuspForm Γ 2) (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    IntegrableOn (fun τ : ℍ => (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2))
      (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) ∧
    (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2)) =
      1 / (2 * Complex.I) *
        (Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
          1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
              (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.solution
