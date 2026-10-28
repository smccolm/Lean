import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups ComplexConjugate

theorem ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N),
        UpperHalfPlane.petersson 2 k g τ) =
      Complex.I / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γT q) k) *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 4 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γS q) k) *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.solution
