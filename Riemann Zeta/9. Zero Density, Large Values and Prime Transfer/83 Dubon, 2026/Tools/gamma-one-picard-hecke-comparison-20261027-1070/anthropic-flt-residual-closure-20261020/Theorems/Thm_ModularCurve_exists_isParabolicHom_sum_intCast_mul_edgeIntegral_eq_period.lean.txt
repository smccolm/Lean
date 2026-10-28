import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
attribute [-instance] HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (δ : CongruenceSubgroup.Gamma0 N) :
    ∃ φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ ∧
      ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
        (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          ModularCurve.period N δ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.solution
