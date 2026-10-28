import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp
attribute [-instance] FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

open Classical in

theorem ModularCurve.exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp.solution
