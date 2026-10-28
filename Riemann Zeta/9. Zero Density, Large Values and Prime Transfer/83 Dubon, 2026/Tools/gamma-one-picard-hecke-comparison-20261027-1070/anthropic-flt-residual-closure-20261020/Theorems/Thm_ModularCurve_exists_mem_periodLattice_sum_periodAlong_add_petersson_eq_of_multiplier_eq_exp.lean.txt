import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp
attribute [-instance] FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ) :
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (∑ s ∈ S, (2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ)) *
              ModularCurve.periodAlong N UpperHalfPlane.I s g) +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) +
          Λ g = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp.solution
