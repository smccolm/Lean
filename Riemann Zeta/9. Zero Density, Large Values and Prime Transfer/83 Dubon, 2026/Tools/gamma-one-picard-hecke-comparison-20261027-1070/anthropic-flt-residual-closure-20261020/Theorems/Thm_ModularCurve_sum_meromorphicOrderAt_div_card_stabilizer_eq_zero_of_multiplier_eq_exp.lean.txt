import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

p2m_open "UpperHalfPlane~sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant"
open scoped MatrixGroups Topology

theorem ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp
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
    ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ)
      = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp.solution
