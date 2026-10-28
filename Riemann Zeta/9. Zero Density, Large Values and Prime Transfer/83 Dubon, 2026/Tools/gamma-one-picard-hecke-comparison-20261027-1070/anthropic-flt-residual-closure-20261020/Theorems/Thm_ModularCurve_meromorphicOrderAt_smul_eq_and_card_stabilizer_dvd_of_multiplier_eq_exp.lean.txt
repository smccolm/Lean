import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ) :
    (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
    (∀ (τ : ℍ) (n : ℤ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) →
        (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) ∣ 2 * n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp.solution
