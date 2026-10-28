import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.solution
