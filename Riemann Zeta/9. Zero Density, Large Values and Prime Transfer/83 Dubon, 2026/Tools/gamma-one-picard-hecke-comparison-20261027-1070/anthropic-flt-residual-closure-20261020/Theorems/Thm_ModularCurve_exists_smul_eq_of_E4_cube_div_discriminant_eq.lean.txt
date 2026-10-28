import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq
attribute [-simp] PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.solution
