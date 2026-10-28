import Dubon2026.SourceParabolicCosetPotentials

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> reciprocity -> integral periods of the winding sum.
Identify the actual edge corners with native rho. Native rho_sq replaces
the primary duplicated square-root algebra. No new elliptic point is defined. -/
namespace Dubon2026.SourceParabolicEdgePeriod
noncomputable section
open UpperHalfPlane Filter Complex
open scoped MatrixGroups Topology Real

theorem coe_rho : (ρ : ℂ) = -(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext <;> norm_num [UpperHalfPlane.ρ]

theorem coe_T_rho : ((ModularGroup.T • ρ : ℍ) : ℂ) = (ρ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem exp_two_pi_div_three :
    Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) = (ρ : ℂ) := by
  rw [coe_rho]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    simp
  · rw [Complex.exp_ofReal_mul_I_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
    simp

theorem exp_pi_div_three :
    Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) = ((ModularGroup.T • ρ : ℍ) : ℂ) := by
  rw [coe_T_rho, coe_rho]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
    simp
    ring
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    simp

theorem S_smul_rho : ModularGroup.S • ρ = ModularGroup.T • ρ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, coe_T_rho]
  change (-((ρ : ℍ) : ℂ))⁻¹ = _
  apply inv_eq_of_mul_eq_one_right
  linear_combination -UpperHalfPlane.ρ_sq

theorem S_smul_T_rho : ModularGroup.S • (ModularGroup.T • ρ) = ρ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  change (-(((ModularGroup.T • ρ : ℍ) : ℂ)))⁻¹ = _
  rw [coe_T_rho]
  apply inv_eq_of_mul_eq_one_right
  linear_combination -UpperHalfPlane.ρ_sq

theorem W_smul_rho : W • ρ = ρ := by
  rw [W, mul_smul, S_smul_rho, inv_smul_smul]

theorem im_T_inv_smul (w : ℍ) : (ModularGroup.T⁻¹ • w).im = w.im := by
  rw [show ModularGroup.T⁻¹ = ModularGroup.T ^ (-1 : ℤ) by simp, UpperHalfPlane.modular_T_zpow_smul,
    UpperHalfPlane.vadd_im]

theorem tendsto_T_inv_smul : Tendsto (fun w : ℍ => ModularGroup.T⁻¹ • w) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ (fun w : ℍ => ModularGroup.T⁻¹ • w) = UpperHalfPlane.im :=
    funext im_T_inv_smul
  rw [this]
  exact tendsto_comap

end
end Dubon2026.SourceParabolicEdgePeriod
