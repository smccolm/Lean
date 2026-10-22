import Dubon2026.SourceAnalyticJTransformation

/-! DUB-17/18 -> numerical modular genus -> elliptic ramification ->
the exact analytic multiplicity of j at each upper-half-plane point.
The required derivative identity follows from native level-one dimension
and discriminant division. This avoids adding a general Ramanujan system
or elliptic-curve uniformization. Full modular orbit separation identifies
the two exceptional fibers with the actual elliptic-point stabilizers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular
local notation "Δ" => ModularForm.discriminant
theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I :=
  ModularGroup.stabilizer_I.mpr (by simp)

theorem TinvS_smul_ρ : (ModularGroup.T⁻¹ * ModularGroup.S) • ρ = ρ :=
  ModularGroup.stabilizer_ρ.mpr (by simp)

theorem E₆_I : E₆ UpperHalfPlane.I = 0 := by
  have h := E₆_smul ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I, ModularGroup.denom_S, UpperHalfPlane.coe_I] at h
  have hI6 : Complex.I ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast]
    calc Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
      _ = -1 := by rw [Complex.I_sq]; norm_num
  rw [hI6] at h
  linear_combination h / 2

theorem denom_TinvS_ρ : denom (↑(ModularGroup.T⁻¹ * ModularGroup.S) : GL (Fin 2) ℝ) ρ = (ρ : ℂ) := by
  rw [ModularGroup.denom_apply]
  have h10 : (ModularGroup.T⁻¹ * ModularGroup.S) 1 0 = 1 := by
    change ((ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv, ModularGroup.coe_S]
    simp
  have h11 : (ModularGroup.T⁻¹ * ModularGroup.S) 1 1 = 0 := by
    change ((ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv, ModularGroup.coe_S]
    simp
  rw [h10, h11]
  simp

theorem ρ_ne_one : (ρ : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [UpperHalfPlane.coe_im] at this
  simp at this
  exact ρ.im_pos.ne' this

theorem E₄_ρ : E₄ ρ = 0 := by
  have h := E₄_smul (ModularGroup.T⁻¹ * ModularGroup.S) ρ
  rw [TinvS_smul_ρ, denom_TinvS_ρ] at h
  have hρ4 : (ρ : ℂ) ^ (4 : ℤ) = (ρ : ℂ) := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    linear_combination ((ρ : ℂ) ^ 2 - ρ) * ρ_sq
  rw [hρ4] at h
  have : ((ρ : ℂ) - 1) * E₄ ρ = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) ρ_ne_one
  · exact h1

theorem E₄_I_ne_zero : E₄ UpperHalfPlane.I ≠ 0 := by
  intro h
  have hΔ := discriminant_ne_zero UpperHalfPlane.I
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, E₆_I] at hΔ
  norm_num at hΔ

theorem E₆_ρ_ne_zero : E₆ ρ ≠ 0 := by
  intro h
  have hΔ := discriminant_ne_zero ρ
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h, E₄_ρ] at hΔ
  norm_num at hΔ

theorem jf_ρ : jf ρ = 0 := by simp [jf, E₄_ρ]

theorem jf_I_ne_zero : jf UpperHalfPlane.I ≠ 0 :=
  div_ne_zero (pow_ne_zero _ E₄_I_ne_zero) (discriminant_ne_zero _)

theorem E₄_smul_eq_zero_iff (γ : SL(2, ℤ)) (τ : ℍ) : E₄ (γ • τ) = 0 ↔ E₄ τ = 0 := by
  rw [E₄_smul, mul_eq_zero, or_iff_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)

theorem E₆_smul_eq_zero_iff (γ : SL(2, ℤ)) (τ : ℍ) : E₆ (γ • τ) = 0 ↔ E₆ τ = 0 := by
  rw [E₆_smul, mul_eq_zero, or_iff_right]
  exact zpow_ne_zero _ (denom_ne_zero _ _)


end
end Dubon2026.SourceFunctionField.JMultiplicity
