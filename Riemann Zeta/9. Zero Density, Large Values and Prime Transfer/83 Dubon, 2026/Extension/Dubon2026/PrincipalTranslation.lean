import Dubon2026.PrincipalRescaledCoefficients

/-! # Literal translation operators on principal-level cusp forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
attribute [local instance] principalNormal

/-- Integral translation on actual principal-level cusp forms. -/
def principalTranslation (N : ℕ) (k : ℤ) (j : ℤ) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k :=
  normalCuspAction (Gamma N) k (ModularGroup.T ^ j)⁻¹

/-- The operator is literally f(z+j), with no residual slash factor. -/
theorem principalTranslation_apply (N : ℕ) (k : ℤ) (j : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (τ : ℍ) :
    principalTranslation N k j f τ = f ((j : ℝ) +ᵥ τ) := by
  change ((⇑f ∣[k] mapGL ℝ ((ModularGroup.T ^ j)⁻¹)⁻¹) τ) = _
  rw [inv_inv]
  change ((⇑f ∣[k] (ModularGroup.T ^ j)) τ) = _
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul]
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T_zpow, -map_zpow]

/-- An integral translate multiplies each actual Fourier coefficient by its exact phase. -/
theorem principalTranslation_coeff (N : ℕ) [NeZero N] (k : ℤ) (j : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (principalTranslation N k j f) n =
      principalCuspCoefficients f n * Function.Periodic.qParam N (j : ℂ) ^ n := by
  have hs : ∀ τ : ℍ, HasSum (fun m =>
      (principalCuspCoefficients f m * Function.Periodic.qParam N (j : ℂ) ^ m) •
        Function.Periodic.qParam N τ ^ m) (principalTranslation N k j f τ) := by
    intro τ
    rw [principalTranslation_apply]
    have h := principalCuspCoefficients_hasSum f ((j : ℝ) +ᵥ τ)
    simp only [coe_vadd, Complex.ofReal_intCast, qParam_add, mul_pow] at h
    convert h using 1
    funext m
    simp only [smul_eq_mul]
    ring1
  exact (ModularFormClass.qExpansion_coeff_unique
    (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) (by simp) hs n).symm

/-- The principal-level period gives exactly the identity operator for translation by N. -/
theorem principalTranslation_period (N : ℕ) (k : ℤ) : principalTranslation N k N = 1 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.coe_injective
  change (⇑f ∣[k] mapGL ℝ ((ModularGroup.T ^ (N : ℤ))⁻¹)⁻¹) = ⇑f
  rw [inv_inv]
  apply f.slash_action_eq'
  refine ⟨_, ?_, rfl⟩
  simpa only [Int.natAbs_natCast] using
    ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) (dvd_refl _)

/-- Integer translations compose by addition on the actual principal-level cusp forms. -/
theorem principalTranslation_add (N : ℕ) (k : ℤ) (i j : ℤ) :
    principalTranslation N k (i + j) = principalTranslation N k i * principalTranslation N k j := by
  apply LinearMap.ext
  intro f
  ext τ
  simp only [Module.End.mul_apply, principalTranslation_apply, Int.cast_add]
  rw [← add_vadd, add_comm (i : ℝ) (j : ℝ)]

end
end Dubon2026
