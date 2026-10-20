import Dubon2026.SourcePeriodCorrectionPolynomial

/-! Exact scalar slash action of the original dual period correction.
DUB-17/18 -> modular Galois association -> analytic H1 injectivity.
This identifies a native cohomological coboundary with the polynomial
correction in the already proved scalar Eichler transformation law.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup MvPolynomial MulOpposite UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The original right coefficient action transforms the Eichler kernel with its exact denominator. -/
theorem sourceEichlerBinaryForm_action (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    sourceModularBinaryFormRep ℂ n (op (g : Matrix (Fin 2) (Fin 2) ℤ))
        (sourceEichlerBinaryForm n (g • τ : UpperHalfPlane)) =
      ((denom g τ : ℂ)⁻¹) ^ n • sourceEichlerBinaryForm n (τ : ℂ) := by
  let a : ℂ := (g.val 0 0 : ℤ)
  let b : ℂ := (g.val 0 1 : ℤ)
  let c : ℂ := (g.val 1 0 : ℤ)
  let d : ℂ := (g.val 1 1 : ℤ)
  have hd : a * d - b * c = 1 := by
    have hg := g.property
    rw [Matrix.det_fin_two] at hg
    dsimp [a, b, c, d]
    exact_mod_cast hg
  have hj : c * (τ : ℂ) + d ≠ 0 := by
    simpa [c, d, denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using denom_ne_zero g τ
  have ht : ((g • τ : UpperHalfPlane) : ℂ) =
      (a * (τ : ℂ) + b) / (c * (τ : ℂ) + d) := by
    rw [coe_specialLinearGroup_apply]
    rfl
  have hden : (denom g τ : ℂ) = c * (τ : ℂ) + d := by
    simp [c, d, denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hp : (g • τ : UpperHalfPlane) * (c * (τ : ℂ) + d) =
      a * (τ : ℂ) + b := by
    rw [ht, div_mul_cancel₀ _ hj]
  have ha : a - (g • τ : UpperHalfPlane) * c = (c * (τ : ℂ) + d)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hj).2
    calc
      _ = a * (c * (τ : ℂ) + d) - c *
          ((g • τ : UpperHalfPlane) * (c * (τ : ℂ) + d)) := by ring
      _ = 1 := by
        rw [hp]
        linear_combination hd
  have hb : b - (g • τ : UpperHalfPlane) * d = -(τ : ℂ) * (c * (τ : ℂ) + d)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (eq_div_iff hj).2
    calc
      _ = b * (c * (τ : ℂ) + d) - d *
          ((g • τ : UpperHalfPlane) * (c * (τ : ℂ) + d)) := by ring
      _ = -(τ : ℂ) := by
        rw [hp]
        linear_combination -(τ : ℂ) * hd
  have hC (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
      matrixPolynomialAction M (C z) = C z := by
    simp [matrixPolynomialAction]
  apply Subtype.ext
  simp only [sourceModularBinaryFormRep_apply, sourceEichlerBinaryForm, map_pow,
    map_sub, map_mul, hC, matrixPolynomialAction_X,
    Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
    smul_eq_C_mul, Submodule.coe_smul]
  rw [← mul_pow]
  congr 1
  change C a * X 0 + C b * X 1 -
      C ((g • τ : UpperHalfPlane) : ℂ) * (C c * X 0 + C d * X 1) =
    C ((denom g τ : ℂ)⁻¹) * (X 0 - C (τ : ℂ) * X 1)
  rw [hden]
  calc
    C a * X (0 : Fin 2) + C b * X 1 -
        C ((g • τ : UpperHalfPlane) : ℂ) * (C c * X 0 + C d * X 1) =
        C (a - (g • τ : UpperHalfPlane) * c) * X 0 +
        C (b - (g • τ : UpperHalfPlane) * d) * X 1 := by
          simp only [map_sub, map_mul]
          ring
    _ = C ((c * (τ : ℂ) + d)⁻¹) * (X 0 - C (τ : ℂ) * X 1) := by
      rw [ha, hb]
      simp only [map_mul, map_neg]
      ring

/-- Scalar slashing of the actual correction is exactly the inverse dual coefficient action. -/
theorem sourcePeriodCorrectionPolynomial_slash {Γ : Subgroup SL(2, ℤ)} (n : ℕ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n)) (g : Γ) :
    (fun τ : UpperHalfPlane => (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ))
        ∣[-(n : ℤ)] g.val =
      fun τ : UpperHalfPlane =>
        (sourcePeriodCorrectionPolynomial n ((sourcePeriodDualRep Γ n).ρ g⁻¹ L)).eval (τ : ℂ) := by
  funext τ
  have he := congrArg (sourceModularBinaryFormSLRep ℂ n g.val)
    (sourceEichlerBinaryForm_action n g.val τ)
  rw [sourceModularBinaryFormSLRep_right_cancel, map_smul] at he
  simp only [ModularForm.SL_slash_apply, neg_neg, zpow_natCast,
    sourcePeriodCorrectionPolynomial_eval]
  rw [he, map_smul]
  simp only [smul_eq_mul, sourceModularBinaryFormSLRep_apply]
  rw [inv_pow]
  field_simp
  exact (sourcePeriodDualRep_apply g⁻¹ L (sourceEichlerBinaryForm n (τ : ℂ))).symm

end
end Dubon2026
