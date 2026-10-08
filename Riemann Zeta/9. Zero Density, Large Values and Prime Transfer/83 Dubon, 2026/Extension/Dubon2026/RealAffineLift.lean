import Dubon2026.RealWhittakerNormalization

/-! # Actual affine matrices and their original real-group lift factors -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The actual affine determinant-one matrix associated to x+iy. -/
def realAffineMatrix (x : ℝ) {y : ℝ} (hy : 0 < y) : SL(2, ℝ) :=
  (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).toSL2R

/-- The lower-row denominator of the actual affine matrix is independent of the upper-half-plane point. -/
theorem realAffineMatrix_denom (x : ℝ) {y : ℝ} (hy : 0 < y) (z : ℍ) :
    denom (mapGL ℝ (realAffineMatrix x hy)) z = ((Real.sqrt y : ℝ) : ℂ)⁻¹ := by
  simp [realAffineMatrix, denom, UpperHalfPlane.toSL2R, mapGL,
    Matrix.SpecialLinearGroup.toGL]

/-- The genuine affine group element acts by z ↦ yz+x. -/
theorem realAffineMatrix_smul (x : ℝ) {y : ℝ} (hy : 0 < y) (z : ℍ) :
    ((realAffineMatrix x hy • z : ℍ) : ℂ) = (y : ℂ) * z + x := by
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hs2 : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  rw [coe_specialLinearGroup_apply]
  simp [realAffineMatrix, UpperHalfPlane.toSL2R]
  field_simp [hs]
  linear_combination (z : ℂ) * hs2

/-- The actual affine slash factor has the exact half-weight normalization. -/
theorem realAffineMatrix_slash_apply (k : ℤ) (f : ℍ → ℂ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) (z : ℍ) :
    (f ∣[k] (mapGL ℝ (realAffineMatrix x hy))) z =
      (((y ^ ((k : ℝ) / 2) : ℝ)) : ℂ) * f (realAffineMatrix x hy • z) := by
  have hd := realAffineMatrix_denom x hy z
  simp only [ModularForm.slash_apply, det_mapGL, Units.val_one, abs_one,
    one_zpow, Complex.ofReal_one, mul_one]
  rw [hd, inv_zpow, zpow_neg, inv_inv, sqrt_zpow_eq_half_weight k hy]
  simp [UpperHalfPlane.σ, MulAction.compHom_smul_def, mul_comm]

/-- Left translation by an actual affine matrix gives the original affine slash transform. -/
theorem realWeightLift_affine (k : ℤ) (f : ℍ → ℂ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) (g : SL(2, ℝ)) :
    realWeightLift k f (realAffineMatrix x hy * g) =
      (((y ^ ((k : ℝ) / 2) : ℝ)) : ℂ) *
        f (realAffineMatrix x hy • (g • I)) * denom (mapGL ℝ g) I ^ (-k) := by
  rw [realWeightLift_mul, realWeightLift_apply, realAffineMatrix_slash_apply]

end
end Dubon2026
