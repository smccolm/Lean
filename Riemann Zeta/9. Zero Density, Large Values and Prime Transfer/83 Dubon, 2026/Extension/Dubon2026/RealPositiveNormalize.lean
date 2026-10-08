import Dubon2026.RealProjectiveHilbertGenerator

/-! # Actual positive-determinant normalization into the real special linear group -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The actual positive square-root determinant of a genuine positive real matrix. -/
def realPositiveDetRoot (g : GL(2, ℝ)⁺) : ℝ :=
  Real.sqrt ((g.val : Matrix (Fin 2) (Fin 2) ℝ).det)

/-- The original determinant root is strictly positive. -/
theorem realPositiveDetRoot_pos (g : GL(2, ℝ)⁺) : 0 < realPositiveDetRoot g :=
  Real.sqrt_pos.mpr g.property

/-- Its actual square is precisely the original determinant. -/
theorem realPositiveDetRoot_sq (g : GL(2, ℝ)⁺) :
    realPositiveDetRoot g ^ 2 = (g.val : Matrix (Fin 2) (Fin 2) ℝ).det :=
  Real.sq_sqrt g.property.le

/-- The determinant root is multiplicative on the actual positive subgroup. -/
theorem realPositiveDetRoot_mul (g h : GL(2, ℝ)⁺) :
    realPositiveDetRoot (g * h) = realPositiveDetRoot g * realPositiveDetRoot h := by
  change Real.sqrt (((g.val : Matrix (Fin 2) (Fin 2) ℝ) *
    (h.val : Matrix (Fin 2) (Fin 2) ℝ)).det) = _
  have hg : 0 ≤ (g.val : Matrix (Fin 2) (Fin 2) ℝ).det := g.property.le
  rw [Matrix.det_mul, Real.sqrt_mul hg]
  rfl

/-- Dividing every entry by its actual positive determinant root gives a genuine group homomorphism to SL2. -/
def realPositiveNormalize : GL(2, ℝ)⁺ →* SL(2, ℝ) where
  toFun g := ⟨(realPositiveDetRoot g)⁻¹ • (g.val : Matrix (Fin 2) (Fin 2) ℝ), by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, ← realPositiveDetRoot_sq g]
    exact inv_mul_cancel₀ (pow_ne_zero _ (realPositiveDetRoot_pos g).ne')⟩
  map_one' := by
    apply Subtype.ext
    simp [realPositiveDetRoot]
  map_mul' g h := by
    apply Subtype.ext
    change (realPositiveDetRoot (g * h))⁻¹ •
      ((g.val : Matrix (Fin 2) (Fin 2) ℝ) * (h.val : Matrix (Fin 2) (Fin 2) ℝ)) =
      ((realPositiveDetRoot g)⁻¹ • (g.val : Matrix (Fin 2) (Fin 2) ℝ)) *
      ((realPositiveDetRoot h)⁻¹ • (h.val : Matrix (Fin 2) (Fin 2) ℝ))
    rw [realPositiveDetRoot_mul, _root_.mul_inv_rev, smul_mul_smul_comm, mul_comm]

/-- The genuine normalization has exactly the original scaled matrix entries. -/
theorem realPositiveNormalize_val (g : GL(2, ℝ)⁺) :
    (realPositiveNormalize g : Matrix (Fin 2) (Fin 2) ℝ) =
      (realPositiveDetRoot g)⁻¹ • (g.val : Matrix (Fin 2) (Fin 2) ℝ) := rfl

/-- Genuine determinant-one matrices are fixed by the actual positive normalization. -/
theorem realPositiveNormalize_toGLPos (g : SL(2, ℝ)) :
    realPositiveNormalize (toGLPos g) = g := by
  apply Subtype.ext
  simp [realPositiveNormalize_val, realPositiveDetRoot]

/-- The original determinant-root normalization varies continuously in the actual matrix topology. -/
theorem realPositiveNormalize_continuous : Continuous realPositiveNormalize := by
  have hM : Continuous (fun g : GL(2, ℝ)⁺ => (g.val : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Units.continuous_val.comp continuous_subtype_val
  apply Continuous.subtype_mk
  exact ((Real.continuous_sqrt.comp hM.matrix_det).inv₀
    (fun g => (realPositiveDetRoot_pos g).ne')).smul hM

/-- Scaling by the positive determinant root leaves the actual upper-half-plane action unchanged. -/
theorem realPositiveNormalize_smul (g : GL(2, ℝ)⁺) (z : ℍ) :
    realPositiveNormalize g • z = g.val • z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_smul_of_det_pos g.property]
  simp only [realPositiveNormalize_val, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self_apply, Complex.ofReal_mul, Complex.ofReal_inv,
    UpperHalfPlane.num, UpperHalfPlane.denom, mul_assoc, ← mul_add]
  have hr : (realPositiveDetRoot g : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realPositiveDetRoot_pos g).ne'
  exact mul_div_mul_left _ _ (inv_ne_zero hr)

/-- The original denominator is scaled by exactly the reciprocal determinant root. -/
theorem realPositiveNormalize_denom (g : GL(2, ℝ)⁺) (z : ℍ) :
    denom (mapGL ℝ (realPositiveNormalize g)) z =
      (realPositiveDetRoot g : ℂ)⁻¹ * denom g.val z := by
  simp [denom, mapGL_coe_matrix, realPositiveNormalize_val]
  ring

end
end Dubon2026
