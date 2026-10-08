import Dubon2026.CuspPeriodFourierCoefficients
import Dubon2026.RealSL2Generators
import Dubon2026.RealAffineLift

/-! # Vanishing genuine real-group unipotent averages at every cusp period -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory
open scoped MatrixGroups

/-- The genuine affine section at height one is precisely the original upper unipotent matrix. -/
theorem realAffineMatrix_one_eq_upperUnipotent (t : ℝ) :
    realAffineMatrix t (show 0 < (1 : ℝ) by norm_num) = realUpperUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realAffineMatrix, UpperHalfPlane.toSL2R, realUpperUnipotent]

/-- Original unipotent left translation changes only the original horizontal cusp argument. -/
theorem realWeightLift_upperUnipotent (k : ℤ) (f : ℍ → ℂ) (t : ℝ) (g : SL(2, ℝ)) :
    realWeightLift k f (realUpperUnipotent t * g) =
      f ⟨((t + (g • I).re : ℝ) : ℂ) + (g • I).im * Complex.I,
        by simpa using (g • I).im_pos⟩ * denom (mapGL ℝ g) I ^ (-k) := by
  rw [← realAffineMatrix_one_eq_upperUnipotent,
    realWeightLift_affine]
  simp only [Real.one_rpow, Complex.ofReal_one, one_mul]
  congr 1
  apply congrArg f
  apply UpperHalfPlane.ext
  rw [realAffineMatrix_smul]
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_add]
  rw [← Complex.re_add_im (g • I : ℍ)]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- Every literal cusp period has zero unipotent average at every point of the real group. -/
theorem realWeightLift_unipotent_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (g : SL(2, ℝ)) :
    (∫ x in (0 : ℝ)..1, realWeightLift k f (realUpperUnipotent (h * x) * g)) = 0 := by
  simp_rw [realWeightLift_upperUnipotent]
  rw [intervalIntegral.integral_mul_const,
    cusp_period_horizontal_shift_integral_zero f hh hΓ (g • I).re (g • I).im_pos, zero_mul]

end
end Dubon2026
