import Dubon2026.RealInfinitesimalSmoothCurves

/-! # Exact original real subgroup conjugation and normalization laws -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ContDiff

/-- The original lower unipotent entries form a smooth real matrix curve. -/
theorem realLowerUnipotent_entries_contDiff (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t : ℝ => realLowerUnipotent t i j) := by
  fin_cases i <;> fin_cases j <;> simp [realLowerUnipotent] <;> fun_prop

/-- The genuine upper unipotent starts at the actual real group identity. -/
theorem realUpperUnipotent_zero : realUpperUnipotent 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realUpperUnipotent]

/-- The genuine lower unipotent starts at the actual real group identity. -/
theorem realLowerUnipotent_zero : realLowerUnipotent 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realLowerUnipotent]

/-- The genuine geodesic starts at the actual real group identity. -/
theorem realGeodesicCurve_zero : realGeodesicCurve 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R]

/-- Original lower unipotents satisfy their literal additive subgroup law. -/
theorem realLowerUnipotent_add (s t : ℝ) :
    realLowerUnipotent (s + t) = realLowerUnipotent s * realLowerUnipotent t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realLowerUnipotent, coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The original geodesic action expands the genuine upper unipotent parameter by precisely exp(s). -/
theorem realGeodesicCurve_mul_upper (s t : ℝ) :
    realGeodesicCurve s * realUpperUnipotent t =
      realUpperUnipotent (Real.exp s * t) * realGeodesicCurve s := by
  have hs : Real.sqrt (Real.exp s) ≠ 0 := (Real.sqrt_pos.mpr (Real.exp_pos s)).ne'
  have hs2 := Real.sq_sqrt (Real.exp_nonneg s)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R, realUpperUnipotent,
      coe_mul, Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_exp]
  all_goals field_simp [hs]
  all_goals nlinarith [mul_eq_mul_right_iff.mpr (Or.inl hs2 :
    Real.sqrt (Real.exp s) ^ 2 = Real.exp s ∨ t = 0)]

/-- The original geodesic action contracts the genuine lower unipotent parameter by precisely exp(-s). -/
theorem realGeodesicCurve_mul_lower (s t : ℝ) :
    realGeodesicCurve s * realLowerUnipotent t =
      realLowerUnipotent (Real.exp (-s) * t) * realGeodesicCurve s := by
  have hs : Real.sqrt (Real.exp s) ≠ 0 := (Real.sqrt_pos.mpr (Real.exp_pos s)).ne'
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have hs2 := Real.sq_sqrt (Real.exp_nonneg s)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R, realLowerUnipotent,
      coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_neg, -Complex.ofReal_exp]
  all_goals field_simp [hs, he]
  all_goals nlinarith [mul_eq_mul_right_iff.mpr (Or.inl hs2 :
    Real.sqrt (Real.exp s) ^ 2 = Real.exp s ∨ t = 0)]

end
end Dubon2026
