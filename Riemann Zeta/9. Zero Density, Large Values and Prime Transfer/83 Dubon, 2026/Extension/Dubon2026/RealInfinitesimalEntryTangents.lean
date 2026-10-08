import Dubon2026.RealGaussSmoothCoordinates

/-! # Exact entry tangents of the original real one-parameter matrices -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The original upper curve has exactly the upper elementary matrix as tangent. -/
theorem realUpperUnipotent_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realUpperUnipotent t i j) (!![0, 1; 0, 0] i j) 0 := by
  fin_cases i <;> fin_cases j <;> dsimp [realUpperUnipotent]
  all_goals first | exact hasDerivAt_const 0 _ | exact hasDerivAt_id 0

/-- The original lower curve has exactly the lower elementary matrix as tangent. -/
theorem realLowerUnipotent_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realLowerUnipotent t i j) (!![0, 0; 1, 0] i j) 0 := by
  fin_cases i <;> fin_cases j <;> dsimp [realLowerUnipotent]
  all_goals first | exact hasDerivAt_const 0 _ | exact hasDerivAt_id 0

/-- The original geodesic tangent is precisely half the standard diagonal generator. -/
theorem realGeodesicCurve_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realGeodesicCurve t i j) (!![(1 / 2 : ℝ), 0; 0, -(1 / 2)] i j) 0 := by
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (Real.exp t)) (1 / 2) 0 := by
    simpa using (Real.hasDerivAt_exp 0).sqrt (by simp)
  have hi : HasDerivAt (fun t : ℝ => (Real.sqrt (Real.exp t))⁻¹) (-(1 / 2)) 0 := by
    simpa using hs.inv (by simp)
  fin_cases i <;> fin_cases j
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using hs
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using
      (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using
      (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using hi

/-- The original compact curve starts at the real group identity. -/
theorem realRotationCurve_zero : realRotationCurve 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realRotationCurve]

/-- The original compact rotation tangent is exactly upper minus lower. -/
theorem realRotationCurve_entry_hasDerivAt (i j : Fin 2) :
    HasDerivAt (fun t => realRotationCurve t i j) (!![0, 1; -1, 0] i j) 0 := by
  fin_cases i <;> fin_cases j
  · simpa [realRotationCurve] using Real.hasDerivAt_cos 0
  · simpa [realRotationCurve] using Real.hasDerivAt_sin 0
  · simpa [realRotationCurve] using (Real.hasDerivAt_sin 0).neg
  · simpa [realRotationCurve] using Real.hasDerivAt_cos 0

end
end Dubon2026
