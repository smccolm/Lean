import Dubon2026.AdelicHilbertGeodesicSmoothness
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Smooth original entries of the actual infinitesimal matrix curves -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ContDiff

/-- Every original matrix entry of the genuine upper unipotent curve is smooth. -/
theorem realUpperUnipotent_entries_contDiff (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t : ℝ => realUpperUnipotent t i j) := by
  fin_cases i <;> fin_cases j <;> simp [realUpperUnipotent] <;> fun_prop

/-- Every original matrix entry of the genuine geodesic curve is smooth. -/
theorem realGeodesicCurve_entries_contDiff (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t : ℝ => realGeodesicCurve t i j) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (Real.exp t)) :=
    Real.contDiff_exp.sqrt (fun t => (Real.exp_pos t).ne')
  have hi := hs.inv (fun t => (Real.sqrt_pos.mpr (Real.exp_pos t)).ne')
  fin_cases i <;> fin_cases j
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using hs
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R] using hi

/-- Every original matrix entry of the genuine compact rotation curve is smooth. -/
theorem realRotationCurve_entries_contDiff (i j : Fin 2) :
    ContDiff ℝ ∞ (fun t : ℝ => realRotationCurve t i j) := by
  fin_cases i <;> fin_cases j <;> simp [realRotationCurve] <;> fun_prop

end
end Dubon2026
