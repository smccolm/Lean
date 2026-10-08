import Dubon2026.RealInfinitesimalGroupRelations
import Dubon2026.RealMatrixSmoothSubmodule
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Genuine smooth Gaussian coordinates at the real group identity -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ContDiff Topology

/-- The original lower, geodesic and upper matrices give a globally smooth coordinate family. -/
def realGaussCoordinates (w : ℝ × ℝ × ℝ) : SL(2, ℝ) :=
  realLowerUnipotent w.1 * realGeodesicCurve w.2.1 * realUpperUnipotent w.2.2

/-- All entries of the actual Gaussian matrix family are smooth. -/
theorem realGaussCoordinates_entries_contDiff (i j : Fin 2) :
    ContDiff ℝ ∞ (fun w => realGaussCoordinates w i j) := by
  have hl (i j : Fin 2) : ContDiff ℝ ∞
      (fun w : ℝ × ℝ × ℝ => (realLowerUnipotent w.1 * realGeodesicCurve w.2.1) i j) := by
    change ContDiff ℝ ∞ (fun w : ℝ × ℝ × ℝ =>
      ∑ l : Fin 2, realLowerUnipotent w.1 i l * realGeodesicCurve w.2.1 l j)
    exact ContDiff.sum (fun l _ =>
      ((realLowerUnipotent_entries_contDiff i l).comp contDiff_fst).mul
        ((realGeodesicCurve_entries_contDiff l j).comp contDiff_snd.fst))
  change ContDiff ℝ ∞ (fun w : ℝ × ℝ × ℝ =>
    ∑ l : Fin 2, (realLowerUnipotent w.1 * realGeodesicCurve w.2.1) i l *
      realUpperUnipotent w.2.2 l j)
  exact ContDiff.sum (fun l _ => (hl i l).mul
    ((realUpperUnipotent_entries_contDiff l j).comp contDiff_snd.snd))

/-- The original geodesic at twice the logarithm is the positive diagonal matrix itself. -/
theorem realGeodesicCurve_two_log (a : ℝ) (ha : 0 < a) :
    realGeodesicCurve (2 * Real.log a) = realDiagonal a ha.ne' := by
  have he : Real.exp (2 * Real.log a) = a ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log ha, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realGeodesicCurve, realAffineMatrix, UpperHalfPlane.toSL2R, realDiagonal,
      -Complex.ofReal_exp, -Complex.ofReal_pow, he, Real.sqrt_sq ha.le]

/-- Exact Gaussian coordinates recover every original matrix with positive first entry. -/
theorem realGaussCoordinates_eq (g : SL(2, ℝ)) (hg : 0 < g 0 0) :
    realGaussCoordinates (g 1 0 / g 0 0, 2 * Real.log (g 0 0), g 0 1 / g 0 0) = g := by
  unfold realGaussCoordinates
  rw [realGeodesicCurve_two_log _ hg]
  exact (realSL2_gauss g hg.ne').symm

/-- Actual matrix-entry derivatives give the precise local Gaussian-coordinate derivative. -/
theorem realGaussCoordinates_curve_deriv (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1)
    (a b d : ℝ) (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    HasDerivAt (fun t => (c t 1 0 / c t 0 0,
      2 * Real.log (c t 0 0), c t 0 1 / c t 0 0)) (b, 2 * a, d) 0 := by
  have hn : c 0 0 0 ≠ 0 := by simp [hc]
  simpa [hc] using (hb.div ha hn).prodMk ((ha.log hn).const_mul 2 |>.prodMk (hd.div ha hn))

end
end Dubon2026
