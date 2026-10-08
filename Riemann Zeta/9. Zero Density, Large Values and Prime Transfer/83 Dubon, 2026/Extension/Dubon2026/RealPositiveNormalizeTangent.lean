import Dubon2026.RealPositiveNormalize
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Actual tangents of positive determinant normalization -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- At the identity, the actual determinant derivative is the original tangent trace. -/
theorem realPositiveCurve_det_hasDerivAt (c : ℝ → GL(2, ℝ)⁺) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val.val i j) (a i j) 0) :
    HasDerivAt (fun t => (c t).val.val.det) (Matrix.trace a) 0 := by
  simpa [Matrix.det_fin_two, hc, Matrix.trace, Fin.sum_univ_two, add_comm] using
    ((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0))

/-- The actual positive square-root determinant has half the original trace as derivative. -/
theorem realPositiveCurve_root_hasDerivAt (c : ℝ → GL(2, ℝ)⁺) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val.val i j) (a i j) 0) :
    HasDerivAt (fun t => realPositiveDetRoot (c t)) (Matrix.trace a / 2) 0 := by
  simpa [realPositiveDetRoot, hc] using
    (realPositiveCurve_det_hasDerivAt c hc a hd).sqrt (by simp [hc])

/-- Each literal normalized matrix entry has its genuine traceless original tangent. -/
theorem realPositiveNormalize_entry_hasDerivAt (c : ℝ → GL(2, ℝ)⁺) (hc : c 0 = 1)
    (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val.val i j) (a i j) 0) (i j : Fin 2) :
    HasDerivAt (fun t => realPositiveNormalize (c t) i j)
      ((a - (Matrix.trace a / 2) • 1) i j) 0 := by
  have hr := (realPositiveCurve_root_hasDerivAt c hc a hd).inv
    (realPositiveDetRoot_pos (c 0)).ne'
  convert hr.mul (hd i j) using 1
  simp [hc, realPositiveDetRoot, Matrix.sub_apply, Matrix.smul_apply, sub_eq_add_neg, add_comm]

end
end Dubon2026
