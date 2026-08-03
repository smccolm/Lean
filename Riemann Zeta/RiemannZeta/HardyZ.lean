import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex

noncomputable section

namespace RiemannZeta

/-- The critical line parametrization s(t) = 1/2 + i * t for t ∈ ℝ. -/
def criticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * I

@[simp]
lemma criticalLinePoint_re (t : ℝ) : (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

@[simp]
lemma criticalLinePoint_im (t : ℝ) : (criticalLinePoint t).im = t := by
  simp [criticalLinePoint]

/-- Conjugate of a point on the critical line s(t) is 1 - s(t). -/
theorem conj_criticalLinePoint (t : ℝ) :
    star (criticalLinePoint t) = 1 - criticalLinePoint t := by
  apply Complex.ext
  · simp [criticalLinePoint]
    norm_num
  · simp [criticalLinePoint]

/-- The completed Riemann Zeta function on the critical line is invariant under t ↦ -t. -/
theorem completedRiemannZeta_criticalLine_neg (t : ℝ) :
    completedRiemannZeta (criticalLinePoint (-t)) =
      completedRiemannZeta (1 - criticalLinePoint t) := by
  have h : criticalLinePoint (-t) = 1 - criticalLinePoint t := by
    apply Complex.ext
    · simp [criticalLinePoint]
      norm_num
    · simp [criticalLinePoint]
  rw [h]

/-- The functional equation on the critical line: Λ(1/2 + i t) = Λ(1/2 - i t). -/
theorem completedRiemannZeta_criticalLine_functional_eq (t : ℝ) :
    completedRiemannZeta (criticalLinePoint t) =
      completedRiemannZeta (1 - criticalLinePoint t) := by
  exact (completedRiemannZeta_one_sub (criticalLinePoint t)).symm

/-- The completed Riemann Zeta function at s = 1/2 + i t is equal to its value at s = 1/2 - i t. -/
theorem completedRiemannZeta_criticalLine_symm (t : ℝ) :
    completedRiemannZeta (criticalLinePoint t) =
      completedRiemannZeta (criticalLinePoint (-t)) := by
  rw [completedRiemannZeta_criticalLine_functional_eq]
  rw [← completedRiemannZeta_criticalLine_neg]

/-- Definition of the Hardy Z-function modulus equality. -/
theorem hardyZ_abs_eq_riemannZeta_abs (t : ℝ) :
    ‖completedRiemannZeta (criticalLinePoint t)‖ =
      ‖completedRiemannZeta (criticalLinePoint (-t))‖ := by
  rw [completedRiemannZeta_criticalLine_symm]

end RiemannZeta
