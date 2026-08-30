import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

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

/-- The complex conjugate of a point on the critical line s(t) = 1/2 + i t is 1 - s(t) = 1/2 - i t. -/
theorem conj_criticalLinePoint (t : ℝ) :
    star (criticalLinePoint t) = 1 - criticalLinePoint t := by
  apply Complex.ext
  · simp [criticalLinePoint]
    norm_num
  · simp [criticalLinePoint]

/-- Argument equality lemma for the critical line: s(-t) = 1 - s(t). -/
lemma criticalLinePoint_neg_eq_one_sub (t : ℝ) :
    criticalLinePoint (-t) = 1 - criticalLinePoint t := by
  apply Complex.ext
  · simp [criticalLinePoint]
    norm_num
  · simp [criticalLinePoint]

/-- The completed Riemann Zeta function functional equation on the critical line:
    Λ(1/2 + i t) = Λ(1/2 - i t). Derived as a coordinate wrapper around Mathlib's `completedRiemannZeta_one_sub`. -/
theorem completedRiemannZeta_criticalLine_functional_eq (t : ℝ) :
    completedRiemannZeta (criticalLinePoint t) =
      completedRiemannZeta (1 - criticalLinePoint t) := by
  exact (completedRiemannZeta_one_sub (criticalLinePoint t)).symm

/-- Completed Riemann Zeta evaluation invariance under negation of the critical line parameter:
    Λ(1/2 + i t) = Λ(1/2 - i t). -/
theorem completedRiemannZeta_criticalLine_symm (t : ℝ) :
    completedRiemannZeta (criticalLinePoint t) =
      completedRiemannZeta (criticalLinePoint (-t)) := by
  rw [completedRiemannZeta_criticalLine_functional_eq]
  rw [← criticalLinePoint_neg_eq_one_sub]

/-- Norm equality for completed Riemann Zeta across the critical line parameter:
    ‖Λ(1/2 + i t)‖ = ‖Λ(1/2 - i t)‖. -/
theorem completedRiemannZeta_norm_criticalLine_neg (t : ℝ) :
    ‖completedRiemannZeta (criticalLinePoint t)‖ =
      ‖completedRiemannZeta (criticalLinePoint (-t))‖ := by
  rw [completedRiemannZeta_criticalLine_symm]

/-- Classical Riemann-Siegel theta function phase angle θ(t) on the critical line.
    Uses Mathlib's principal branch Complex.log. -/
def riemannSiegelTheta (t : ℝ) : ℝ :=
  (Complex.log (Gamma ((1 / 4 : ℂ) + (t / 2 : ℂ) * I))).im - (t / 2) * Real.log Real.pi

/-- Complex-valued Hardy-type normalization H(t) = exp(i * θ(t)) * ζ(1/2 + i t). -/
def hardyZ (t : ℝ) : ℂ :=
  exp (I * (riemannSiegelTheta t : ℂ)) * riemannZeta (criticalLinePoint t)

/-- Absolute value correspondence: ‖H(t)‖ = ‖ζ(1/2 + i t)‖. -/
theorem hardyZ_norm_eq_riemannZeta_norm (t : ℝ) :
    ‖hardyZ t‖ = ‖riemannZeta (criticalLinePoint t)‖ := by
  dsimp [hardyZ]
  rw [norm_mul]
  have h_phase : ‖exp (I * (riemannSiegelTheta t : ℂ))‖ = 1 := by
    rw [norm_exp]
    have h_re : (I * (riemannSiegelTheta t : ℂ)).re = 0 := by
      simp [I_re, I_im]
    rw [h_re, Real.exp_zero]
  rw [h_phase, one_mul]

/-- Zero equivalence: H(t) = 0 ↔ ζ(1/2 + i t) = 0. -/
theorem hardyZ_zero_iff_riemannZeta_zero (t : ℝ) :
    hardyZ t = 0 ↔ riemannZeta (criticalLinePoint t) = 0 := by
  dsimp [hardyZ]
  have h_exp_ne_zero : exp (I * (riemannSiegelTheta t : ℂ)) ≠ 0 := exp_ne_zero _
  rw [mul_eq_zero]
  simp [h_exp_ne_zero]

/-- Symmetry of the Hardy-type norm under parameter negation:
    ‖H(-t)‖ = ‖H(t)‖ under Zeta critical line norm symmetry. -/
theorem hardyZ_neg_norm (t : ℝ) (h_symm : ‖riemannZeta (criticalLinePoint (-t))‖ = ‖riemannZeta (criticalLinePoint t)‖) :
    ‖hardyZ (-t)‖ = ‖hardyZ t‖ := by
  rw [hardyZ_norm_eq_riemannZeta_norm (-t)]
  rw [hardyZ_norm_eq_riemannZeta_norm t]
  exact h_symm

end RiemannZeta
