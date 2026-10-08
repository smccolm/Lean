import Dubon2026.RealInfinitesimalEntryTangents
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # The original real rotations exhaust the genuine compact stabilizer -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The original rotation matrices satisfy their exact one-parameter group law. -/
theorem realRotationCurve_add (s t : ℝ) :
    realRotationCurve (s + t) = realRotationCurve s * realRotationCurve t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realRotationCurve, coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/-- Every actual element of the original compact stabilizer is a genuine real rotation. -/
theorem realCompactSubgroup_eq_rotation (h : realCompactSubgroup) :
    ∃ t : ℝ, h.val = realRotationCurve t := by
  let z := denom (mapGL ℝ h.val) I
  have hn : ‖z‖ = 1 := realCompactSubgroup_denom_norm h
  have hz : z ≠ 0 := denom_ne_zero _ _
  have he := congrArg (fun w : ℍ => (w : ℂ)) h.property
  dsimp only at he
  rw [coe_specialLinearGroup_apply] at he
  change ((h.val 0 0 : ℂ) * Complex.I + (h.val 0 1 : ℂ)) /
    ((h.val 1 0 : ℂ) * Complex.I + (h.val 1 1 : ℂ)) = Complex.I at he
  have hcross := (div_eq_iff hz).mp he
  have hre := congrArg Complex.re hcross
  have him := congrArg Complex.im hcross
  norm_num [Complex.mul_re, Complex.mul_im] at hre him
  have hcos : Real.cos (-Complex.arg z) = h.val 1 1 := by
    rw [Real.cos_neg, Complex.cos_arg hz, hn, div_one]
    simp [z, denom]
  have hsin : Real.sin (-Complex.arg z) = -h.val 1 0 := by
    rw [Real.sin_neg, Complex.sin_arg, hn, div_one]
    simp [z, denom]
  refine ⟨-Complex.arg z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · change h.val 0 0 = Real.cos (-Complex.arg z)
    rw [hcos, him]
    simp [z, denom]
  · change h.val 0 1 = Real.sin (-Complex.arg z)
    rw [hsin, hre]
    simp [z, denom]
  · change h.val 1 0 = -Real.sin (-Complex.arg z)
    rw [hsin, neg_neg]
  · change h.val 1 1 = Real.cos (-Complex.arg z)
    exact hcos.symm

end
end Dubon2026
