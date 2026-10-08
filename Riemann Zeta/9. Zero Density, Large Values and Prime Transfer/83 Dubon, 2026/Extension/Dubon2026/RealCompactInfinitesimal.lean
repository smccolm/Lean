import Dubon2026.RealLiftInfinitesimal
import Dubon2026.RealCompactWeight

/-! # The genuine compact rotation and its original weight derivative -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The actual compact rotation with tangent matrix [[0,1],[-1,0]]. -/
def realRotationCurve (t : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t], by
    simp only [Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq t]⟩

/-- The original lower-row denominator along the compact rotation is precisely cos(t)-i sin(t). -/
theorem realRotationCurve_denom (t : ℝ) :
    denom (mapGL ℝ (realRotationCurve t)) I = (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
  simp [denom, realRotationCurve, mapGL, toGL, sub_eq_add_neg, add_comm]

/-- The actual real rotation fixes the original upper-half-plane base point. -/
theorem realRotationCurve_smul_I (t : ℝ) : realRotationCurve t • I = I := by
  have hd : (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I ≠ 0 := by
    rw [← realRotationCurve_denom]
    exact denom_ne_zero _ _
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  change ((Real.cos t : ℂ) * Complex.I + (Real.sin t : ℂ)) /
    (((-Real.sin t : ℝ) : ℂ) * Complex.I + (Real.cos t : ℂ)) = Complex.I
  rw [Complex.ofReal_neg]
  have hd' : -(Real.sin t : ℂ) * Complex.I + (Real.cos t : ℂ) ≠ 0 := by
    simpa only [sub_eq_add_neg, neg_mul, add_comm] using hd
  apply (div_eq_iff hd').mpr
  linear_combination (Real.sin t : ℂ) * Complex.I_sq

/-- The literal compact right orbit retains the exact original denominator weight. -/
theorem realWeightLift_right_rotation_formula (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (t : ℝ) :
    realWeightLift k f (g * realRotationCurve t) = realWeightLift k f g *
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) ^ (-k) := by
  rw [realWeightLift_right_stabilizer k f g _ (realRotationCurve_smul_I t), realRotationCurve_denom]

/-- The actual compact right derivative is precisely i times the original integral weight. -/
theorem realWeightLift_right_rotation_hasDerivAt (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    HasDerivAt (fun t : ℝ => realWeightLift k f (g * realRotationCurve t))
      ((k : ℂ) * Complex.I * realWeightLift k f g) 0 := by
  have hd : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I)
      (-Complex.I) 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp.sub
      ((Real.hasDerivAt_sin 0).ofReal_comp.mul_const Complex.I)
  have hp := (hasDerivAt_zpow (-k) (1 : ℂ) (Or.inl one_ne_zero)).comp_of_eq 0 hd (by simp)
  simp_rw [realWeightLift_right_rotation_formula]
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hp.const_mul (realWeightLift k f g)

end
end Dubon2026
