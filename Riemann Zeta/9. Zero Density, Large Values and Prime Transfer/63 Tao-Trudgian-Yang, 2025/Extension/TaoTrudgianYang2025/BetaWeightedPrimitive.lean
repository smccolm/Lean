import TaoTrudgianYang2025.AtkinsonAmplitudeIntegral

/-!
# Weighted primitive bounds for an arbitrary continuous carrier

The proof is ordinary integration by parts. Unlike the root-phase
specialization, this theorem consumes a carrier on any open interval.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem IntervalC1Bound.integral_mul_of_primitive_bound
    {f k : ℝ → ℂ} {a b M B : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hk : ∀ x ∈ J, ContinuousAt k x)
    (hprimitive : ∀ x ∈ Icc a b, ‖∫ y in a..x, k y‖ ≤ B) :
    ‖∫ y in a..b, f y*k y‖ ≤ 2*B*M := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hprimitive a ⟨le_rfl,hab⟩)
  let K : ℝ → ℂ := fun x => ∫ y in a..x, k y
  have hki {x : ℝ} (hx : x ∈ Icc a b) : IntervalIntegrable k volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact fun y hy => (hk y (hsub ⟨hy.1,hy.2.trans hx.2⟩)).continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt K (k x) x :=
    intervalIntegral.integral_hasDerivAt_right (hki hx)
      (ContinuousAt.stronglyMeasurableAtFilter hJ hk x (hsub hx)) (hk x (hsub hx))
  have hK : ContinuousOn K (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hKb (x : ℝ) (hx : x ∈ Icc a b) : ‖K x‖ ≤ B := hprimitive x hx
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := deriv f) (v := K) (v' := k)
    (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => by rw [uIcc_of_le hab] at hx; exact hd x hx)
    (hf.derivative_integrable hab) (hki ⟨hab,le_rfl⟩)
  have hKa : K a = 0 := by simp [K]
  have hvar : ‖∫ y in a..b, deriv f y*K y‖ ≤ B*M := by
    calc
      _ ≤ |∫ y in a..b, ‖deriv f y*K y‖| := intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ y in a..b, ‖deriv f y*K y‖ := by
        rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))]
      _ ≤ ∫ y in a..b, ‖deriv f y‖*B := by
        apply intervalIntegral.integral_mono_on hab
        · simpa only [norm_mul] using
            (hf.derivative_integrable hab).norm.mul_continuousOn hK.norm
        · exact (hf.derivative_integrable hab).norm.mul_const B
        · intro y hy
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hKb y hy) (norm_nonneg _)
      _ = (∫ y in a..b, ‖deriv f y‖)*B := by rw [intervalIntegral.integral_mul_const]
      _ ≤ B*M := by nlinarith [hf.variation_le]
  rw [hparts,hKa,mul_zero,sub_zero]
  apply (norm_sub_le _ _).trans
  have hprod : ‖f b*K b‖ ≤ M*B := by
    rw [norm_mul]
    exact mul_le_mul (hf.norm_le b ⟨hab,le_rfl⟩) (hKb b ⟨hab,le_rfl⟩)
      (norm_nonneg _) hf.nonneg
  linarith

end TaoTrudgianYang2025
