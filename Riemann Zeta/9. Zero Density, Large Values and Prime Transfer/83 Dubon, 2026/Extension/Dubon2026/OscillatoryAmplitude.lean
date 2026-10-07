import Dubon2026.PhaseSecondDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Exact amplitude variation bound for an actual oscillatory integral -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- Integration by parts bounds an actual weighted oscillatory integral by the proved primitive
bound times the terminal amplitude and its genuine total derivative variation. -/
theorem norm_integral_amplitude_mul_le {z w w' : ℝ → ℂ} {a b M : ℝ}
    (hz : Continuous z) (hab : a ≤ b)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hw' : IntervalIntegrable w' volume a b)
    (hM : ∀ t ∈ Icc a b, ‖∫ u in a..t, z u‖ ≤ M) :
    ‖∫ t in a..b, w t * z t‖ ≤ M * (‖w b‖ + ∫ t in a..b, ‖w' t‖) := by
  let F : ℝ → ℂ := fun t => ∫ u in a..t, z u
  have hF (t : ℝ) : HasDerivAt F (z t) t :=
    intervalIntegral.integral_hasDerivAt_right (hz.intervalIntegrable _ _)
      hz.aestronglyMeasurable.stronglyMeasurableAtFilter hz.continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (v := F) (u' := w') (v' := z)
    (fun t ht => hw t (by simpa only [uIcc_of_le hab] using ht))
    (fun t _ => hF t) hw' (hz.intervalIntegrable _ _)
  have hFa : F a = 0 := by simp [F]
  rw [hFa, mul_zero, sub_zero] at hi
  have hprod : IntervalIntegrable (fun t => w' t * F t) volume a b :=
    hw'.mul_continuousOn hFc.continuousOn
  have hbound : ‖∫ t in a..b, w' t * F t‖ ≤ (∫ t in a..b, ‖w' t‖) * M := by
    calc
      _ ≤ ∫ t in a..b, ‖w' t * F t‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, ‖w' t‖ * M := intervalIntegral.integral_mono_on hab hprod.norm
        (hw'.norm.mul_const M) (fun t ht => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM t ht) (norm_nonneg _))
      _ = _ := intervalIntegral.integral_mul_const M _
  rw [hi]
  calc
    _ ≤ ‖w b * F b‖ + ‖∫ t in a..b, w' t * F t‖ := norm_sub_le _ _
    _ ≤ ‖w b‖ * M + (∫ t in a..b, ‖w' t‖) * M := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hM b ⟨hab, le_rfl⟩) (norm_nonneg _)) hbound
    _ = _ := by ring

end
end Dubon2026
