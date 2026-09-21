import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A logarithmic integral bound from a truncated inverse tail

This finite-measure deduction will be consumed by the actual zeta
superlevel measure theorem. All endpoint and logarithmic factors are exact.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval

namespace TaoTrudgianYang2025

theorem continuous_const_div_max {A C : ℝ} (hA : 0 < A) :
    Continuous (fun t : ℝ => C / max A t) :=
  continuous_const.div (continuous_const.max continuous_id)
    (fun _ => ne_of_gt (hA.trans_le (le_max_left _ _)))

theorem integral_const_div_max {A M C : ℝ}
    (hA : 0 < A) (hAM : A ≤ M) :
    (∫ t in 0..M, C / max A t) = C*(1+Real.log (M/A)) := by
  have hcont := continuous_const_div_max (C := C) hA
  have hlo : (∫ t in 0..A, C/max A t) = C := by
    calc
      _ = ∫ _t in 0..A, C/A := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hA.le] at ht
        dsimp only
        rw [max_eq_left ht.2]
      _ = C := by simp; field_simp
  have hhi : (∫ t in A..M, C/max A t) = C*Real.log (M/A) := by
    calc
      _ = ∫ t in A..M, C*(1/t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hAM] at ht
        dsimp only
        rw [max_eq_right ht.1]
        ring
      _ = C*Real.log (M/A) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hA (hA.trans_le hAM)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 A) (hcont.intervalIntegrable A M),hlo,hhi]
  ring

theorem integral_le_log_of_truncated_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A M C : ℝ}
    (hA : 0 < A) (hAM : A ≤ M)
    (hfi : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hfm : f ≤ᵐ[μ] (fun _ => M))
    (htail : ∀ t : ℝ, 0 < t → t ≤ M →
      μ.real {x | t ≤ f x} ≤ C/max A t) :
    (∫ x, f x ∂μ) ≤ C*(1+Real.log (M/A)) := by
  rw [hfi.integral_eq_integral_Ioc_meas_le hfn hfm]
  have hcont := continuous_const_div_max (C := C) hA
  have hi : IntegrableOn (fun t : ℝ => C/max A t) (Ioc 0 M) :=
    (hcont.intervalIntegrable 0 M).1
  calc
    _ ≤ ∫ t in Ioc 0 M, C/max A t := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hi
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact htail t ht.1 ht.2
    _ = ∫ t in 0..M, C/max A t :=
      (intervalIntegral.integral_of_le (hA.le.trans hAM)).symm
    _ = C*(1+Real.log (M/A)) := integral_const_div_max hA hAM

end TaoTrudgianYang2025
