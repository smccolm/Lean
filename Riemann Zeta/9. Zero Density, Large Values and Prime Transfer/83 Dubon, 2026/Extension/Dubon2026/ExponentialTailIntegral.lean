import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrating an exponential distribution bound -/

namespace Dubon2026

open MeasureTheory Set
open scoped ENNReal

theorem integral_le_of_exponential_tail {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f)
    {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * Real.exp (-t))) :
    ∫ x, f x ∂μ ≤ C := by
  have hmain : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal C := by
    rw [ofReal_integral_eq_lintegral_ofReal hf hfn, lintegral_eq_lintegral_meas_lt μ hfn hf.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-t)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        exact fun t ht => htail t ht
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), C * Real.exp (-t)) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg_Ioi 0).const_mul C)
          (Filter.Eventually.of_forall (fun t => mul_nonneg hC (Real.exp_pos _).le))).symm
      _ = ENNReal.ofReal C := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hmain

end Dubon2026
