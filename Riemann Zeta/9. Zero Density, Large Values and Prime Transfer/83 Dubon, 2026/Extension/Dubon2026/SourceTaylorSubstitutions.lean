import Dubon2026.SourceScalarTaylorSeries
import Mathlib.RingTheory.PowerSeries.Expand

/-! DUB-17/18 -> original torsion cardinality -> cusp realization.
The original cusp generators are unit twists and positive power
substitutions of j. Native Taylor convergence and coefficient uniqueness
identify these substitutions with literal formal rescaling and expansion.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter
open scoped Topology

theorem series_eq_of_hasFPowerSeriesAt {f : ℂ → ℂ} {P : PowerSeries ℂ}
    (h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => P.coeff n)) 0) :
    series f = P := by
  have he := (hasFPowerSeriesAt_series h.analyticAt).eq_formalMultilinearSeries h
  have hc := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ he
  ext n
  exact congrFun hc n

theorem series_comp_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    series (fun z => f (c * z)) = PowerSeries.rescale c (series f) := by
  apply series_eq_of_hasFPowerSeriesAt
  rw [hasFPowerSeriesAt_iff]
  have hs := hasFPowerSeriesAt_iff.mp (hasFPowerSeriesAt_series hf)
  have ht : Tendsto (fun z : ℂ => c * z) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => c * z) := continuous_const.mul continuous_id
    simpa using hc.tendsto (0 : ℂ)
  filter_upwards [ht.eventually hs] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, PowerSeries.coeff_rescale,
    smul_eq_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hz

theorem series_comp_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (d : ℕ) (hd : d ≠ 0) :
    series (fun z => f (z ^ d)) = PowerSeries.expand d hd (series f) := by
  apply series_eq_of_hasFPowerSeriesAt
  rw [hasFPowerSeriesAt_iff]
  have hs := hasFPowerSeriesAt_iff.mp (hasFPowerSeriesAt_series hf)
  have ht : Tendsto (fun z : ℂ => z ^ d) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z ^ d) := continuous_id.pow d
    simpa [hd] using hc.tendsto (0 : ℂ)
  filter_upwards [ht.eventually hs] with z hz
  simp only [zero_add, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] at hz ⊢
  have hinj : Function.Injective (fun n : ℕ => d * n) := mul_right_injective₀ hd
  rw [← hinj.hasSum_iff]
  · change HasSum (fun n : ℕ => z ^ (d * n) *
      (PowerSeries.expand d hd (series f)).coeff (d * n)) (f (z ^ d))
    simpa only [PowerSeries.coeff_expand_mul, pow_mul] using hz
  · intro m hm
    have hdm : ¬ d ∣ m := by
      rintro ⟨n, hn⟩
      exact hm ⟨n, hn.symm⟩
    rw [PowerSeries.coeff_expand_of_not_dvd d hd _ hdm, mul_zero]

end
end Dubon2026.SourceFunctionField.CuspTaylor
