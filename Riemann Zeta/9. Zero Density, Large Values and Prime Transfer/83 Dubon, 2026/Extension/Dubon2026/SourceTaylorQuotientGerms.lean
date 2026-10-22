import Dubon2026.SourceTaylorLaurentOrder

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
Equality of formal analytic Taylor quotients is exactly equality of their
punctured meromorphic germs. This makes the cusp realization independent
of quotient choices and permits field operations on one common disk.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter
open scoped Topology

theorem series_eq_iff_eventuallyEq {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series f = series g ↔ f =ᶠ[𝓝 (0 : ℂ)] g := by
  refine ⟨fun he => ?_, series_eq_of_eventuallyEq hf hg⟩
  have hsf := hasFPowerSeriesAt_iff.mp (hasFPowerSeriesAt_series hf)
  have hsg := hasFPowerSeriesAt_iff.mp (hasFPowerSeriesAt_series hg)
  rw [he] at hsf
  filter_upwards [hsf, hsg] with z hzf hzg
  simpa only [zero_add] using hzf.unique hzg

theorem eventually_ne_zero_of_series_ne_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : series f ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z ≠ 0 :=
  hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun he => hf0 ((series_eq_zero_iff hf).mpr he))

theorem quotient_eq_iff_eventuallyEq {f g h k : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hh : AnalyticAt ℂ h 0) (hk : AnalyticAt ℂ k 0)
    (hg0 : (series g : LaurentSeries ℂ) ≠ 0)
    (hk0 : (series k : LaurentSeries ℂ) ≠ 0) :
    (series f : LaurentSeries ℂ) / (series g : LaurentSeries ℂ) =
      (series h : LaurentSeries ℂ) / (series k : LaurentSeries ℂ) ↔
      f / g =ᶠ[𝓝[≠] (0 : ℂ)] h / k := by
  have hg0' : series g ≠ 0 := fun he => hg0 (by rw [he, map_zero])
  have hk0' : series k ≠ 0 := fun he => hk0 (by rw [he, map_zero])
  have hg_ne := eventually_ne_zero_of_series_ne_zero hg hg0'
  have hk_ne := eventually_ne_zero_of_series_ne_zero hk hk0'
  rw [div_eq_div_iff hg0 hk0]
  have hs : (series f : LaurentSeries ℂ) * (series k : LaurentSeries ℂ) =
      (series h : LaurentSeries ℂ) * (series g : LaurentSeries ℂ) ↔
      series (f * k) = series (h * g) := by
    rw [series_mul hf hk, series_mul hh hg]
    rw [← PowerSeries.coe_mul, ← PowerSeries.coe_mul]
    exact HahnSeries.ofPowerSeries_injective.eq_iff
  rw [hs, series_eq_iff_eventuallyEq (hf.mul hk) (hh.mul hg)]
  constructor
  · intro he
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hg_ne, hk_ne] with z hz hgz hkz
    exact (div_eq_div_iff hgz hkz).mpr hz
  · intro he
    apply (hf.mul hk).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hh.mul hg).continuousAt |>.mp
    filter_upwards [he, hg_ne, hk_ne] with z hz hgz hkz
    exact (div_eq_div_iff hgz hkz).mp hz

end
end Dubon2026.SourceFunctionField.CuspTaylor
