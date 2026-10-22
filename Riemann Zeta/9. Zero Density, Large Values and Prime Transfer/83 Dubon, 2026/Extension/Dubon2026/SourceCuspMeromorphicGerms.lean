import Dubon2026.SourceTaylorQuotientGerms
import Dubon2026.SourceAnalyticLaurentQuotients

/-! DUB-17/18 -> original torsion cardinality -> cusp charts.
A meromorphic germ represents a literal Laurent series when it agrees
with an analytic Taylor quotient for that series. Quotient uniqueness
and field operations allow the original generators to be realized on
one common disk, rather than with unrelated function-dependent radii.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter
open scoped Topology

/-- An analytic Taylor quotient for the actual Laurent series, with its punctured germ. -/
def Represents (A : LaurentSeries ℂ) (F : ℂ → ℂ) : Prop :=
  ∃ f g : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
    (series g : LaurentSeries ℂ) ≠ 0 ∧
    A = (series f : LaurentSeries ℂ) / (series g : LaurentSeries ℂ) ∧
    F =ᶠ[𝓝[≠] (0 : ℂ)] f / g

theorem Represents.congr {A : LaurentSeries ℂ} {F G : ℂ → ℂ}
    (h : Represents A F) (he : G =ᶠ[𝓝[≠] (0 : ℂ)] F) : Represents A G := by
  obtain ⟨f, g, hf, hg, hg0, hA, hF⟩ := h
  exact ⟨f, g, hf, hg, hg0, hA, he.trans hF⟩

theorem Represents.unique {A : LaurentSeries ℂ} {F G : ℂ → ℂ}
    (hF : Represents A F) (hG : Represents A G) : F =ᶠ[𝓝[≠] (0 : ℂ)] G := by
  obtain ⟨f, g, hf, hg, hg0, hA, heF⟩ := hF
  obtain ⟨h, k, hh, hk, hk0, hA', heG⟩ := hG
  exact heF.trans (((quotient_eq_iff_eventuallyEq hf hg hh hk hg0 hk0).mp
    (hA.symm.trans hA')).trans heG.symm)

theorem represents_const (c : ℂ) : Represents (algebraMap ℂ (LaurentSeries ℂ) c) (fun _ => c) := by
  refine ⟨fun _ => c, fun _ => 1, analyticAt_const, analyticAt_const, ?_, ?_, ?_⟩
  · rw [series_const]
    simp
  · rw [series_const, series_const]
    simp [LaurentSeries.algebraMap_apply]
  · filter_upwards [] with z
    simp

theorem Represents.add {A B : LaurentSeries ℂ} {F G : ℂ → ℂ}
    (hF : Represents A F) (hG : Represents B G) : Represents (A + B) (F + G) := by
  obtain ⟨f, g, hf, hg, hg0, rfl, heF⟩ := hF
  obtain ⟨h, k, hh, hk, hk0, rfl, heG⟩ := hG
  have hg0' : series g ≠ 0 := fun he => hg0 (by rw [he, map_zero])
  have hk0' : series k ≠ 0 := fun he => hk0 (by rw [he, map_zero])
  refine ⟨f * k + h * g, g * k, (hf.mul hk).add (hh.mul hg), hg.mul hk, ?_, ?_, ?_⟩
  · rw [series_mul hg hk, PowerSeries.coe_mul]
    exact mul_ne_zero hg0 hk0
  · rw [series_add (hf.mul hk) (hh.mul hg), series_mul hf hk, series_mul hh hg,
      series_mul hg hk, PowerSeries.coe_add, PowerSeries.coe_mul,
      PowerSeries.coe_mul, PowerSeries.coe_mul]
    rw [div_add_div _ _ hg0 hk0]
    congr 1
    ring
  · filter_upwards [heF, heG, eventually_ne_zero_of_series_ne_zero hg hg0',
      eventually_ne_zero_of_series_ne_zero hk hk0'] with z hzF hzG hgz hkz
    change F z + G z = (f z * k z + h z * g z) / (g z * k z)
    rw [hzF, hzG]
    simpa only [Pi.div_apply, mul_comm] using div_add_div (f z) (h z) hgz hkz

theorem Represents.mul {A B : LaurentSeries ℂ} {F G : ℂ → ℂ}
    (hF : Represents A F) (hG : Represents B G) : Represents (A * B) (F * G) := by
  obtain ⟨f, g, hf, hg, hg0, rfl, heF⟩ := hF
  obtain ⟨h, k, hh, hk, hk0, rfl, heG⟩ := hG
  refine ⟨f * h, g * k, hf.mul hh, hg.mul hk, ?_, ?_, ?_⟩
  · rw [series_mul hg hk, PowerSeries.coe_mul]
    exact mul_ne_zero hg0 hk0
  · rw [series_mul hf hh, series_mul hg hk, PowerSeries.coe_mul, PowerSeries.coe_mul]
    exact div_mul_div_comm _ _ _ _
  · filter_upwards [heF, heG] with z hzF hzG
    change F z * G z = (f z * h z) / (g z * k z)
    rw [hzF, hzG]
    exact div_mul_div_comm _ _ _ _

theorem Represents.inv {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : Represents A F) : Represents A⁻¹ F⁻¹ := by
  by_cases hA : A = 0
  · subst A
    have hz : Represents 0 (fun _ : ℂ => (0 : ℂ)) := by
      simpa only [map_zero] using represents_const 0
    have he := hF.unique hz
    rw [inv_zero]
    apply hz.congr
    filter_upwards [he] with z hz
    simp only [Pi.inv_apply, hz, inv_zero]
  obtain ⟨f, g, hf, hg, hg0, hAeq, heF⟩ := hF
  have hf0 : (series f : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    apply hA
    rw [hAeq, hz, zero_div]
  refine ⟨g, f, hg, hf, hf0, by rw [hAeq, inv_div], ?_⟩
  filter_upwards [heF] with z hz
  change (F z)⁻¹ = g z / f z
  rw [hz, Pi.div_apply, inv_div]

end
end Dubon2026.SourceFunctionField.CuspTaylor
