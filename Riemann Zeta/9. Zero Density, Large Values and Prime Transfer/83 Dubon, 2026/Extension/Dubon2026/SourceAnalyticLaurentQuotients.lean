import Dubon2026.SourceScalarTaylorSeries
import Mathlib.RingTheory.LaurentSeries

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
Quotients of the actual Taylor series of analytic complex germs form a
subfield of the literal Laurent-series field. Inversion just exchanges
the two analytic germs, avoiding a separate convergence proof for formal
inverse series. The original cusp generators must still be shown to lie
in this subfield before it supplies their analytic realization.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section

/-- A literal Laurent series represented by the quotient of two analytic Taylor germs. -/
def RationallyRealized (A : LaurentSeries ℂ) : Prop :=
  ∃ f g : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
    (series g : LaurentSeries ℂ) ≠ 0 ∧
    A = (series f : LaurentSeries ℂ) / (series g : LaurentSeries ℂ)

theorem rationallyRealized_const (c : ℂ) : RationallyRealized (algebraMap ℂ (LaurentSeries ℂ) c) := by
  refine ⟨fun _ => c, fun _ => 1, analyticAt_const, analyticAt_const, ?_, ?_⟩
  · rw [series_const]
    simp
  · rw [series_const, series_const]
    simp [LaurentSeries.algebraMap_apply]

theorem RationallyRealized.add {A B : LaurentSeries ℂ}
    (hA : RationallyRealized A) (hB : RationallyRealized B) : RationallyRealized (A + B) := by
  obtain ⟨f, g, hf, hg, hg0, rfl⟩ := hA
  obtain ⟨h, k, hh, hk, hk0, rfl⟩ := hB
  refine ⟨f * k + h * g, g * k, (hf.mul hk).add (hh.mul hg), hg.mul hk, ?_, ?_⟩
  · rw [series_mul hg hk, PowerSeries.coe_mul]
    exact mul_ne_zero hg0 hk0
  · rw [series_add (hf.mul hk) (hh.mul hg), series_mul hf hk, series_mul hh hg,
      series_mul hg hk, PowerSeries.coe_add, PowerSeries.coe_mul,
      PowerSeries.coe_mul, PowerSeries.coe_mul]
    rw [div_add_div _ _ hg0 hk0]
    congr 1
    ring

theorem RationallyRealized.mul {A B : LaurentSeries ℂ}
    (hA : RationallyRealized A) (hB : RationallyRealized B) : RationallyRealized (A * B) := by
  obtain ⟨f, g, hf, hg, hg0, rfl⟩ := hA
  obtain ⟨h, k, hh, hk, hk0, rfl⟩ := hB
  refine ⟨f * h, g * k, hf.mul hh, hg.mul hk, ?_, ?_⟩
  · rw [series_mul hg hk, PowerSeries.coe_mul]
    exact mul_ne_zero hg0 hk0
  · rw [series_mul hf hh, series_mul hg hk, PowerSeries.coe_mul, PowerSeries.coe_mul]
    exact div_mul_div_comm _ _ _ _

theorem RationallyRealized.inv {A : LaurentSeries ℂ} (hA : RationallyRealized A) :
    RationallyRealized A⁻¹ := by
  by_cases hA0 : A = 0
  · rw [hA0, inv_zero]
    simpa only [map_zero] using rationallyRealized_const 0
  obtain ⟨f, g, hf, hg, hg0, hAeq⟩ := hA
  have hf0 : (series f : LaurentSeries ℂ) ≠ 0 := by
    intro h
    apply hA0
    rw [hAeq, h, zero_div]
  exact ⟨g, f, hg, hf, hf0, by rw [hAeq, inv_div]⟩

/-- The actual intermediate field of analytic Taylor quotients in the Laurent field. -/
def realizedField : IntermediateField ℂ (LaurentSeries ℂ) where
  carrier := RationallyRealized
  zero_mem' := by simpa only [map_zero] using rationallyRealized_const 0
  one_mem' := by simpa only [map_one] using rationallyRealized_const 1
  add_mem' := RationallyRealized.add
  mul_mem' := RationallyRealized.mul
  inv_mem' := fun _ h => h.inv
  algebraMap_mem' := rationallyRealized_const

end
end Dubon2026.SourceFunctionField.CuspTaylor
