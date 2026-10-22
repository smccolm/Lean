import Dubon2026.SourceAnalyticLaurentQuotients
import Dubon2026.SourceJModularQuotient

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
The actual original j Laurent series belongs to the field of analytic
Taylor quotients. This consumes its proved E4-cube/discriminant expansion
and native analytic cusp functions. The q-expansion/Taylor bridge is an
exact coefficient identity, not a new convergence assumption.
-/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open UpperHalfPlane
open scoped ModularForm

theorem series_cuspFunction (h : ℝ) (f : ℍ → ℂ) :
    series (cuspFunction h f) = qExpansion h f := by
  ext n
  rw [coeff_series, qExpansion_coeff]
  ring

theorem series_mem_realizedField {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    (series f : LaurentSeries ℂ) ∈ realizedField := by
  refine ⟨f, fun _ => (1 : ℂ), hf, analyticAt_const, ?_, ?_⟩
  · rw [series_const]
    simp
  · rw [series_const]
    simp

theorem qExpansion_mem_realizedField (h : ℝ) (f : ℍ → ℂ)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    (qExpansion h f : LaurentSeries ℂ) ∈ realizedField := by
  rw [← series_cuspFunction]
  exact series_mem_realizedField hf

theorem jqModC_mem_realizedField : jqModC ℂ ∈ realizedField := by
  have h4 : (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : LaurentSeries ℂ) ∈ realizedField :=
    qExpansion_mem_realizedField 1 _
      (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL)
  have hΔ : (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ∈ realizedField :=
    qExpansion_mem_realizedField 1 _
      (ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL)
  rw [jqModC_eq_modular_quotient]
  exact div_mem (pow_mem h4 3) hΔ

end
end Dubon2026.SourceFunctionField.CuspTaylor
