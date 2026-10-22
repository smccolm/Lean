import Dubon2026.SourceAnalyticJTransformation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! DUB-17/18 -> regular-differential cusp forms -> analytic cusp decay.
The native q-expansion and discriminant cusp-form results give the actual
limits E4 -> 1 and inverse j -> 0. No general Fourier-series framework or
additional Eisenstein identities are needed for the monic-root bound.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped Topology ModularForm

theorem tendsto_E₄_atImInfty : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : cuspFunction 1 (E₄ : ℍ → ℂ) 0 = 1 := by
    simpa only [qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedDeriv_zero, one_mul] using
      (EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩)
  have ht := (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos
    one_mem_strictPeriods_SL).continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  simpa only [Function.comp_def,
    SlashInvariantFormClass.eq_cuspFunction E₄ _ one_mem_strictPeriods_SL one_ne_zero, h0] using ht

theorem tendsto_discriminant_atImInfty :
    Tendsto (ModularForm.discriminant : ℍ → ℂ) atImInfty (𝓝 0) :=
  CuspFormClass.zero_at_infty CuspForm.discriminant

theorem tendsto_inverse_j_atImInfty :
    Tendsto (fun τ : ℍ => (jf τ)⁻¹) atImInfty (𝓝 0) := by
  have ht := tendsto_discriminant_atImInfty.div (tendsto_E₄_atImInfty.pow 3)
    (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  simpa only [jf, inv_div, zero_div] using ht

theorem eventually_j_ne_zero_atImInfty : ∀ᶠ τ : ℍ in atImInfty, jf τ ≠ 0 := by
  filter_upwards [tendsto_E₄_atImInfty.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with τ hτ
  exact div_ne_zero (pow_ne_zero _ hτ) (discriminant_ne_zero τ)

end
end Dubon2026.SourceFunctionField.JMultiplicity
