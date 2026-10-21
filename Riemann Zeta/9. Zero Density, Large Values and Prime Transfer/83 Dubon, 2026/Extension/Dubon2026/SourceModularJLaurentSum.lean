import Dubon2026.SourceModularJNumeratorSum
import Dubon2026.SourceAnalyticJInvariant

/-! DUB-17/18 -> original parabolic Hecke realization -> cusp-form lower
dimension bound -> differential expansion -> finite original function-field
extension -> modular polynomial relations -> analytic realization of the
literal j Laurent series. Pinned Eisenstein coefficients, the actual analytic
discriminant and its convergent product are used. Formal principal coefficients
alone are not treated as analytic modularity or as a field-degree proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_hasSum_jq_qParam.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology ModularForm OnePoint
local notation "𝕢" => Function.Periodic.qParam

theorem hasSum_jq_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((Dubon2026.SourceFunctionField.jq.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
  set q : ℂ := 𝕢 1 (τ : ℂ) with hqdef
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have h := (hasSum_jNum_qParam τ).mul_left q⁻¹
  rw [← hqdef, inv_mul_cancel_left₀ hq] at h

  have hinj : Function.Injective fun n : ℕ => (n : ℤ) - 1 := fun a b hab => by
    simpa using hab
  rw [← hinj.hasSum_iff]
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply]
    rw [jq, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, sub_add_cancel, jNumQ,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, Rat.cast_intCast,
      zpow_sub_one₀ hq, zpow_natCast]
    ring
  · intro m hm
    have hm' : m < -1 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m + 1).toNat, by simp; omega⟩
    rw [coeff_jq_of_lt hm', Rat.cast_zero, zero_mul]
end
end Dubon2026.SourceFunctionField
