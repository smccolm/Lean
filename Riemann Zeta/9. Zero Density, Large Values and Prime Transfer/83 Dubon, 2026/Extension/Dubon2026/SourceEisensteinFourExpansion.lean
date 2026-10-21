import Dubon2026.SourceModularJSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! DUB-17/18 -> original parabolic Hecke realization -> cusp-form lower
dimension bound -> differential expansion -> finite original function-field
extension -> modular polynomial relations -> analytic realization of the
literal j Laurent series. Pinned Eisenstein coefficients, the actual analytic
discriminant and its convergent product are used. Formal principal coefficients
alone are not treated as analytic modularity or as a field-degree proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology ModularForm OnePoint
local notation "𝕢" => Function.Periodic.qParam

theorem qExpansion_E4_eq_map_eisenstein4 : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) Dubon2026.SourceFunctionField.eisenstein4 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩ m, PowerSeries.coeff_map, eisenstein4,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four,
      ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast]
    push_cast
    ring
end
end Dubon2026.SourceFunctionField
