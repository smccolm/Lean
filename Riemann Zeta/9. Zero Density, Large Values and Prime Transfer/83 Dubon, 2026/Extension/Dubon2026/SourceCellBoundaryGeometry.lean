import Dubon2026.SourceCellPeriodicRadius
import Dubon2026.SourceCellRadialRegion
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> centered cell residue contour.
The exact radial boundary lies in the cell, avoids its center and closes after
one positive turn. These facts connect the actual cell coefficient and primitive
domains to the boundary integrals; no curve dissection is assumed constructed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Complex Set
open scoped Real

variable (R : RadialRegion)

theorem loop_sub_center (φ : ℝ) : R.loop φ - R.q = (R.r φ : ℂ) * exp (φ * I) := by
  simp [loop]

theorem norm_loop_sub_center (φ : ℝ) : ‖R.loop φ - R.q‖ = R.r φ := by
  rw [R.loop_sub_center, norm_mul, norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_of_nonneg (R.hpos φ).le]

theorem radius_arg_loop (φ : ℝ) : R.r (arg (R.loop φ - R.q)) = R.r φ := by
  rw [R.loop_sub_center]
  exact periodic_apply_arg R.hper (R.hpos φ) φ

theorem loop_mem_K (φ : ℝ) : R.loop φ ∈ R.K := by
  change ‖R.loop φ - R.q‖ ≤ R.r (arg (R.loop φ - R.q))
  rw [R.norm_loop_sub_center, R.radius_arg_loop]

theorem loop_ne_center (φ : ℝ) : R.loop φ ≠ R.q := by
  intro h
  have hn := R.norm_loop_sub_center φ
  rw [h, sub_self, norm_zero] at hn
  exact (R.hpos φ).ne' hn.symm

theorem loop_periodic : Function.Periodic R.loop (2 * π) := by
  intro φ
  simp only [loop, R.hper φ, ofReal_add, add_mul, exp_add]
  have he : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    convert exp_two_pi_mul_I using 1; push_cast; ring
  rw [he, mul_one]

theorem continuous_loop : Continuous R.loop := by
  have hc := R.hcont
  unfold loop
  fun_prop

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
