import Dubon2026.SourceCellRadialRegion
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic

/-! DUB-17/18 -> raw geometric reciprocity -> analytic cells -> open radial
neighborhoods admitting primitives. Native continuity of the complex argument
as an angle and the periodic lift to AddCircle replace a manual branch-cut
argument. Only the radius hypotheses used by the source cells are required.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Set Complex
open scoped Real

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π))
    {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

theorem continuousAt_periodic_radius_arg {r : ℝ → ℝ} (hc : Continuous r)
    (hp : Function.Periodic r (2 * π)) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w => r (arg w)) z := by
  letI : Fact (0 < 2 * π) := ⟨by positivity⟩
  let f : Real.Angle → ℝ := AddCircle.liftIoc (2 * π) (-π) r
  have hf : Continuous f := AddCircle.liftIoc_continuous (hp (-π)).symm hc.continuousOn
  have he : ∀ w : ℂ, f (arg w) = r (arg w) := by
    intro w
    apply AddCircle.liftIoc_coe_apply
    exact ⟨neg_pi_lt_arg w, by linarith [arg_le_pi w]⟩
  have h := hf.continuousAt.comp (continuousAt_arg_coe_angle hz)
  simpa only [Function.comp_def, he] using h

end
end Dubon2026.SourceFunctionField.CellGeometry
