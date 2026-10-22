import Dubon2026.SourceCellRadialCompact
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Pointwise

/-! DUB-17/18 -> raw geometric reciprocity -> cellwise primitives.
An actual radial cell admits an open star-convex neighborhood inside any
prescribed open chart target. Native compact-set thickening and addition of
star-convex sets replace the source's scaled-radius and distance estimates.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Set Complex Metric
open scoped Real Pointwise

theorem center_mem_K (R : RadialRegion) : R.q ∈ R.K := by
  change ‖R.q - R.q‖ ≤ R.r (arg (R.q - R.q))
  simpa only [sub_self, norm_zero] using (R.hpos (arg (0 : ℂ))).le

theorem starConvex_K (R : RadialRegion) : StarConvex ℝ R.q R.K := by
  intro z hz a t ha ht hat
  have hz' : ‖z - R.q‖ ≤ R.r (arg (z - R.q)) := hz
  change ‖a • R.q + t • z - R.q‖ ≤ R.r (arg (a • R.q + t • z - R.q))
  have he : a • R.q + t • z - R.q = (t : ℂ) * (z - R.q) := by
    have ha' : a = 1 - t := by linarith
    rw [ha']
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [he]
  rcases ht.lt_or_eq with ht0 | ht0
  · rw [arg_real_mul _ ht0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith : t ≤ 1)).trans hz'
  · rw [← ht0]
    simpa only [ofReal_zero, zero_mul, norm_zero] using (R.hpos (arg (0 : ℂ))).le

theorem exists_open_starConvex_neighborhood (R : RadialRegion) (T : Set ℂ)
    (hT : IsOpen T) (hKT : R.K ⊆ T) :
    ∃ V : Set ℂ, IsOpen V ∧ R.q ∈ V ∧ StarConvex ℝ R.q V ∧ R.K ⊆ V ∧ V ⊆ T := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_K R).exists_thickening_subset_open hT hKT
  have hsc : StarConvex ℝ R.q (thickening δ R.K) := by
    rw [← add_ball_zero]
    simpa only [add_zero] using
      (starConvex_K R).add ((convex_ball (0 : ℂ) δ).starConvex (mem_ball_self hδ))
  have hK := self_subset_thickening hδ R.K
  exact ⟨thickening δ R.K, isOpen_thickening, hK (center_mem_K R), hsc, hK, hsub⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
