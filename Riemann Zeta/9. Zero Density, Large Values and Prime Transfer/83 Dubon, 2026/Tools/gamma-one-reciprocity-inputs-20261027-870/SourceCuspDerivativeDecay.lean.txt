import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> derivative decay of the invariant untwist.
Existing modular derivative bounds require global holomorphy. Here the
translated normalized function is holomorphic only above some height;
native Cauchy estimates on unit disks give the needed precise variant.
Adapted from the Apache-2.0 scope-848 untwisting primary at commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open Filter Complex Metric Set
open scoped Topology

theorem eventually_imInf_iff {P : ℂ → Prop} :
    (∀ᶠ z in comap Complex.im atTop, P z) ↔ ∃ B : ℝ, ∀ z : ℂ, B ≤ z.im → P z := by
  rw [eventually_comap, eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun z hz => ha z.im hz z rfl⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, fun b hb z hz => hB z (by rw [hz]; exact hb)⟩

theorem tendsto_deriv_zero {f : ℂ → ℂ} {A : ℝ} (hf : ∀ z : ℂ, A < z.im → DifferentiableAt ℂ f z)
    {L : ℂ} (hL : Tendsto f (comap Complex.im atTop) (𝓝 L)) :
    Tendsto (deriv f) (comap Complex.im atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨B, hB⟩ := eventually_imInf_iff.1 (Metric.tendsto_nhds.1 hL (ε / 2) (half_pos hε))
  refine eventually_imInf_iff.2 ⟨max A B + 2, fun z hz => ?_⟩
  have hball : ∀ w ∈ Metric.closedBall z 1, max A B < w.im := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im] at this
    have := (abs_le.1 (this.trans hw)).1
    linarith
  have hd : DiffContOnCl ℂ (fun w => f w - L) (Metric.ball z 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z one_ne_zero]
    intro w hw
    exact ((hf w (lt_of_le_of_lt (le_max_left _ _) (hball w hw))).sub_const L).differentiableWithinAt
  have hC : ∀ w ∈ Metric.sphere z 1, ‖f w - L‖ ≤ ε / 2 := by
    intro w hw
    rw [← dist_eq_norm]
    exact (hB w (lt_of_le_of_lt (le_max_right _ _)
      (hball w (Metric.sphere_subset_closedBall hw))).le).le
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hd hC
  rw [div_one, deriv_sub_const] at hest
  rw [dist_zero_right]
  linarith

end
end Dubon2026.SourcePeriodUntwist
