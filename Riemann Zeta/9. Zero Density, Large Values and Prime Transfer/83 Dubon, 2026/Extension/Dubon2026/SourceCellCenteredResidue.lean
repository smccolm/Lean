import Dubon2026.SourceCellPrimitiveContour
import Dubon2026.SourceCellCenteredWinding

/-! DUB-17/18 -> raw reciprocity -> pole-centered cell residue identity.
Remove the one simple principal part, fill its analytic remainder at the center,
and integrate. The holomorphic part vanishes by constructed radial primitives;
the principal part uses the proved centered logarithmic integral. This serves
the source dissection whose pole cells are centered at their unique poles.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Real Topology

theorem centered_residue (R : RadialRegion) (f : ℂ → ℂ) (c : ℂ)
    (hf : ∀ z ∈ R.K, z ≠ R.q → AnalyticAt ℂ f z)
    (hp : ∃ g : ℂ → ℂ, AnalyticAt ℂ g R.q ∧
      ∀ᶠ z in 𝓝[≠] R.q, f z = c / (z - R.q) + g z) :
    IntervalIntegrable (fun φ => f (R.loop φ) * R.loop' φ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), f (R.loop φ) * R.loop' φ) = 2 * π * I * c := by
  classical
  obtain ⟨g, hga, hge⟩ := hp
  let F : ℂ → ℂ := Function.update (fun z => f z - c / (z - R.q)) R.q (g R.q)
  have hFeq : ∀ z, z ≠ R.q → F z = f z - c / (z - R.q) :=
    fun z hz => Function.update_of_ne hz _ _
  have hF0 : F =ᶠ[𝓝 R.q] g := by
    rw [eventually_nhdsWithin_iff] at hge
    filter_upwards [hge] with z hz
    by_cases hn : z = R.q
    · subst z
      simp only [F, Function.update_self]
    · rw [hFeq z hn, hz hn]
      ring
  have hFa : ∀ z ∈ R.K, AnalyticAt ℂ F z := by
    intro z hz
    by_cases hn : z = R.q
    · subst z
      exact hga.congr hF0.symm
    have hloc : F =ᶠ[𝓝 z] fun w => f w - c / (w - R.q) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hn] with w hw
      exact hFeq w hw
    exact ((hf z hz hn).sub (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hn))).congr hloc.symm
  obtain ⟨hFint, hFzero⟩ := R.integral_eq_zero_of_analyticOnNhd F hFa
  obtain ⟨hWint, hW⟩ := R.centered_winding
  have hdecomp : (fun φ => f (R.loop φ) * R.loop' φ) =
      (fun φ => F (R.loop φ) * R.loop' φ) +
        (fun φ => c * (R.loop' φ / (R.loop φ - R.q))) := by
    funext φ
    simp only [Pi.add_apply]
    rw [hFeq _ (R.loop_ne_center φ)]
    ring
  rw [hdecomp]
  refine ⟨hFint.add (hWint.const_mul c), ?_⟩
  change (∫ φ in (0 : ℝ)..(2 * π),
    F (R.loop φ) * R.loop' φ + c * (R.loop' φ / (R.loop φ - R.q))) = _
  rw [intervalIntegral.integral_add hFint (hWint.const_mul c), hFzero,
    intervalIntegral.integral_const_mul, hW]
  ring

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
