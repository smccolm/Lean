import Dubon2026.SourceCellBoundaryDifferentiation
import Dubon2026.SourceCellArcFundamentalTheorem
import Dubon2026.SourceCellRadialPrimitive
import Dubon2026.SourceCellRadialNeighborhood

/-! DUB-17/18 -> raw reciprocity -> centered cell residue contour.
Actual radial primitives make holomorphic boundary integrals vanish. This
replaces the external two-dimensional Green formula for the holomorphic
regular part; the exact source piecewise C2 boundary is retained.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Set MeasureTheory
open scoped Real

theorem integral_eq_zero_of_primitive (R : RadialRegion) (f Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ R.K, HasDerivAt Φ (f z) z)
    (hf : ∀ z ∈ R.K, ContinuousAt f z) :
    IntervalIntegrable (fun φ => f (R.loop φ) * R.loop' φ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), f (R.loop φ) * R.loop' φ) = 0 := by
  have hfc : Continuous (fun φ => f (R.loop φ)) :=
    continuous_iff_continuousAt.mpr fun φ =>
      (hf _ (R.loop_mem_K φ)).comp R.continuous_loop.continuousAt
  have hΦc : Continuous (fun φ => Φ (R.loop φ)) :=
    continuous_iff_continuousAt.mpr fun φ =>
      (hΦ _ (R.loop_mem_K φ)).continuousAt.comp R.continuous_loop.continuousAt
  have hd : ∀ k : Fin R.N, ∀ φ ∈ Ioo (R.φs k.castSucc) (R.φs k.succ),
      HasDerivAt (fun φ => Φ (R.loop φ)) (f (R.loop φ) * R.loop' φ) φ :=
    fun k φ hφ => (hΦ _ (R.loop_mem_K φ)).comp φ (R.hasDerivAt_loop k hφ)
  have hext : ∀ k : Fin R.N, ∃ g : ℝ → ℂ, Continuous g ∧
      EqOn (fun φ => f (R.loop φ) * R.loop' φ) g (Ioo (R.φs k.castSucc) (R.φs k.succ)) := by
    intro k
    refine ⟨fun φ => f (R.loop φ) * R.loopDerivOnArc k φ,
      hfc.mul (R.continuous_loopDerivOnArc k), ?_⟩
    intro φ hφ
    dsimp only
    rw [R.loop'_eq_loopDerivOnArc k hφ]
  obtain ⟨hint, he⟩ := R.integral_eq_sub_of_arc_derivatives _ _ hΦc hd hext
  have hclose : R.loop (2 * π) = R.loop 0 := by simpa only [zero_add] using R.loop_periodic 0
  rw [hclose, sub_self] at he
  exact ⟨hint, he⟩

theorem integral_eq_zero_of_analyticOnNhd (R : RadialRegion) (f : ℂ → ℂ)
    (hf : ∀ z ∈ R.K, AnalyticAt ℂ f z) :
    IntervalIntegrable (fun φ => f (R.loop φ) * R.loop' φ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), f (R.loop φ) * R.loop' φ) = 0 := by
  obtain ⟨V, hVo, _, hVs, hKV, hVf⟩ := R.exists_open_starConvex_neighborhood
    {z | AnalyticAt ℂ f z} (isOpen_analyticAt ℂ f) hf
  obtain ⟨Φ, _, hΦ⟩ := exists_radial_primitive hVo hVs
    (fun z hz => (hVf hz).differentiableAt.differentiableWithinAt)
  exact R.integral_eq_zero_of_primitive f Φ (fun z hz => hΦ z (hKV hz))
    (fun z hz => (hf z hz).continuousAt)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
