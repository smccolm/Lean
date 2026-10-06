import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # One-sided derivatives and the Stieltjes measure of a finite convex function -/

namespace Dubon2026

open Set Filter Function
open scoped Topology

noncomputable section

theorem monotone_convex_rightDeriv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    Monotone (fun x => derivWithin f (Ioi x) x) := by
  intro x y hxy
  exact hf.monotoneOn_rightDeriv (by simp) (by simp) hxy

theorem continuousAt_slope_left {f : ℝ → ℝ} (hf : Continuous f)
    {x y : ℝ} (hxy : x ≠ y) : ContinuousAt (fun u => slope f u y) x := by
  simp only [slope_def_field]
  exact (continuousAt_const.sub hf.continuousAt).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hxy.symm)

theorem rightLim_convex_rightDeriv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    rightLim (fun u => derivWithin f (Ioi u) u) x = derivWithin f (Ioi x) x := by
  have hm := monotone_convex_rightDeriv hf
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  apply le_antisymm ?_ (hm.le_rightLim le_rfl)
  have hb (y : ℝ) (hxy : x < y) :
      rightLim (fun u => derivWithin f (Ioi u) u) x ≤ slope f x y := by
    apply le_of_tendsto_of_tendsto (hm.tendsto_rightLim x)
      ((continuousAt_slope_left hc hxy.ne).tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [eventually_lt_nhds hxy |>.filter_mono nhdsWithin_le_nhds] with u hu
    exact hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ _) hu
  have hd := (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Ioi x by simp)).mp
    (hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp : x ∈ interior univ))
  apply ge_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hb y hy

theorem leftLim_convex_rightDeriv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    leftLim (fun u => derivWithin f (Ioi u) u) x = derivWithin f (Iio x) x := by
  have hm := monotone_convex_rightDeriv hf
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hd := (hasDerivWithinAt_iff_tendsto_slope' (show x ∉ Iio x by simp)).mp
    (hf.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp : x ∈ interior univ))
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto (hm.tendsto_leftLim x) hd
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [slope_comm]
    exact hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ _) hu
  · have hb (y : ℝ) (hyx : y < x) :
        slope f y x ≤ leftLim (fun u => derivWithin f (Ioi u) u) x := by
      have hs : Tendsto (fun u => slope f y u) (𝓝[<] x) (𝓝 (slope f y x)) := by
        simpa only [slope_comm] using
          (continuousAt_slope_left hc hyx.ne.symm).tendsto.mono_left nhdsWithin_le_nhds
      apply le_of_tendsto_of_tendsto hs (hm.tendsto_leftLim x)
      filter_upwards [eventually_gt_nhds hyx |>.filter_mono nhdsWithin_le_nhds] with u hu
      exact (hf.slope_le_leftDeriv_of_mem_interior (mem_univ _) (by simp) hu).trans
        (hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp))
    apply le_of_tendsto hd
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [slope_comm]
    exact hb y hy

/-- The Stieltjes function of the actual right derivative of a finite convex function. -/
def convexDerivativeStieltjes {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    StieltjesFunction ℝ :=
  (monotone_convex_rightDeriv hf).stieltjesFunction

theorem convexDerivativeStieltjes_apply {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    convexDerivativeStieltjes hf x = derivWithin f (Ioi x) x :=
  rightLim_convex_rightDeriv hf x

theorem leftLim_convexDerivativeStieltjes {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (x : ℝ) :
    leftLim (convexDerivativeStieltjes hf) x = derivWithin f (Iio x) x := by
  have he : (convexDerivativeStieltjes hf : ℝ → ℝ) =
      fun u => derivWithin f (Ioi u) u := funext (convexDerivativeStieltjes_apply hf)
  rw [he]
  exact leftLim_convex_rightDeriv hf x

theorem convexDerivativeStieltjes_measure_Ioo {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (a b : ℝ) :
    (convexDerivativeStieltjes hf).measure (Ioo a b) =
      ENNReal.ofReal (derivWithin f (Iio b) b - derivWithin f (Ioi a) a) := by
  rw [StieltjesFunction.measure_Ioo, leftLim_convexDerivativeStieltjes,
    convexDerivativeStieltjes_apply]

end

end Dubon2026
