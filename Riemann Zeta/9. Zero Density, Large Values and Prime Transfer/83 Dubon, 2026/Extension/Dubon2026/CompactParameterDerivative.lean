import Dubon2026.CompactParameterIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Differentiation of a genuine finite parameter integral using compact joint continuity -/

namespace Dubon2026

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Actual pointwise derivatives and joint derivative continuity on a compact height interval justify differentiation under the finite integral. -/
theorem hasDerivAt_intervalIntegral_of_positive_compact_joint
    {F F' : ℝ → ℝ → ℂ} {x : ℝ} (hx : 0 < x) (a b : ℝ)
    (hF : ∀ y : ℝ, 0 < y → Continuous (F y))
    (hF' : ∀ t ∈ uIcc a b, ContinuousAt (Function.uncurry F') (x, t))
    (hd : ∀ y : ℝ, 0 < y → ∀ t ∈ uIcc a b, HasDerivAt (fun z => F z t) (F' y t) y) :
    HasDerivAt (fun y => ∫ t in a..b, F y t) (∫ t in a..b, F' x t) x := by
  have hc : ContinuousOn (F' x) (uIcc a b) := by
    intro t ht
    exact ((hF' t ht).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  have hbound : ∀ᶠ y in 𝓝 x, ∀ t ∈ uIcc a b, ‖F' y t‖ ≤ C + 1 := by
    apply isCompact_uIcc.eventually_forall_of_forall_eventually
    intro t ht
    exact ((hF' t ht).norm.eventually_lt_const (by
      change ‖F' x t‖ < C + 1
      linarith [hC t ht])).mono fun _ h => h.le
  let S : Set ℝ := {y | 0 < y ∧ ∀ t ∈ uIcc a b, ‖F' y t‖ ≤ C + 1}
  have hs : S ∈ 𝓝 x := by
    filter_upwards [isOpen_Ioi.mem_nhds hx, hbound] with y hy hB
    exact ⟨hy, hB⟩
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (uIoc a b)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (hF y hy).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (F' x) (volume.restrict (uIoc a b)) :=
    (intervalIntegrable_iff.mp hc.intervalIntegrable).aestronglyMeasurable
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => C + 1) hs hmeas ((hF x hx).intervalIntegrable a b)
    hdmeas (Eventually.of_forall fun t ht y hy => hy.2 t (uIoc_subset_uIcc ht))
    intervalIntegrable_const (Eventually.of_forall fun t ht y hy => hd y hy.1 t (uIoc_subset_uIcc ht))).2

end
end Dubon2026
