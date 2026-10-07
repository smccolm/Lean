import Dubon2026.PhaseDerivatives

/-! # Continuity of a parameter integral near a compact interval

Joint continuity is required at the base parameter along the interval. Nearby
interval integrability is kept explicit, permitting application to a logarithmic
derivative whose poles lie outside the contour under consideration.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

theorem continuousAt_intervalIntegral_of_compact_joint {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℂ} (x : X) (a b : ℝ)
    (hc : ∀ t ∈ uIcc a b, ContinuousAt (Function.uncurry f) (x, t))
    (hi : ∀ᶠ y in 𝓝 x, IntervalIntegrable (f y) volume a b) :
    ContinuousAt (fun y => ∫ t in a..b, f y t) x := by
  have hix : IntervalIntegrable (f x) volume a b := hi.self_of_nhds
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (|b - a| + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : ∀ᶠ y in 𝓝 x, ∀ t ∈ uIcc a b, ‖f y t - f x t‖ < δ := by
    apply (isCompact_uIcc : IsCompact (uIcc a b)).eventually_forall_of_forall_eventually
    intro t ht
    have hs₀ : ContinuousAt (fun u : ℝ => f x u) t :=
      (hc t ht).comp (continuousAt_const.prodMk continuousAt_id)
    have hs : ContinuousAt (fun yt : X × ℝ => f x yt.2) (x, t) :=
      hs₀.comp continuousAt_snd
    have hh := ((hc t ht).sub hs).norm.eventually_lt continuousAt_const
      (by simpa using hδ)
    exact hh
  filter_upwards [hi, he] with y hiy hey
  rw [dist_eq_norm, ← intervalIntegral.integral_sub hiy hix]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => (hey t (uIoc_subset_uIcc ht)).le)
  apply hb.trans_lt
  calc
    δ * |b - a| < δ * (|b - a| + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ ε (by positivity : |b - a| + 1 ≠ 0)

end Dubon2026
