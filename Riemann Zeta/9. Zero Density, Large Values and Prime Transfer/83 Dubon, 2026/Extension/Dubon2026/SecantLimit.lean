import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic

/-! # A vanishing secant error identifies the limiting derivative -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_of_approximate_secants {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {D e : ι → ℝ} {σ d : ℝ}
    (hF : ∀ x : ℝ, Tendsto (fun i => F i x) L (𝓝 (G x)))
    (he : Tendsto e L (𝓝 0)) (hd : HasDerivAt G d σ)
    (hl : ∀ l : ℝ, l < σ → ∀ᶠ i in L, slope (F i) l σ - e i ≤ D i)
    (hu : ∀ u : ℝ, σ < u → ∀ᶠ i in L, D i ≤ slope (F i) σ u + e i) :
    Tendsto D L (𝓝 d) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hleft := (hasDerivWithinAt_iff_tendsto_slope' (show σ ∉ Iio σ by simp)).mp
      (hd.hasDerivWithinAt (s := Iio σ))
    have hmem : ∀ᶠ l in 𝓝[<] σ, l < σ := self_mem_nhdsWithin
    obtain ⟨l, hls, hbl⟩ := (hmem.and ((tendsto_order.mp hleft).1 b hb)).exists
    have hlim : Tendsto (fun i => slope (F i) l σ - e i) L (𝓝 (slope G l σ)) := by
      simpa only [slope_def_field, sub_zero] using ((hF σ).sub (hF l)).div_const (σ - l) |>.sub he
    have hbound : b < slope G l σ := by simpa only [slope_comm] using hbl
    filter_upwards [hl l hls, (tendsto_order.mp hlim).1 b hbound] with i hdi hbi
    exact hbi.trans_le hdi
  · intro b hb
    have hright := (hasDerivWithinAt_iff_tendsto_slope' (show σ ∉ Ioi σ by simp)).mp
      (hd.hasDerivWithinAt (s := Ioi σ))
    have hmem : ∀ᶠ u in 𝓝[>] σ, σ < u := self_mem_nhdsWithin
    obtain ⟨u, hsu, hub⟩ := (hmem.and ((tendsto_order.mp hright).2 b hb)).exists
    have hlim : Tendsto (fun i => slope (F i) σ u + e i) L (𝓝 (slope G σ u)) := by
      simpa only [slope_def_field, add_zero] using ((hF u).sub (hF σ)).div_const (u - σ) |>.add he
    filter_upwards [hu u hsu, (tendsto_order.mp hlim).2 b hub] with i hdi hib
    exact hdi.trans_lt hib

end Dubon2026
