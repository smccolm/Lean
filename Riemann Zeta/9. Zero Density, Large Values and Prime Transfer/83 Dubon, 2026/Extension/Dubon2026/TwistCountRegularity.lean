import Dubon2026.TwistCountPartition
import Dubon2026.HorizontalPhaseZeros

/-! # Almost-everywhere continuity of the actual open-rectangle zero count -/

namespace Dubon2026

open Filter Set MeasureTheory Complex
open scoped Topology

noncomputable section

/-- The actual multiplicity count is Haar-almost-everywhere continuous, with no
restriction excluding atoms at either vertical endpoint. -/
theorem ae_continuousAt_twistZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    ∀ᵐ z ∂torusHaar N, ContinuousAt (twistZeroCount a N hN ha l u H) z := by
  by_cases hlu : l < u
  · have hl₀ : l - 1 < l := by linarith
    have hu₀ : u < u + 1 := by linarith
    filter_upwards [ae_torus_vertical_count_continuous hN ha hl₀ (hlu.trans hu₀) H,
      ae_torus_vertical_count_continuous hN ha (hl₀.trans hlu) hu₀ H,
      ae_horizontal_phase_closed_segment_ne_zero hN ha (l - 1) (u + 1) (-H),
      ae_horizontal_phase_closed_segment_ne_zero hN ha (l - 1) (u + 1) H] with z hcl hcu hbot htop
    have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
    obtain ⟨L, hL, hnL⟩ := exists_zero_free_vertical_line hN haz hl₀
    obtain ⟨U, hU, hnU⟩ := exists_zero_free_vertical_line hN haz hu₀
    have hLU : L ≤ U := (hL.2.trans (hlu.trans hU.1)).le
    have hn : ∀ s ∈ RectangleBorder (⟨L, -H⟩ : ℂ) (⟨U, H⟩ : ℂ),
        dirichletSum (twistedCoefficients a N z) N s ≠ 0 := by
      intro s hs
      rcases hs with ((hs | hs) | hs) | hs
      · have hre : L ≤ s.re ∧ s.re ≤ U := by
          simpa only [uIcc_of_le hLU] using hs.1
        exact hbot s (hL.1.le.trans hre.1) (hre.2.trans hU.2.le) hs.2
      · exact hnL s hs.1
      · have hre : L ≤ s.re ∧ s.re ≤ U := by
          simpa only [uIcc_of_le hLU] using hs.1
        exact htop s (hL.1.le.trans hre.1) (hre.2.trans hU.2.le) hs.2
      · exact hnU s hs.1
    have ht := eventually_eq_twistZeroCount_of_boundary_ne_zero hN ha z hLU hH hn
    have hle : ∀ᶠ w in 𝓝 z, twistVerticalLineZeroCount a N hN ha L U H l w =
        twistVerticalLineZeroCount a N hN ha L U H l z := by
      have hh := hcl.eventually ((isOpen_discrete
        {twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H l z}).mem_nhds rfl)
      filter_upwards [hh] with w hw
      change twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H l w =
        twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H l z at hw
      simpa only [twistVerticalLineZeroCount_eq_of_bounds hN ha hl₀ (hlu.trans hu₀)
        hL.2 (hlu.trans hU.1)] using hw
    have hue : ∀ᶠ w in 𝓝 z, twistVerticalLineZeroCount a N hN ha L U H u w =
        twistVerticalLineZeroCount a N hN ha L U H u z := by
      have hh := hcu.eventually ((isOpen_discrete
        {twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H u z}).mem_nhds rfl)
      filter_upwards [hh] with w hw
      change twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H u w =
        twistVerticalLineZeroCount a N hN ha (l - 1) (u + 1) H u z at hw
      simpa only [twistVerticalLineZeroCount_eq_of_bounds hN ha (hl₀.trans hlu) hu₀
        (hL.2.trans hlu) hU.1] using hw
    have he := eventually_eq_twistZeroCount_of_line_counts hN ha hL.2 hlu hU.1 z ht hle hue
    exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  · have he : twistZeroCount a N hN ha l u H = fun _ => 0 := by
      funext z
      exact verticalZeroCount_empty_interval hN (by rwa [twistedCoefficients_one]) (le_of_not_gt hlu) H
    rw [he]
    exact Filter.Eventually.of_forall fun _ => continuousAt_const

/-- The fixed-polynomial height limit exists for every open strip, including
strips whose vertical endpoints support Jessen atoms. -/
theorem tendsto_zeroDensity_torus_mean {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T))
      atTop (𝓝 ((∫ z, (twistZeroCount a N hN ha l u 1 z : ℝ) ∂torusHaar N) / 2)) :=
  tendsto_zeroDensity_of_twist_count_ae_continuous hN ha l u
    (ae_continuousAt_twistZeroCount hN ha l u zero_le_one)

end

end Dubon2026
