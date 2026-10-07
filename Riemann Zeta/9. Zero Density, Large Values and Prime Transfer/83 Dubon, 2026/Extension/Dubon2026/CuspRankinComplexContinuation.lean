import Dubon2026.CuspRankinRealContinuation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! # The actual Rankin unfolding identity throughout the complex convergence half-plane -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter Set
open scoped Topology

noncomputable section

/-- The actual continued Eisenstein cusp integral is analytic on the entire convergence half-plane. -/
theorem gamma0CuspEisensteinContinuation_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    AnalyticOnNhd ℂ (gamma0CuspEisensteinContinuation f) {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change 1 < s.re at hs
  exact (differentiableAt_gamma0CuspEisensteinContinuation f (by linarith [hs]) (by
    intro h
    simp only [h, Complex.one_re, lt_self_iff_false] at hs)).differentiableWithinAt

/-- The Gamma factor times the true normalized square series is analytic on the convergence half-plane. -/
theorem cuspRankinFactor_mul_series_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) :
    AnalyticOnNhd ℂ (fun s => cuspRankinFactor k s * cuspRankinSeries f s)
      {s : ℂ | 1 < s.re} := by
  have hF : AnalyticOnNhd ℂ (cuspRankinFactor k) {s : ℂ | 1 < s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    change 1 < s.re at hs
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
    exact (differentiableAt_cuspRankinFactor k (by linarith [hs])).differentiableWithinAt
  exact hF.mul (cuspRankinSeries_analyticOnNhd f hk)

/-- The actual primitive Eisenstein cusp integral equals the normalized Rankin series with its precise Gamma factor for every Re(s)>1. -/
theorem gamma0CuspEisensteinContinuation_eq_rankin {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    gamma0CuspEisensteinContinuation f s = cuspRankinFactor k s * cuspRankinSeries f s := by
  have ht : Tendsto Complex.ofReal (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [Complex.ofReal_ofNat] using
        (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change (x : ℂ) ≠ (2 : ℂ)
      exact_mod_cast ne_of_gt hx
  have he : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      gamma0CuspEisensteinContinuation f z = cuspRankinFactor k z * cuspRankinSeries f z := by
    apply ht.frequently
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 2 < x at hx
    exact gamma0CuspEisensteinContinuation_real f hk (by linarith [hx])
  exact (gamma0CuspEisensteinContinuation_analyticOnNhd f).eqOn_of_preconnected_of_frequently_eq
    (cuspRankinFactor_mul_series_analyticOnNhd f hk) (convex_halfSpace_re_gt 1).isPreconnected
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num) he hs

end
end Dubon2026
