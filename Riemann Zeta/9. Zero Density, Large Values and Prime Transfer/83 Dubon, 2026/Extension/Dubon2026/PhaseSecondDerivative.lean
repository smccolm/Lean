import Dubon2026.PhaseCurvatureBand

/-! # A second derivative integral bound for the actual complex phase -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A true phase with negative frequency derivative admits the usual second derivative bound,
with an explicit free splitting threshold and all three actual intervals accounted for. -/
theorem norm_phase_integral_le_of_frequency_curvature {ν : ℝ → ℝ} {z : ℝ → ℂ}
    (hν : Differentiable ℝ ν) (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t)
    (hz0 : ‖z 0‖ = 1) {a b δ lam : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hlam : 0 < lam)
    (hcurv : ∀ t ∈ Icc a b, deriv ν t ≤ -δ) :
    ‖∫ t in a..b, z t‖ ≤ 2 * lam / δ + 4 / lam := by
  have hmono : AntitoneOn ν (Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hν.continuous.continuousOn
      hν.differentiableOn (fun t ht => (hcurv t (interior_subset ht)).trans (by linarith))
  have hnonneg : 0 ≤ 2 * lam / δ := by positivity
  have hrec : 2 / lam ≤ 4 / lam := div_le_div_of_nonneg_right (by norm_num) hlam.le
  by_cases ha : ν a ≤ -lam
  · have hh := norm_phase_integral_le_of_negative_frequency hν.continuous hz hz0 hab hlam
      (fun t ht => (hmono ⟨le_rfl, hab⟩ ht ht.1).trans ha) hmono
    exact hh.trans (hrec.trans (le_add_of_nonneg_left hnonneg))
  by_cases hb : lam ≤ ν b
  · have hh := norm_phase_integral_le_of_positive_frequency hν.continuous hz hz0 hab hlam
      (fun t ht => hb.trans (hmono ht ⟨hab, le_rfl⟩ ht.2)) hmono
    exact hh.trans (hrec.trans (le_add_of_nonneg_left hnonneg))
  obtain ⟨l, r, hl, hr, hlr, hlv, hrv, hle, hre⟩ :=
    exists_frequency_band_endpoints hν.continuous hab hlam hmono (lt_of_not_ge ha) (lt_of_not_ge hb)
  have hlen := frequency_band_length_le hν hδ hl hr hlr hcurv hlv hrv
  have hleft : ‖∫ t in a..l, z t‖ ≤ 2 / lam := by
    rcases hle with rfl | hle
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · apply norm_phase_integral_le_of_positive_frequency hν.continuous hz hz0 hl.1 hlam
      · intro t ht
        rw [← hle]
        exact hmono ⟨ht.1, ht.2.trans hl.2⟩ hl ht.2
      · intro t ht u hu htu
        exact hmono ⟨ht.1, ht.2.trans hl.2⟩ ⟨hu.1, hu.2.trans hl.2⟩ htu
  have hright : ‖∫ t in r..b, z t‖ ≤ 2 / lam := by
    rcases hre with rfl | hre
    · simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · apply norm_phase_integral_le_of_negative_frequency hν.continuous hz hz0 hr.2 hlam
      · intro t ht
        rw [← hre]
        exact hmono hr ⟨hr.1.trans ht.1, ht.2⟩ ht.1
      · intro t ht u hu htu
        exact hmono ⟨hr.1.trans ht.1, ht.2⟩ ⟨hr.1.trans hu.1, hu.2⟩ htu
  have hnorm (t : ℝ) : ‖z t‖ = 1 := (norm_phase_eq_initial hν.continuous hz t).trans hz0
  have hmiddle : ‖∫ t in l..r, z t‖ ≤ r - l := by
    calc
      _ ≤ ∫ t in l..r, ‖z t‖ := intervalIntegral.norm_integral_le_integral_norm hlr
      _ = r - l := by simp only [hnorm, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hc : Continuous z := continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  have he : (∫ t in a..b, z t) =
      (∫ t in a..l, z t) + (∫ t in l..r, z t) + (∫ t in r..b, z t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  rw [he]
  have htri := (norm_add_le ((∫ t in a..l, z t) + (∫ t in l..r, z t)) (∫ t in r..b, z t)).trans
    (add_le_add (norm_add_le (∫ t in a..l, z t) (∫ t in l..r, z t)) le_rfl)
  linarith [show 4 / lam = 2 / lam + 2 / lam by ring]

/-- At reciprocal scale 1/(2T), the proved frequency-curvature estimate yields the explicit square-root bound. -/
theorem norm_phase_integral_le_sqrt_scale {ν : ℝ → ℝ} {z : ℝ → ℂ}
    (hν : Differentiable ℝ ν) (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t)
    (hz0 : ‖z 0‖ = 1) {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    (hcurv : ∀ t ∈ Icc a b, deriv ν t ≤ -(1 / (2 * T))) :
    ‖∫ t in a..b, z t‖ ≤ 8 * Real.sqrt T := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hh := norm_phase_integral_le_of_frequency_curvature hν hz hz0 hab
    (by positivity : 0 < 1 / (2 * T)) (by positivity : 0 < 1 / Real.sqrt T) hcurv
  apply hh.trans_eq
  have hsq := Real.sq_sqrt hT.le
  field_simp
  nlinarith

end
end Dubon2026
