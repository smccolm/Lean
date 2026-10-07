import Dubon2026.GammaRieszCompact

/-! # Sharp uniform power bounds for the actual improper Riesz Gamma kernels -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate

noncomputable section

/-- The actual low interval before the stationary window has a uniform fixed-parameter bound. -/
theorem norm_gammaRiesz_low_integral_le {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    ‖∫ t in gammaRieszBaseHeight k..gammaRieszWindowHeight k x, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  have hC := gammaRieszConstant_pos k r
  by_cases he : gammaRieszBaseHeight k = gammaRieszWindowHeight k x
  · rw [he, intervalIntegral.integral_same, norm_zero]
    positivity
  have hh := norm_gammaRieszIntegrand_lower_interval_le hk hr0 hr2 hx
    (gammaRieszBaseHeight_properties k).1 (gammaRieszBaseHeight_properties k).2
    (gammaRieszWindowHeight_ge k x) (le_of_eq (gammaRieszWindowHeight_log he).symm)
  apply hh.trans
  exact div_le_self (by positivity)
    (by simpa using Real.sqrt_le_sqrt (show 1 ≤ gammaRieszBaseHeight k by
      linarith [(gammaRieszBaseHeight_properties k).1]))

/-- Exactly two genuine dyadic blocks cover the entire stationary window. -/
theorem norm_gammaRiesz_window_integral_le {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    ‖∫ t in gammaRieszWindowHeight k x..4 * gammaRieszWindowHeight k x, gammaRieszIntegrand k r x t‖ ≤
      16 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  let S := gammaRieszWindowHeight k x
  have h128 : 128 ≤ S := (gammaRieszBaseHeight_properties k).1.trans (gammaRieszWindowHeight_ge k x)
  have hkS : 21 + 2 * k ≤ S := (gammaRieszBaseHeight_properties k).2.trans (gammaRieszWindowHeight_ge k x)
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  have h1 := norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx h128 hkS
    (le_refl S) (show S ≤ 2 * S by linarith) (le_refl (2 * S))
  have h2 := norm_gammaRieszIntegrand_integral_le hk hr0 hr2 hx
    (show 128 ≤ 2 * S by linarith) (show 21 + 2 * k ≤ 2 * S by linarith)
    (le_refl (2 * S)) (show 2 * S ≤ 4 * S by linarith) (show 4 * S ≤ 2 * (2 * S) by linarith)
  change ‖∫ t in S..4 * S, gammaRieszIntegrand k r x t‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable S (2 * S))
    (hc.intervalIntegrable (2 * S) (4 * S))]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- The actual high tail after the stationary window is uniformly bounded, regardless of its endpoint. -/
theorem norm_gammaRiesz_high_integral_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hu : 4 * gammaRieszWindowHeight k x ≤ u) :
    ‖∫ t in 4 * gammaRieszWindowHeight k x..u, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r := by
  have hC := gammaRieszConstant_pos k r
  have hh := norm_gammaRieszIntegrand_tail_le hk hr0 hr2 hx (gammaRieszTailHeight_le_four_window k x) hu
  apply hh.trans
  exact div_le_self (by positivity)
    (by simpa using Real.sqrt_le_sqrt (show 1 ≤ 4 * gammaRieszWindowHeight k x by
      linarith [(gammaRieszBaseHeight_properties k).1, gammaRieszWindowHeight_ge k x]))

/-- Every sufficiently long finite positive cutoff satisfies the same sharp power bound. -/
theorem norm_gammaRiesz_cutoff_integral_le {k r x u : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hu : 4 * gammaRieszWindowHeight k x ≤ u) :
    ‖∫ t in 0..u, gammaRieszIntegrand k r x t‖ ≤
      (gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) * x ^ gammaRieszLine r := by
  let H := gammaRieszBaseHeight k
  let S := gammaRieszWindowHeight k x
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  have he : (∫ t in 0..u, gammaRieszIntegrand k r x t) =
      (∫ t in 0..H, gammaRieszIntegrand k r x t) +
      (∫ t in H..S, gammaRieszIntegrand k r x t) +
      (∫ t in S..4 * S, gammaRieszIntegrand k r x t) +
      (∫ t in 4 * S..u, gammaRieszIntegrand k r x t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 H) (hc.intervalIntegrable H S),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 S) (hc.intervalIntegrable S (4 * S)),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (4 * S)) (hc.intervalIntegrable (4 * S) u)]
  rw [he]
  have hn := (norm_add_le
    ((∫ t in 0..H, gammaRieszIntegrand k r x t) + (∫ t in H..S, gammaRieszIntegrand k r x t) +
      (∫ t in S..4 * S, gammaRieszIntegrand k r x t)) (∫ t in 4 * S..u, gammaRieszIntegrand k r x t)).trans
      (add_le_add norm_add₃_le le_rfl)
  apply hn.trans
  have hb := add_le_add (add_le_add (add_le_add
    (norm_gammaRieszIntegrand_compact_integral_le hx k r)
    (norm_gammaRiesz_low_integral_le hk hr0 hr2 hx))
    (norm_gammaRiesz_window_integral_le hk hr0 hr2 hx))
    (norm_gammaRiesz_high_integral_le hk hr0 hr2 hx hu)
  convert hb using 1
  ring

/-- Passing to the proved improper limit preserves the sharp power with a constant independent of x. -/
theorem norm_gammaRieszPositiveIntegral_le {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    ‖gammaRieszPositiveIntegral k r x‖ ≤
      (gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) * x ^ gammaRieszLine r :=
  le_of_tendsto (tendsto_gammaRieszPositiveIntegral hk hr0 hr2 hx).norm
    ((eventually_ge_atTop (4 * gammaRieszWindowHeight k x)).mono fun _ hu =>
      norm_gammaRiesz_cutoff_integral_le hk hr0 hr2 hx hu)

/-- The genuine normalized symmetric Riesz kernel has its exact sharp power with an explicit fixed-parameter constant. -/
theorem norm_gammaRieszKernel_le {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    ‖gammaRieszKernel k r x‖ ≤
      ((gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) / Real.pi) * x ^ gammaRieszLine r := by
  have hh := norm_gammaRieszPositiveIntegral_le hk hr0 hr2 hx
  rw [gammaRieszKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖gammaRieszPositiveIntegral k r x‖ + ‖conj (gammaRieszPositiveIntegral k r x)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (2 * ((gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) * x ^ gammaRieszLine r)) := by
      rw [norm_conj]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

/-- Uniform sharp bounds hold for the actual improper kernel at every positive Mellin argument. -/
theorem exists_gammaRieszKernel_bound {k r : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → ‖gammaRieszKernel k r x‖ ≤ C * x ^ (3 / 8 - r / 4) := by
  refine ⟨(gammaRieszCompactMass k r + 24 * gammaRieszConstant k r) / Real.pi, ?_, ?_⟩
  · exact div_pos (by linarith [gammaRieszCompactMass_nonneg k r, gammaRieszConstant_pos k r]) Real.pi_pos
  · intro x hx
    exact norm_gammaRieszKernel_le hk hr0 hr2 hx

end
end Dubon2026
