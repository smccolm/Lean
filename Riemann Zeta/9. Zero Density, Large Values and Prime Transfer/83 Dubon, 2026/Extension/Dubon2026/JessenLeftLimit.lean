import Dubon2026.UniformLogIntegral

/-! # Terminal affine asymptote of the actual Jessen function -/

namespace Dubon2026

open MeasureTheory Filter Set
open scoped Topology

theorem log_scaledBohr_ae {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    (fun z => Real.log ‖scaledBohr a N σ z‖) =ᵐ[torusHaar N]
      (fun z => σ * Real.log (lastIndex a N) + Real.log ‖bohrOnTorus a N σ z‖) := by
  filter_upwards [bohrOnTorus_ne_zero_ae hN ha σ] with z hz
  rw [scaledBohr_eq_smul, ContinuousMap.smul_apply, smul_eq_mul, norm_mul,
    Complex.norm_of_nonneg (Real.exp_pos _).le,
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hz), Real.log_exp]

theorem integrable_scaledBohr_log {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    Integrable (fun z => Real.log ‖scaledBohr a N σ z‖) (torusHaar N) :=
  ((integrable_const (σ * Real.log (lastIndex a N))).add
    (integrable_bohrOnTorus_log a N σ)).congr (log_scaledBohr_ae hN ha σ).symm

theorem integral_log_scaledBohr {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    (∫ z, Real.log ‖scaledBohr a N σ z‖ ∂torusHaar N) =
      jessenFunction a N σ + σ * Real.log (lastIndex a N) := by
  rw [integral_congr_ae (log_scaledBohr_ae hN ha σ),
    integral_add (integrable_const _) (integrable_bohrOnTorus_log a N σ),
    integral_const, probReal_univ, one_smul, jessenFunction_eq_haar hN ha]
  exact add_comm _ _

theorem tendsto_jessenFunction_affine_atBot {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (fun σ => jessenFunction a N σ + σ * Real.log (lastIndex a N)) atBot
      (𝓝 (Real.log ‖a (lastIndex a N)‖)) := by
  have hlim := tendsto_integral_log_of_constant_modulus_limit
    (norm_pos_iff.mpr (coefficient_lastIndex_ne_zero hN ha))
    (norm_terminal_bohr_term a N) (tendsto_scaledBohr_atBot hN ha)
    (integrable_scaledBohr_log hN ha)
  simpa only [integral_log_scaledBohr hN ha] using hlim

theorem tendsto_jessen_derivatives_atBot {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (fun x => derivWithin (jessenFunction a N) (Iio x) x) atBot
      (𝓝 (-Real.log (lastIndex a N))) ∧
    Tendsto (fun x => derivWithin (jessenFunction a N) (Ioi x) x) atBot
      (𝓝 (-Real.log (lastIndex a N))) := by
  apply tendsto_convex_derivatives_atBot (convexOn_jessenFunction hN ha)
  simpa only [neg_mul, mul_neg, sub_neg_eq_add, mul_comm] using
    tendsto_jessenFunction_affine_atBot hN ha

theorem tendsto_jessenStieltjes_atBot {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    Tendsto (jessenStieltjes hN ha) atBot (𝓝 (-Real.log (lastIndex a N))) := by
  change Tendsto (fun x => jessenStieltjes hN ha x) atBot (𝓝 (-Real.log (lastIndex a N)))
  simpa only [jessenStieltjes_apply] using (tendsto_jessen_derivatives_atBot hN ha).2

end Dubon2026
