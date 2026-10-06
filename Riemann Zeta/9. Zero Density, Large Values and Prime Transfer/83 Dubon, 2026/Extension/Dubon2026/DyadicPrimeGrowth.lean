import Dubon2026.PrimeCountAsymptotics
import Dubon2026.LogarithmicScale

/-! # Growth and logarithmic scale of the exact isolated-prime block -/

namespace Dubon2026

open Filter
open scoped Topology

theorem tendsto_nat_div_log_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log N) atTop atTop := by
  have hp := pi_alt'.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpi : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  apply hp.tendsto_atTop
  simpa only [Function.comp_def, Nat.floor_natCast] using hpi

theorem tendsto_card_dyadicPrimes : Tendsto (fun N => (dyadicPrimes N).card) atTop atTop := by
  have hh := tendsto_card_dyadicPrimes_ratio.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    tendsto_nat_div_log_atTop
  have hcast : Tendsto (fun N => ((dyadicPrimes N).card : ℝ)) atTop atTop := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact div_mul_cancel₀ _ (div_ne_zero (by positivity) (Real.log_pos hNr).ne')
  exact tendsto_natCast_atTop_iff.mp hcast

theorem tendsto_log_card_dyadicPrimes_ratio :
    Tendsto (fun N => Real.log (dyadicPrimes N).card / Real.log N) atTop (𝓝 1) := by
  apply tendsto_log_scaled_ratio (by norm_num : (0 : ℝ) < 1 / 2)
    (g := fun N => (N : ℝ) / Real.log N) ?_ tendsto_card_dyadicPrimes_ratio
    tendsto_log_nat_div_log_ratio
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (by positivity) (Real.log_pos hNr)

end Dubon2026
