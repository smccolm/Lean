import Dubon2026.DyadicPrimes
import Dubon2026.PrimeCountingPNT

/-! # Pinned PNT consumers at the exact dyadic-prime normalization

The direct PNT adapter follows the existing node-73 normalization method;
the endpoint convention here is the actual source block (N/2,N].
-/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_log_mul_nat_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (c * N) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun N : ℕ => Real.log c / Real.log N + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using (hlog.const_div_atTop (Real.log c)).add_const 1
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [Real.log_mul hc.ne' (by positivity : (N : ℝ) ≠ 0), add_div,
    div_self (Real.log_pos hNr).ne']

/-- Actual inclusive prime counting at any fixed positive multiple of N. -/
theorem tendsto_primeCounting_scaled {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (Nat.primeCounting ⌊c * N⌋₊ : ℝ) / ((N : ℝ) / Real.log N))
      atTop (𝓝 c) := by
  obtain ⟨δ, hδ, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hδ
  simp only [div_one] at hδ
  have hcN : Tendsto (fun N : ℕ => c * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlim : Tendsto (fun N : ℕ => (1 + δ (c * N)) * c /
      (Real.log (c * N) / Real.log N)) atTop (𝓝 c) := by
    simpa only [add_zero, one_mul, div_one] using
      (((hδ.comp hcN).const_add 1).mul_const c).div (tendsto_log_mul_nat_ratio hc) one_ne_zero
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), hcN.eventually_gt_atTop 1] with N hN hcN'
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [hpi (c * N)]
  field_simp [(Real.log_pos hNr).ne', (Real.log_pos hcN').ne',
    (by positivity : (N : ℝ) ≠ 0)]

/-- The exact source prime-block cardinality, normalized by N/log N, tends to 1/2. -/
theorem tendsto_card_dyadicPrimes_ratio :
    Tendsto (fun N : ℕ => ((dyadicPrimes N).card : ℝ) / ((N : ℝ) / Real.log N))
      atTop (𝓝 (1 / 2)) := by
  have hfull : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log N))
      atTop (𝓝 1) := by
    simpa only [one_mul, Nat.floor_natCast] using tendsto_primeCounting_scaled (c := 1) (by norm_num)
  have hhalf : Tendsto (fun N : ℕ => (Nat.primeCounting (N / 2) : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (1 / 2)) := by
    have he (N : ℕ) : (1 / 2 : ℝ) * N = (N : ℝ) / (2 : ℕ) := by push_cast; ring
    simpa only [he, Nat.floor_div_eq_div] using tendsto_primeCounting_scaled (c := 1 / 2) (by norm_num)
  have hh := hfull.sub hhalf
  norm_num at hh
  convert hh using 1
  funext N
  rw [card_dyadicPrimes, Nat.cast_sub (Nat.monotone_primeCounting (Nat.div_le_self N 2)), sub_div]

end Dubon2026
