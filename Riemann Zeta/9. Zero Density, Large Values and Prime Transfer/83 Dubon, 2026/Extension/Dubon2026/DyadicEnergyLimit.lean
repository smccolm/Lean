import Dubon2026.DyadicEnergyBounds
import Dubon2026.DyadicPrimeGrowth

/-! # The locally uniform isolated-prime energy hypothesis for zeta coefficients -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem dyadic_energy_normalized_error {N : ℕ} (hN : 2 ≤ N)
    (hcard : 0 < (dyadicPrimes N).card) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ) /
      (2 * Real.log N) - (1 / 2 - σ)| ≤
        (2 * M * Real.log 2) / (2 * Real.log N) +
          |Real.log (dyadicPrimes N).card / Real.log N - 1| / 2 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := isolatedPrimeEnergy_one_log_error (by omega : 1 ≤ N) hcard hσ
  have hdiv := div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 2 * Real.log N)
  have he : Real.log (isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ) /
      (2 * Real.log N) - (1 / 2 - σ) =
      (Real.log (isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ) -
        (Real.log (dyadicPrimes N).card - 2 * σ * Real.log N)) / (2 * Real.log N) +
          (Real.log (dyadicPrimes N).card / Real.log N - 1) / 2 := by
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.log N), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add hdiv le_rfl

theorem tendstoLocallyUniformly_dyadic_energy :
    TendstoLocallyUniformly
      (fun N : ℕ => fun σ : ℝ =>
        Real.log (isolatedPrimeEnergy (fun _ => (1 : ℂ)) dyadicPrimes N σ) / (2 * Real.log N))
      (fun σ => 1 / 2 - σ) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let M := max |x - 1| |x + 1|
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => (2 * M * Real.log 2) / (2 * Real.log N) +
      |Real.log (dyadicPrimes N).card / Real.log N - 1| / 2) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun N : ℕ => (2 * M * Real.log 2) / (2 * Real.log N)) atTop (𝓝 0) :=
      (hlogN.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop _
    simpa only [sub_self, abs_zero, zero_div, add_zero] using
      hfirst.add ((tendsto_log_card_dyadicPrimes_ratio.sub_const 1).abs.div_const 2)
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  filter_upwards [hbound.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℕ),
    tendsto_card_dyadicPrimes.eventually_ge_atTop 1] with N hb hN hc
  intro σ hσ
  have hs : |σ| ≤ M := by
    apply abs_le.mpr
    have hl := (neg_abs_le (x - 1)).trans hσ.1
    have hu := hσ.2.trans (le_abs_self (x + 1))
    have hMl : |x - 1| ≤ M := le_max_left _ _
    have hMu : |x + 1| ≤ M := le_max_right _ _
    constructor <;> linarith
  rw [Real.dist_eq, abs_sub_comm]
  exact (dyadic_energy_normalized_error hN (by omega) hs).trans_lt hb

theorem isolatedEnergyAsymptotic_one :
    IsolatedEnergyAsymptotic (fun _ => (1 : ℂ)) dyadicPrimes (1 / 2) :=
  tendstoLocallyUniformly_dyadic_energy.tendstoLocallyUniformlyOn

end Dubon2026
