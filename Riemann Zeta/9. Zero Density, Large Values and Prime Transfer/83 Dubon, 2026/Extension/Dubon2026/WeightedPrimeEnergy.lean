import Dubon2026.DeligneConcentration

namespace Dubon2026
open Filter Set
open scoped Topology

/-- Dyadic prime powers vary by a bounded factor, independently of the coefficient amplitudes. -/
theorem weighted_prime_energy_log_error {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) {N : ℕ} (hN : 1 ≤ N)
    (hm : 0 < ∑ p ∈ Q N, ‖a p‖ ^ 2) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy a Q N σ) -
      (Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) - 2 * σ * Real.log N)| ≤ 2 * M * Real.log 2 := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlow := Finset.sum_le_sum (s := Q N) fun p hp =>
    mul_le_mul_of_nonneg_left (selected_prime_power_bounds hQ hN hσ hp).1 (sq_nonneg ‖a p‖)
  have hhigh := Finset.sum_le_sum (s := Q N) fun p hp =>
    mul_le_mul_of_nonneg_left (selected_prime_power_bounds hQ hN hσ hp).2 (sq_nonneg ‖a p‖)
  rw [← Finset.sum_mul] at hlow hhigh
  have hr := Real.rpow_pos_of_pos hn (-2*σ)
  have h := abs_log_sub_log_le_of_exp_bounds (Y := isolatedPrimeEnergy a Q N σ) (mul_pos hm hr)
    (by convert hlow using 1; ring) (by convert hhigh using 1; ring)
  rw [Real.log_mul hm.ne' hr.ne', Real.log_rpow hn] at h
  convert h.2 using 1; ring_nf

theorem energy_mass_normalized_error {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) {N : ℕ} (hN : 2 ≤ N)
    (hmass : 0 < ∑ p ∈ Q N, ‖a p‖ ^ 2) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy a Q N σ) /
      (2 * Real.log N) - (1 / 2 - σ)| ≤
        (2 * M * Real.log 2) / (2 * Real.log N) +
          |Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) / Real.log N - 1| / 2 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := weighted_prime_energy_log_error hQ (by omega : 1 ≤ N) hmass hσ
  have hdiv := div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 2 * Real.log N)
  have he : Real.log (isolatedPrimeEnergy a Q N σ) /
      (2 * Real.log N) - (1 / 2 - σ) =
      (Real.log (isolatedPrimeEnergy a Q N σ) -
        (Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) - 2 * σ * Real.log N)) / (2 * Real.log N) +
          (Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) / Real.log N - 1) / 2 := by
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.log N), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add hdiv le_rfl

theorem tendstoLocallyUniformly_weighted_prime_energy {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q)
    (hmass : ∀ᶠ N in atTop, 0 < ∑ p ∈ Q N, ‖a p‖ ^ 2)
    (hlogmass : Tendsto (fun N => Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) / Real.log N) atTop (𝓝 1)) :
    TendstoLocallyUniformly
      (fun N : ℕ => fun σ : ℝ =>
        Real.log (isolatedPrimeEnergy a Q N σ) / (2 * Real.log N))
      (fun σ => 1 / 2 - σ) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let M := max |x - 1| |x + 1|
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => (2 * M * Real.log 2) / (2 * Real.log N) +
      |Real.log (∑ p ∈ Q N, ‖a p‖ ^ 2) / Real.log N - 1| / 2) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun N : ℕ => (2 * M * Real.log 2) / (2 * Real.log N)) atTop (𝓝 0) :=
      (hlogN.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop _
    simpa only [sub_self, abs_zero, zero_div, add_zero] using
      hfirst.add ((hlogmass.sub_const 1).abs.div_const 2)
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  filter_upwards [hbound.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℕ),
    hmass] with N hb hN hm
  intro σ hσ
  have hs : |σ| ≤ M := by
    apply abs_le.mpr
    have hl := (neg_abs_le (x - 1)).trans hσ.1
    have hu := hσ.2.trans (le_abs_self (x + 1))
    have hMl : |x - 1| ≤ M := le_max_left _ _
    have hMu : |x + 1| ≤ M := le_max_right _ _
    constructor <;> linarith
  rw [Real.dist_eq, abs_sub_comm]
  exact (energy_mass_normalized_error hQ hN hm hs).trans_lt hb


end Dubon2026
