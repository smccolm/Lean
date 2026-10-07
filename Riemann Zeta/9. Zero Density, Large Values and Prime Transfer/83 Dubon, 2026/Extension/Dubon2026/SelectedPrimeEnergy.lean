import Dubon2026.SelectedPrimeBounds
import Dubon2026.SelectedPrimeDensity

/-! # Deriving H2 from positive prime density and bounded selected coefficients -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem selected_energy_normalized_error {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q) {N : ℕ} (hN : 2 ≤ N)
    (hcard : 0 < (Q N).card)
    (ha : ∀ p ∈ Q N, 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) {σ M : ℝ} (hσ : |σ| ≤ M) :
    |Real.log (isolatedPrimeEnergy a Q N σ) /
      (2 * Real.log N) - (1 / 2 - σ)| ≤
        (Real.log 4 + 2 * M * Real.log 2) / (2 * Real.log N) +
          |Real.log (Q N).card / Real.log N - 1| / 2 := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb := selected_prime_energy_log_error hQ (by omega : 1 ≤ N) hcard ha hσ
  have hdiv := div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 2 * Real.log N)
  have he : Real.log (isolatedPrimeEnergy a Q N σ) /
      (2 * Real.log N) - (1 / 2 - σ) =
      (Real.log (isolatedPrimeEnergy a Q N σ) -
        (Real.log (Q N).card - 2 * σ * Real.log N)) / (2 * Real.log N) +
          (Real.log (Q N).card / Real.log N - 1) / 2 := by
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.log N), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add hdiv le_rfl

theorem tendstoLocallyUniformly_selected_energy {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (hQ : IsolatedPrimeBlocks Q)
    (ha : ∀ᶠ N in atTop, ∀ p ∈ Q N, 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hlogcard : Tendsto (fun N => Real.log (Q N).card / Real.log N) atTop (𝓝 1)) :
    TendstoLocallyUniformly
      (fun N : ℕ => fun σ : ℝ =>
        Real.log (isolatedPrimeEnergy a Q N σ) / (2 * Real.log N))
      (fun σ => 1 / 2 - σ) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let M := max |x - 1| |x + 1|
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => (Real.log 4 + 2 * M * Real.log 2) / (2 * Real.log N) +
      |Real.log (Q N).card / Real.log N - 1| / 2) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun N : ℕ => (Real.log 4 + 2 * M * Real.log 2) / (2 * Real.log N)) atTop (𝓝 0) :=
      (hlogN.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop _
    simpa only [sub_self, abs_zero, zero_div, add_zero] using
      hfirst.add ((hlogcard.sub_const 1).abs.div_const 2)
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  filter_upwards [hbound.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℕ),
    hcard.eventually_ge_atTop 1, ha] with N hb hN hc haN
  intro σ hσ
  have hs : |σ| ≤ M := by
    apply abs_le.mpr
    have hl := (neg_abs_le (x - 1)).trans hσ.1
    have hu := hσ.2.trans (le_abs_self (x + 1))
    have hMl : |x - 1| ≤ M := le_max_left _ _
    have hMu : |x + 1| ≤ M := le_max_right _ _
    constructor <;> linarith
  rw [Real.dist_eq, abs_sub_comm]
  exact (selected_energy_normalized_error hQ hN (by omega) haN hs).trans_lt hb

/-- The actual selected dyadic block satisfies all parts of H2, conditional on its
prime density and the explicitly displayed coefficient bounds. -/
theorem selected_primes_H2 {a : ℕ → ℂ} {S : ℕ → Prop} {η : ℝ} (hη : 0 < η)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo S N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 η))
    (ha : ∀ p, Nat.Prime p → S p → 1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) :
    IsolatedPrimeBlocks (selectedDyadicPrimes S) ∧
      Tendsto (fun N => (selectedDyadicPrimes S N).card) atTop atTop ∧
      PrimeCoefficientComparability a (selectedDyadicPrimes S) (1 / 2) ∧
      IsolatedEnergyAsymptotic a (selectedDyadicPrimes S) (1 / 2) := by
  have hQ := isolatedPrimeBlocks_selectedDyadicPrimes S
  have hr := selected_dyadic_density hd
  have hc : 0 < η / 2 := by linarith
  have hcard := tendsto_card_of_positive_prime_scale hc hr
  have hlog := tendsto_log_card_of_positive_prime_scale hc hr
  have hb : ∀ᶠ N in atTop, ∀ p ∈ selectedDyadicPrimes S N,
      1 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2 := by
    apply Eventually.of_forall
    intro N p hp
    have hh := mem_selectedDyadicPrimes.mp hp
    exact ha p hh.1.1 hh.2
  exact ⟨hQ, hcard, primeCoefficientComparability_of_selected_bounds hQ hb _,
    (tendstoLocallyUniformly_selected_energy hQ hb hcard hlog).tendstoLocallyUniformlyOn⟩

end Dubon2026
