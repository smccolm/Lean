import Dubon2026.HarmonicPowerEnergy

/-! # Deriving H1 for bounded coefficients from the genuine isolated-prime energy -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem eventually_isolatedPrimeEnergy_pos {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (hQ : IsolatedPrimeBlocks Q) (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    ∀ᶠ N in atTop, ∀ σ, 0 < isolatedPrimeEnergy a Q N σ := by
  filter_upwards [eventually_primeBlock_coefficients_ne_zero hc,
    hcard.eventually_ge_atTop 1] with N hn hcardN
  intro σ
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Q N).card by omega)
  apply Finset.sum_pos'
  · intro q _
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  · refine ⟨p, hp, mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (hn p hp))) ?_⟩
    exact Real.rpow_pos_of_pos (by exact_mod_cast (hQ N p hp).1.pos) _

/-- The lower estimate is obtained from the actual subset of coefficient terms.
Only H2 is assumed here; the global H1 conclusion is derived, including its corner. -/
theorem globalEnergyAsymptotic_of_bounded_isolated {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (ha : a 1 = 1) (hb : ∀ n, ‖a n‖ ≤ 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q (1 / 2))
    (hH2 : IsolatedEnergyAsymptotic a Q (1 / 2)) :
    GlobalEnergyAsymptotic a (1 / 2) := by
  intro σ
  have hu : Tendsto (fun N : ℕ => max (1 / 2 - σ) 0 +
      (Real.log (harmonic N : ℝ) / Real.log N) / 2) atTop (𝓝 (max (1 / 2 - σ) 0)) := by
    simpa only [zero_div, add_zero] using
      tendsto_const_nhds.add (tendsto_log_harmonic_ratio.div_const 2)
  have hupper : ∀ᶠ N : ℕ in atTop,
      Real.log (coefficientEnergy a N σ) / (2 * Real.log N) ≤
        max (1 / 2 - σ) 0 + (Real.log (harmonic N : ℝ) / Real.log N) / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact coefficientEnergy_log_upper hb ha hN σ
  by_cases hσ : σ < 1 / 2
  · have hl : Tendsto (fun N : ℕ => Real.log (isolatedPrimeEnergy a Q N σ) /
        (2 * Real.log N)) atTop (𝓝 (max (1 / 2 - σ) 0)) := by
      simpa only [max_eq_left (sub_nonneg.mpr hσ.le)] using hH2.tendsto_at hσ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ hupper
    filter_upwards [eventually_isolatedPrimeEnergy_pos hQ hcard hc,
      eventually_ge_atTop (2 : ℕ)] with N hp hN
    apply div_le_div_of_nonneg_right
      (Real.log_le_log (hp σ) (isolatedPrimeEnergy_le_coefficientEnergy hQ N σ))
    positivity
  · have hz : max (1 / 2 - σ) 0 = 0 := max_eq_right (by linarith)
    have hl : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (max (1 / 2 - σ) 0)) := by
      rw [hz]
      exact tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ hupper
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact div_nonneg (Real.log_nonneg (one_le_coefficientEnergy (by omega) ha σ))
      (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))

end Dubon2026
