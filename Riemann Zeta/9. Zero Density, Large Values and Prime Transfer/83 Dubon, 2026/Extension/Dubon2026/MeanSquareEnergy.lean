import Dubon2026.PrefixEnergyBounds
import Dubon2026.BoundedCoefficientEnergy

/-! # Deriving H1 from cumulative square sums and the actual isolated-prime lower bound -/

namespace Dubon2026

open Filter Set
open scoped Topology

/-- A convergent unweighted mean-square sequence gives a uniform bound on all
positive partial sums, including the finitely many initial indices. -/
theorem exists_prefix_square_bound_of_mean {a : ℕ → ℂ} {c : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N)
      atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N := by
  obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ hmean).bddAbove
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    exact (div_le_iff₀ hN0).mp ((hK ⟨N, rfl⟩).trans (le_max_left _ _))

theorem coefficientEnergy_log_upper_of_prefix {a : ℕ → ℂ} {C : ℝ} (hC : 0 < C)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N)
    (ha : a 1 = 1) {N : ℕ} (hN : 2 ≤ N) (σ : ℝ) :
    Real.log (coefficientEnergy a N σ) / (2 * Real.log N) ≤
      max (1 / 2 - σ) 0 + (Real.log C + Real.log (harmonic N : ℝ)) / (2 * Real.log N) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hH : 0 < (harmonic N : ℝ) := zero_lt_one.trans_le (one_le_real_harmonic (by omega))
  have hP := Real.rpow_pos_of_pos (zero_lt_one.trans hNr) (max (-2 * σ + 1) 0)
  have hE := Real.log_le_log (zero_lt_one.trans_le (one_le_coefficientEnergy (N := N) (by omega) ha σ))
    (coefficientEnergy_le_of_prefix_bound hC.le hb (by omega) σ)
  rw [Real.log_mul hC.ne' (mul_pos hP hH).ne', Real.log_mul hP.ne' hH.ne',
    Real.log_rpow (zero_lt_one.trans hNr)] at hE
  have hh := div_le_div_of_nonneg_right hE (by positivity : 0 ≤ 2 * Real.log N)
  have hm : max (-2 * σ + 1) 0 = 2 * max (1 / 2 - σ) 0 := by
    by_cases hs : σ ≤ 1 / 2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  convert hh using 1
  rw [hm]
  field_simp [(Real.log_pos hNr).ne']
  ring

/-- The lower estimate is obtained from the actual subset of coefficient terms.
The unweighted square-sum bound and H2 imply H1, including its corner. -/
theorem globalEnergyAsymptotic_of_prefix_isolated {a : ℕ → ℂ} {Q : ℕ → Finset ℕ}
    (ha : a 1 = 1) {C : ℝ} (hC : 0 < C)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q (1 / 2))
    (hH2 : IsolatedEnergyAsymptotic a Q (1 / 2)) :
    GlobalEnergyAsymptotic a (1 / 2) := by
  intro σ
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun N : ℕ =>
      (Real.log C + Real.log (harmonic N : ℝ)) / (2 * Real.log N)) atTop (𝓝 0) := by
    have hh := ((hlogN.const_div_atTop (Real.log C)).add tendsto_log_harmonic_ratio).div_const 2
    simpa only [add_zero, zero_div, add_div, div_div, mul_comm (Real.log _)] using hh
  have hu : Tendsto (fun N : ℕ => max (1 / 2 - σ) 0 +
      (Real.log C + Real.log (harmonic N : ℝ)) / (2 * Real.log N)) atTop (𝓝 (max (1 / 2 - σ) 0)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  have hupper : ∀ᶠ N : ℕ in atTop,
      Real.log (coefficientEnergy a N σ) / (2 * Real.log N) ≤
        max (1 / 2 - σ) 0 + (Real.log C + Real.log (harmonic N : ℝ)) / (2 * Real.log N) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact coefficientEnergy_log_upper_of_prefix hC hb ha hN σ
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
    exact div_nonneg (Real.log_nonneg (one_le_coefficientEnergy (N := N) (by omega) ha σ))
      (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))

/-- H1 from a genuine mean-square limit and H2. Neither is a zero-concentration conclusion. -/
theorem globalEnergyAsymptotic_of_mean_isolated {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {c : ℝ}
    (ha : a 1 = 1)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N)
      atTop (𝓝 c))
    (hQ : IsolatedPrimeBlocks Q) (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q (1 / 2))
    (hH2 : IsolatedEnergyAsymptotic a Q (1 / 2)) : GlobalEnergyAsymptotic a (1 / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_prefix_square_bound_of_mean hmean
  exact globalEnergyAsymptotic_of_prefix_isolated ha hC hb hQ hcard hc hH2

end Dubon2026
