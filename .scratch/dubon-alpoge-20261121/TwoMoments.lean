import Dubon2026.CuspSatoTateConcentration
import Dubon2026.PrimitiveNormalizedRecurrence

/-! # Modular concentration from the second and sixth prime-power averages -/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- This signed combination of just two characters is nonpositive outside the
source coefficient band, including outside the entire tempered interval. -/
private theorem two_character_band_bound (x : ℝ) :
    1 + 2 * (Chebyshev.S ℝ 2).eval x - (Chebyshev.S ℝ 6).eval x ≤
      if 1 ≤ |x| ∧ |x| ≤ 2 then 9 else 0 := by
  have hid : 1 + 2 * (Chebyshev.S ℝ 2).eval x - (Chebyshev.S ℝ 6).eval x =
      x^2 * ((x^2 - 1) * (4 - x^2)) := by
    have step (n : ℤ) : (Chebyshev.S ℝ (n+2)).eval x =
        x * (Chebyshev.S ℝ (n+1)).eval x - (Chebyshev.S ℝ n).eval x := by
      rw [Chebyshev.S_add_two, eval_sub, eval_mul, eval_X]
    have e3 := step 1
    have e4 := step 2
    have e5 := step 3
    have e6 := step 4
    norm_num [Chebyshev.S_two, Chebyshev.S_one] at e3 e4 e5 e6 ⊢
    rw [e6, e5, e4, e3]
    ring
  rw [hid, ← sq_abs x]
  split_ifs with h
  · have ht : |x| ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 - |x|), mul_self_le_mul_self (abs_nonneg x) h.2]
    have hb : (|x| ^ 2 - 1) * (4 - |x| ^ 2) ≤ 9 / 4 := by nlinarith [sq_nonneg (|x| ^ 2 - 5 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg |x|)]
  · push Not at h
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    by_cases hl : 1 ≤ |x|
    · have ht := h hl
      have ht' := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2) ht.le
      apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith
    · have hx := abs_nonneg x
      have ht := mul_self_le_mul_self hx (le_of_not_ge hl)
      apply mul_nonpos_of_nonpos_of_nonneg <;> nlinarith

/-- A prime-count normalized mean transfers to the open/closed dyadic interval. -/
private theorem dyadic_prime_sum_of_mean {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto (fun N => (∑ p ∈ Nat.primesLE N, u p) / Nat.primeCounting N)
      atTop (𝓝 c)) :
    Tendsto (fun N => (∑ p ∈ dyadicPrimes N, u p) / ((N : ℝ) / Real.log N))
      atTop (𝓝 (c / 2)) := by
  have hf : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 1) := by
    simpa only [one_mul, Nat.floor_natCast] using tendsto_primeCounting_scaled (c := 1) (by norm_num)
  have hh : Tendsto (fun N : ℕ => (Nat.primeCounting (N / 2) : ℝ) /
      ((N : ℝ) / Real.log N)) atTop (𝓝 (1 / 2)) := by
    have he (N : ℕ) : (1 / 2 : ℝ) * N = (N : ℝ) / (2 : ℕ) := by push_cast; ring
    simpa only [he, Nat.floor_div_eq_div] using tendsto_primeCounting_scaled (c := 1/2) (by norm_num)
  have h := (hu.mul hf).sub ((hu.comp tendsto_nat_half_atTop).mul hh)
  rw [show c * 1 - c * (1 / 2) = c / 2 by ring] at h
  apply h.congr'
  filter_upwards [Nat.tendsto_primeCounting.eventually_ge_atTop 1,
    (Nat.tendsto_primeCounting.comp tendsto_nat_half_atTop).eventually_ge_atTop 1] with N hN hM
  change 1 ≤ Nat.primeCounting (N / 2) at hM
  have hsub : Nat.primesLE (N / 2) ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.div_le_self N 2),
      (Nat.mem_primesLE.mp hp).2⟩
  have he := Finset.sum_sdiff hsub (f := u)
  rw [dyadicPrimes_eq_sdiff, ← he, add_div]
  have hp : (Nat.primeCounting N : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting N ≠ 0 by omega)
  have hq : (Nat.primeCounting (N / 2) : ℝ) ≠ 0 := by exact_mod_cast (show Nat.primeCounting (N / 2) ≠ 0 by omega)
  simp only [Function.comp_apply]
  field_simp
  ring

/-- Averages over all primes suffice. Eventually each prime in the dyadic window is
above the level, so both character identities apply to the original form. -/
theorem primitive_band_count_of_two_prime_means {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hmean : ∀ r ∈ ({2, 6} : Finset ℕ), Tendsto (fun N =>
      (∑ p ∈ Nat.primesLE N, (normalizedCuspCoefficients f.toCuspForm (p^r)).re) /
        Nat.primeCounting N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) / Real.log N) / 36 ≤
      ((selectedDyadicPrimes (cuspPrimeSelection f.toCuspForm) N).card : ℝ) := by
  classical
  let a := normalizedCuspCoefficients f.toCuspForm
  let w := fun p => 1 + 2 * (a (p^2)).re - (a (p^6)).re
  have h2 := dyadic_prime_sum_of_mean (hmean 2 (by simp))
  have h6 := dyadic_prime_sum_of_mean (hmean 6 (by simp))
  have hw : Tendsto (fun N => (∑ p ∈ dyadicPrimes N, w p) / ((N : ℝ) / Real.log N))
      atTop (𝓝 (1/2)) := by
    have h := (tendsto_card_dyadicPrimes_ratio.add (h2.const_mul 2)).sub h6
    norm_num at h
    apply h.congr
    intro N
    simp only [w, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum, sub_div, add_div, mul_div_assoc, a]
  filter_upwards [hw.eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ) < 1/2)),
    eventually_ge_atTop (2 * Q + 2)] with N hwN hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log N := div_pos (by linarith) (Real.log_pos hNr)
  have hsum : (∑ p ∈ dyadicPrimes N, w p) ≤
      9 * ((selectedDyadicPrimes (cuspPrimeSelection f.toCuspForm) N).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ dyadicPrimes N, (if cuspPrimeSelection f.toCuspForm p then (9 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hprime, _, _⟩ := mem_dyadicPrimes.mp hp
        have hinterval := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        have hgood : ¬p ∣ Q := fun hd => by
          have := Nat.le_of_dvd (Nat.pos_of_neZero Q) hd
          omega
        have hreal := primitiveCuspForm_normalizedCoefficient_im f p (hprime.coprime_iff_not_dvd.mpr hgood)
        simpa only [w, a, cuspPrimeSelection, hgood, not_false_eq_true, true_and,
          primitiveCuspForm_normalized_primePower_re f hprime hgood,
          norm_eq_abs_re_of_im_zero hreal, Nat.cast_ofNat] using
          two_character_band_bound ((a p).re)
      _ = _ := by rw [← Finset.sum_filter]; simp [selectedDyadicPrimes, mul_comm]
  have hlarge := (lt_div_iff₀ hscale).mp hwN
  linarith

private theorem growth_of_band_count {S : ℕ → Prop}
    (hl : ∀ᶠ N : ℕ in atTop, ((N : ℝ) / Real.log N) / 36 ≤
      ((selectedDyadicPrimes S N).card : ℝ)) :
    Tendsto (fun N => (selectedDyadicPrimes S N).card) atTop atTop ∧
    Tendsto (fun N => Real.log (selectedDyadicPrimes S N).card / Real.log N) atTop (𝓝 1) := by
  classical
  have hg := tendsto_nat_div_log_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 36)
  have hcard := tendsto_atTop_mono' atTop hl hg
  refine ⟨tendsto_natCast_atTop_iff.mp hcard, ?_⟩
  have hlogN := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlow := tendsto_log_nat_div_log_ratio.sub (hlogN.const_div_atTop (Real.log 36))
  rw [sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_log_card_dyadicPrimes_ratio
  · filter_upwards [hl, eventually_ge_atTop 2] with N hb hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hs : 0 < (N : ℝ) / Real.log N := div_pos (by linarith) (Real.log_pos hNr)
    have hlog := Real.log_le_log (div_pos hs (by norm_num : (0 : ℝ) < 36)) hb
    rw [Real.log_div hs.ne' (by norm_num)] at hlog
    simpa only [sub_div] using div_le_div_of_nonneg_right hlog (Real.log_pos hNr).le
  · filter_upwards [hcard.eventually_ge_atTop 1, eventually_ge_atTop 2] with N hc hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hsub : selectedDyadicPrimes S N ⊆ dyadicPrimes N := Finset.filter_subset _ _
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith)
      (Nat.cast_le.mpr (Finset.card_le_card hsub))) (Real.log_pos hNr).le

/-- Two explicit prime-power means give the normalized and classical concentration
laws and the actual fixed-length height limit for the original Fourier coefficients. -/
theorem primitive_concentration_of_two_prime_means {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k)
    (hmean : ∀ r ∈ ({2, 6} : Finset ℕ), Tendsto (fun N =>
      (∑ p ∈ Nat.primesLE N, (normalizedCuspCoefficients f.toCuspForm (p^r)).re) /
        Nat.primeCounting N) atTop (𝓝 0)) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f.toCuspForm))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f.toCuspForm f.normalized)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f.toCuspForm))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f.toCuspForm) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f.toCuspForm) N)) *
        ((verticalZeroCount (cuspCoefficients f.toCuspForm) N hN (f.normalized.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized N : Measure ℝ) (Ioo l u)).toReal))) := by
  let B := selectedDyadicPrimes (cuspPrimeSelection f.toCuspForm)
  have hQ := isolatedPrimeBlocks_selectedDyadicPrimes (cuspPrimeSelection f.toCuspForm)
  obtain ⟨hcard, hlog⟩ := growth_of_band_count (primitive_band_count_of_two_prime_means f hmean)
  have hb : ∀ᶠ N in atTop, ∀ p ∈ B N,
      1 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖ ∧ ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 :=
    Eventually.of_forall fun _ _ hp => (mem_selectedDyadicPrimes.mp hp).2.2
  have hc := primeCoefficientComparability_of_selected_bounds hQ hb (1 / 2)
  have hH2 := (tendstoLocallyUniformly_selected_energy hQ hb hcard hlog).tendstoLocallyUniformlyOn
    (s := Iio (1/2))
  have ha := normalizedCuspCoefficients_one f.toCuspForm f.normalized
  have hH1 := globalEnergyAsymptotic_of_mean_isolated ha (tendsto_cusp_square_mean f.toCuspForm hk)
    hQ hcard hc hH2
  obtain ⟨hp, _, _, hw, he⟩ := abstract_actual_zero_concentration ha hQ hcard hc hH1 hH2
  have hne : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 < lastIndex (normalizedCuspCoefficients f.toCuspForm) N := by
    filter_upwards [he] with N hN
    obtain ⟨hn, hm, _⟩ := hN
    exact ⟨hn, hm⟩
  have hcp := shifted_normalizedJessen_limit hp (((k : ℝ) - 1) / 2)
  have hcw := shifted_jessen_probability_limit ha hne hw (((k : ℝ) - 1) / 2)
  rw [← cuspCoefficients_eq_shifted_normalized f.toCuspForm, classical_cusp_concentration_line] at hcp
  rw [← jessenProbability_congr (cuspCoefficients_eq_shifted_normalized f.toCuspForm) f.normalized _,
    classical_cusp_concentration_line] at hcw
  refine ⟨hp, hw, hcp, hcw, ?_⟩
  filter_upwards [hne] with N hn
  have hm : 1 < lastIndex (cuspCoefficients f.toCuspForm) N := by
    simpa only [normalizedCuspCoefficients_lastIndex] using hn.2
  exact ⟨hn.1, hm, tendsto_normalized_verticalZeroCount hn.1 f.normalized hm⟩

end
end Dubon2026
