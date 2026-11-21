import Dubon2026.TwoPrimeMeanConcentration
import Dubon2026.RankinBoundaryNonvanishing

/-! # Modular concentration from the good-prime bound alone

The second symmetric Euler function already has its required continuation.
Its prime mean controls a wider coefficient band, sufficient for the original
abstract concentration theorem. This route also applies to CM forms.
-/

namespace Dubon2026

open Filter Set MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- The existing symmetric-square continuation gives its prime mean under the
good-prime bound, independently of any higher symmetric-power continuation. -/
theorem primitive_second_prime_mean_of_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) :
    Tendsto (fun N => (∑ p ∈ Nat.primesLE N, primitivePrimeCharacter f 2 p) /
      Nat.primeCounting N) atTop (𝓝 0) := by
  obtain ⟨F, hF, hne, hmatch⟩ := primitive_second_symmetric_nonvanishing_continuation f hk
  let tail := primeSpectralTail (primitiveSymmetricSpectralRoots f 2)
  apply prime_average_zero_of_boundary_continuation (C := (2 : ℝ) + 1) (by norm_num)
    (fun p hp => abs_primitivePrimeCharacter_le f hb 2 hp) (fun s => -logDeriv F s - tail s)
  · exact ((hF.deriv.continuousOn.div hF.continuousOn hne).neg).sub
      ((primitiveSymmetricSpectralTail_analyticOnNhd f hb 2).continuousOn.mono
        (fun s hs => by dsimp at hs ⊢; linarith))
  · intro s hs
    have he : F =ᶠ[𝓝 s] primitiveSymmetricLFunction f 2 :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
        (fun t ht => hmatch ht)
    have hlog : -logDeriv F s = primitiveSymmetricLogSeries f 2 s := by
      rw [logDeriv_apply, he.deriv_eq, hmatch hs]
      exact primitiveSymmetricLFunction_logDeriv f hb 2 hs
    dsimp only [tail]
    rw [hlog, primitiveSymmetricLogSeries_eq f hb 2 hs, add_sub_cancel_right]

/-- The mean square at primes tends to one. With the pointwise upper bound,
every sufficiently large dyadic interval contains enough coefficients of norm
at least one half. All primes dividing the level have already left the interval. -/
theorem primitive_wide_band_count_of_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) :
    let S := fun p => ¬p ∣ Q ∧ 1/2 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) / Real.log N) / 36 ≤ ((selectedDyadicPrimes S N).card : ℝ) := by
  classical
  let a := normalizedCuspCoefficients f.toCuspForm
  let S := fun p => ¬p ∣ Q ∧ 1/2 ≤ ‖a p‖
  let u := primitivePrimeCharacter f 2
  have hav := dyadic_prime_sum_of_mean (primitive_second_prime_mean_of_bound f hk hb)
  have hw : Tendsto (fun N => (∑ p ∈ dyadicPrimes N, (3/4 + u p)) / ((N : ℝ) / Real.log N))
      atTop (𝓝 (3/8)) := by
    have h := (tendsto_card_dyadicPrimes_ratio.const_mul (3/4)).add hav
    norm_num at h
    apply h.congr
    intro N
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, add_div, u]
    ring
  filter_upwards [hw.eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ) < 3/8)),
    eventually_ge_atTop (2 * Q + 2)] with N hwN hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs : 0 < (N : ℝ) / Real.log N := div_pos (by linarith) (Real.log_pos hNr)
  have hsum : (∑ p ∈ dyadicPrimes N, (3/4 + u p)) ≤ 4 * ((selectedDyadicPrimes S N).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ dyadicPrimes N, (if S p then (4 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro p hp
        have hprime := (mem_dyadicPrimes.mp hp).1
        have hinterval := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        have hgood : ¬p ∣ Q := fun hd => by
          have := Nat.le_of_dvd (Nat.pos_of_neZero Q) hd
          omega
        have he : u p = ‖a p‖^2 - 1 := by
          rw [norm_eq_abs_re_of_im_zero (primitiveCuspForm_normalizedCoefficient_im f p
            (hprime.coprime_iff_not_dvd.mpr hgood)), sq_abs]
          simp [u, primitivePrimeCharacter, hgood, primitiveCuspForm_normalized_primePower_re f hprime hgood,
            Chebyshev.S_two]
        rw [he]
        by_cases ht : S p
        · rw [if_pos ht]
          nlinarith [mul_self_le_mul_self (norm_nonneg (a p)) (hb p hprime hgood)]
        · rw [if_neg ht]
          have hsmall : ‖a p‖ ≤ 1/2 := le_of_lt (lt_of_not_ge (fun hz => ht ⟨hgood, hz⟩))
          nlinarith [mul_self_le_mul_self (norm_nonneg (a p)) hsmall]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [selectedDyadicPrimes, mul_comm]
        apply congrArg Finset.card
        ext p
        simp only [Finset.mem_filter]
  have hlarge := (lt_div_iff₀ hs).mp hwN
  change _ ≤ ((selectedDyadicPrimes S N).card : ℝ)
  linarith

/-- Uniform two-sided amplitude bounds transfer the unit-coefficient dyadic
energy and comparability estimates to the wider block. -/
private theorem wide_band_H2 {a : ℕ → ℂ} {B : ℕ → Finset ℕ}
    (hB : IsolatedPrimeBlocks B) (hcard : Tendsto (fun N => (B N).card) atTop atTop)
    (hlog : Tendsto (fun N => Real.log (B N).card / Real.log N) atTop (𝓝 1))
    (ha : ∀ N, ∀ p ∈ B N, 1/2 ≤ ‖a p‖ ∧ ‖a p‖ ≤ 2) :
    PrimeCoefficientComparability a B (1/2) ∧ IsolatedEnergyAsymptotic a B (1/2) := by
  let b := fun _ : ℕ => (1 : ℂ)
  have hb : ∀ᶠ N in atTop, ∀ p ∈ B N, 1 ≤ ‖b p‖ ∧ ‖b p‖ ≤ 2 := by
    exact Eventually.of_forall fun _ _ _ => by norm_num [b]
  have hc := primeCoefficientComparability_of_selected_bounds hB hb (1/2)
  constructor
  · intro l u hlu hu
    obtain ⟨K, hK, hcomp⟩ := hc l u hlu hu
    refine ⟨4*K, by linarith, ?_⟩
    filter_upwards [hcomp] with N hN
    intro σ hσ p hp q hq
    have hratio := hN σ hσ p hp q hq
    simp only [b, norm_one, one_mul] at hratio
    obtain ⟨hp1, hp2⟩ := ha N p hp
    obtain ⟨hq1, hq2⟩ := ha N q hq
    have hpos : 0 < ‖a q‖ := by linarith
    have hl : (1/4 : ℝ) ≤ ‖a p‖ / ‖a q‖ := (le_div_iff₀ hpos).mpr (by linarith)
    have hh : ‖a p‖ / ‖a q‖ ≤ 4 := (div_le_iff₀ hpos).mpr (by linarith)
    rw [mul_div_mul_comm]
    refine ⟨?_, mul_le_mul hh hratio.2 (by positivity) (by norm_num)⟩
    simpa only [mul_inv_rev, one_div, mul_comm] using
      mul_le_mul hl hratio.1 (inv_nonneg.mpr (by linarith)) (div_nonneg (norm_nonneg _) hpos.le)
  · have hu := tendstoLocallyUniformly_selected_energy hB hb hcard hlog
    have hpos := eventually_isolatedPrimeEnergy_pos hB hcard hc
    have hden : Tendsto (fun N : ℕ => Real.log 4 / (2 * Real.log N)) atTop (𝓝 0) :=
      ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)).const_div_atTop _
    apply TendstoLocallyUniformly.tendstoLocallyUniformlyOn
    rw [Metric.tendstoLocallyUniformly_iff] at hu ⊢
    intro ε hε x
    obtain ⟨U, hU, hctrl⟩ := hu (ε/2) (half_pos hε) x
    refine ⟨U, hU, ?_⟩
    filter_upwards [hctrl, hpos, hden.eventually (gt_mem_nhds (half_pos hε)),
      eventually_ge_atTop (2 : ℕ)] with N hlocal hp hsmall hN
    intro σ hσ
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hbounds (p : ℕ) (h : p ∈ B N) :
        (1/4 : ℝ) * ((p : ℝ)^(-2*σ)) ≤ ‖a p‖^2 * (p : ℝ)^(-2*σ) ∧
        ‖a p‖^2 * (p : ℝ)^(-2*σ) ≤ 4 * (p : ℝ)^(-2*σ) := by
      obtain ⟨h1, h2⟩ := ha N p h
      constructor <;> apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      · nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1/2) h1]
      · nlinarith [mul_self_le_mul_self (norm_nonneg (a p)) h2]
    have hl := Finset.sum_le_sum (s := B N) fun p h => (hbounds p h).1
    have hh := Finset.sum_le_sum (s := B N) fun p h => (hbounds p h).2
    rw [← Finset.mul_sum] at hl hh
    have hd := (abs_log_sub_log_le_of_exp_bounds (D := Real.log 4) (Y := isolatedPrimeEnergy a B N σ)
      (hp σ) (by simpa [isolatedPrimeEnergy, b, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4), one_div] using hl)
      (by simpa [isolatedPrimeEnergy, b, Real.exp_log (by norm_num : (0:ℝ)<4)] using hh)).2
    have hd' := div_le_div_of_nonneg_right hd (by positivity : 0 ≤ 2 * Real.log (N : ℝ))
    rw [← abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.log_pos hNr)),
      ← abs_div, sub_div, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.log_pos hNr))] at hd'
    have he := hlocal σ hσ
    rw [Real.dist_eq] at he ⊢
    have htri := abs_sub_le (1/2-σ)
      (Real.log (isolatedPrimeEnergy b B N σ)/(2*Real.log N))
      (Real.log (isolatedPrimeEnergy a B N σ)/(2*Real.log N))
    linarith [abs_sub_comm (Real.log (isolatedPrimeEnergy a B N σ)/(2*Real.log N))
      (Real.log (isolatedPrimeEnergy b B N σ)/(2*Real.log N))]

/-- The fixed-band argument gives both concentration lines under the good-prime
coefficient bound. The proof uses a wider band than the separate
Sato–Tate acceptance test. The prime average is proved using the symmetric square. -/
theorem primitive_concentration_of_good_prime_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2) :
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
  let S := fun p => ¬p ∣ Q ∧ 1/2 ≤ ‖normalizedCuspCoefficients f.toCuspForm p‖
  have hQ := isolatedPrimeBlocks_selectedDyadicPrimes S
  obtain ⟨hc, hl⟩ := growth_of_band_count (primitive_wide_band_count_of_bound f hk hb)
  obtain ⟨hcomp, henergy⟩ := wide_band_H2 hQ hc hl (a := normalizedCuspCoefficients f.toCuspForm)
    (fun _ p h => ⟨(mem_selectedDyadicPrimes.mp h).2.2,
      hb p (mem_selectedDyadicPrimes.mp h).1.1 (mem_selectedDyadicPrimes.mp h).2.1⟩)
  exact primitive_concentration_of_isolated_block f (by omega) hQ hc hcomp henergy

end
end Dubon2026
