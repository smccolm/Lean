import Dubon2026.SecondSpectralTail
import Dubon2026.SecondPrimeSeries
import Dubon2026.PositiveWiener

namespace Dubon2026
open Filter Set ArithmeticFunction
open scoped Topology
noncomputable section

/-- The actual prime character has an unconditional continuous boundary value.
Analytic uniqueness transports the shifted Euler computation from its far half-plane. -/
theorem primitive_second_prime_boundary {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
      (LSeries (fun n => (primeLogCoefficients (primitivePrimeCharacter f 2) n : ℂ))) {s | 1 < s.re} := by
  let coeff := fun n => (primeLogCoefficients (primitivePrimeCharacter f 2) n : ℂ)
  let tail := primeSpectralTail (primitiveSymmetricSpectralRoots f 2)
  obtain ⟨F,hF,hne,hmatch⟩ := primitive_second_symmetric_nonvanishing_continuation f hk
  let G := fun s => -logDeriv F s - tail s
  have hG : AnalyticOnNhd ℂ G {s | 1 ≤ s.re} := by
    intro s hs
    exact (((hF.deriv s hs).div (hF s hs) (hne s hs)).neg).sub
      (primitive_second_tail_analytic f hk s (show 9/10 < s.re by change 1 ≤ s.re at hs; linarith))
  refine ⟨G, hG.continuousOn, ?_⟩
  have hL : AnalyticOnNhd ℂ (LSeries coeff) {s | 1 < s.re} := by
    intro s hs
    let t : ℝ := (1 + s.re)/2
    have h1 : 1 < t := by change 1 < s.re at hs; dsimp [t]; linarith
    have h2 : t < s.re := by change 1 < s.re at hs; dsimp [t]; linarith
    exact LSeries_analyticOnNhd coeff s
      ((primitive_second_prime_series_summable f hk (s := (t : ℂ)) (by simpa using h1)).abscissaOfAbsConv_le.trans_lt
        (by exact_mod_cast h2))
  have hfar (s : ℂ) (hs : 2 < s.re) : G s = LSeries coeff s := by
    have he : F =ᶠ[𝓝 s] primitiveSymmetricLFunction f 2 :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by linarith : 1 < s.re))
        (fun z hz => hmatch hz)
    change -logDeriv F s - tail s = _
    have hlog : logDeriv F s = logDeriv (primitiveSymmetricLFunction f 2) s := by
      simp only [logDeriv_apply, he.deriv_eq, he.self_of_nhds]
    rw [hlog, primitive_second_logDeriv_far f hk (primitive_second_spectral_growth f hk) hs]
    exact add_sub_cancel_right _ _
  have h3 : (3 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hG' : AnalyticOnNhd ℂ G {s | 1 < s.re} := hG.mono fun s hs => (show 1 < s.re from hs).le
  apply hG'.eqOn_of_preconnected_of_frequently_eq hL
    (convex_halfSpace_re_gt 1).isPreconnected h3
  apply Filter.Eventually.frequently
  have hh : ∀ᶠ s : ℂ in 𝓝 (3 : ℂ), 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact (hh.filter_mono nhdsWithin_le_nhds).mono hfar

/-- Adding the ordinary von Mangoldt coefficients gives a nonnegative sequence.
The positive Wiener–Ikehara theorem obtains the required Chebyshev bound internally. -/
theorem primitive_second_prime_log_mean {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, primitivePrimeCharacter f 2 p * Real.log p) /
      (N : ℝ)) atTop (𝓝 0) := by
  let u := primitivePrimeCharacter f 2
  let b := fun n => primeLogCoefficients u n + vonMangoldt n
  have hpos : 0 ≤ b := by
    intro n
    change 0 ≤ primeLogCoefficients u n + vonMangoldt n
    by_cases hp : n.Prime
    · simp only [primeLogCoefficients, if_pos hp, vonMangoldt_apply_prime hp]
      by_cases hq : n ∣ Q
      · simp only [u, primitivePrimeCharacter, if_pos hq, zero_mul, zero_add]
        exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      · rw [show u n = _ from primitive_second_character_at_good f hp hq]
        nlinarith [mul_nonneg (sq_nonneg ‖normalizedCuspCoefficients f.toCuspForm n‖)
          (Real.log_nonneg (by exact_mod_cast hp.one_le) : 0 ≤ Real.log (n : ℝ))]
    · simp [primeLogCoefficients, hp, vonMangoldt_nonneg]
  have hfun : (fun n => (b n : ℂ)) = (fun n => (primeLogCoefficients u n : ℂ)) +
      (fun n => (vonMangoldt n : ℂ)) := by funext n; simp [b]
  obtain ⟨G,hG,hseries⟩ := primitive_second_prime_boundary f hk
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hF : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have hw : Tendsto (fun N : ℕ => cumsum b N / N) atTop (𝓝 1) := by
    apply Tauberian.WienerIkeharaTheorem'' hpos (G := fun s => G s + F s)
    · intro σ hσ
      have he := (primitive_second_prime_series_summable f hk (s := (σ : ℂ)) (by simpa using hσ)).add
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ))
      rw [← hfun] at he
      simpa only [← nterm_eq_norm_term] using he.norm
    · exact hG.add hF
    · intro s hs
      rw [show (fun s => G s + F s) s = G s + F s from rfl]
      change G s + F s = LSeries (fun n => (b n : ℂ)) s - ((1:ℝ):ℂ) / (s-1)
      rw [hfun]
      dsimp only [u]
      rw [LSeries_add (primitive_second_prime_series_summable f hk hs)
          (ArithmeticFunction.LSeriesSummable_vonMangoldt hs), hseries hs,
        show F s = LSeries (fun n => (vonMangoldt n : ℂ)) s - 1 / (s-1) from vonMangoldt_regularPart_eq hs]
      push_cast
      ring
  have he : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, primeLogCoefficients u n) / (N:ℝ)) atTop (𝓝 0) := by
    have h := hw.sub WeakPNT
    simp only [sub_self] at h
    apply h.congr
    intro N
    simp only [cumsum, b, Finset.sum_add_distrib, add_div, add_sub_cancel_right]
  have hnext := he.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N+1), primeLogCoefficients u n) /
    ((N+1 : ℕ) : ℝ)) atTop (𝓝 0) at hnext
  simp only [sum_primeLogCoefficients] at hnext
  have hratio : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ) / (N:ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun N : ℕ => 1 + 1 / (N:ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).const_add 1
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    push_cast
    rw [add_div, div_self (by exact_mod_cast (show N ≠ 0 by omega))]
  have h := hnext.mul hratio
  simp only [zero_mul] at h
  apply h.congr
  intro N
  have hn : ((N+1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp only [u,Function.comp_apply]
  field_simp [hn]

end
end Dubon2026
