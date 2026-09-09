import Tao2026.FourierAssembly

/-!
# Uniform Fourier-approximation transfer for Theorem 2.5

This module proves the exact stability step that transfers a finite Fourier-polynomial
estimate to a uniformly approximated continuous periodic weight. The analytic construction
and decay estimate for the Fourier approximation remain separate obligations.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- A continuous weight produces an integrable logarithmically weighted
reciprocal-parameter integrand on Tao's source interval. -/
theorem integrableOn_primeEquidistributionIntegrand
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P))
    {W : ℝ × ℝ → ℂ} (hW : Continuous W)
    (N M : ℝ) (j : ℕ) :
    IntegrableOn (fun t => W (N / t, M / t ^ j) / Real.log t) I := by
  have hPpos : 0 < P := by linarith
  have hcontinuous : ContinuousOn
      (fun t => W (N / t, M / t ^ j) / Real.log t) (Set.Icc P (2 * P)) := by
    intro t ht
    have htpos : 0 < t := hPpos.trans_le ht.1
    have htone : 1 < t := lt_of_lt_of_le (by norm_num) (hP.trans ht.1)
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htone)
    have hpair : ContinuousAt (fun u : ℝ => (N / u, M / u ^ j)) t :=
      (continuousAt_const.div continuousAt_id htpos.ne').prodMk
        (continuousAt_const.div (continuousAt_id.pow j) (pow_ne_zero j htpos.ne'))
    have hnumerator : ContinuousAt (fun u : ℝ => W (N / u, M / u ^ j)) t :=
      hW.continuousAt.comp hpair
    have hdenominator : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htpos.ne')
    exact (hnumerator.div hdenominator (by exact_mod_cast hlog)).continuousWithinAt
  exact (hcontinuous.integrableOn_Icc).mono_set hI

/-- Uniform approximation costs at most the number of sampled primes times
the pointwise approximation error in the finite prime sum. -/
theorem norm_primeEquidistributionSum_sub_le_card_mul
    (P : ℝ) (I : Set ℝ) (W V : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ)
    {δ : ℝ} (happrox : ∀ x, ‖W x - V x‖ ≤ δ) :
    ‖primeEquidistributionSum P I W N M j -
        primeEquidistributionSum P I V N M j‖ ≤
      ((primesInScaleSet P I).card : ℝ) * δ := by
  unfold primeEquidistributionSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p ∈ primesInScaleSet P I,
        (W (N / (p : ℝ), M / (p : ℝ) ^ j) -
          V (N / (p : ℝ), M / (p : ℝ) ^ j))‖ ≤
        ∑ p ∈ primesInScaleSet P I,
          ‖W (N / (p : ℝ), M / (p : ℝ) ^ j) -
            V (N / (p : ℝ), M / (p : ℝ) ^ j)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ primesInScaleSet P I, δ := by
      apply Finset.sum_le_sum
      intro p _hp
      exact happrox _
    _ = ((primesInScaleSet P I).card : ℝ) * δ := by simp

/-- The ambient finite prime set contains at most `2P+1` elements. -/
theorem card_primesInScaleSet_le
    {P : ℝ} (hP : 0 ≤ P) (I : Set ℝ) :
    ((primesInScaleSet P I).card : ℝ) ≤ 2 * P + 1 := by
  classical
  have hcard : (primesInScaleSet P I).card ≤ ⌊2 * P⌋₊ + 1 := by
    unfold primesInScaleSet
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hfloor : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ 2 * P)
  calc
    ((primesInScaleSet P I).card : ℝ) ≤ ((⌊2 * P⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = (⌊2 * P⌋₊ : ℝ) + 1 := by push_cast; rfl
    _ ≤ 2 * P + 1 := by simpa [add_comm] using add_le_add_right hfloor 1

/-- Every measurable subset of `[P,2P]` has real volume at most `P`. -/
theorem volumeReal_le_scale
    {P : ℝ} (hP : 0 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P)) :
    volume.real I ≤ P := by
  have hIccFinite : volume (Set.Icc P (2 * P)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  calc
    volume.real I ≤ volume.real (Set.Icc P (2 * P)) :=
      measureReal_mono hI hIccFinite.ne
    _ = P := by
      change (volume (Set.Icc P (2 * P))).toReal = P
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring

/-- Uniform approximation by `δ` perturbs Tao's logarithmic integral by at
most `Pδ / log P`. -/
theorem norm_primeEquidistributionIntegral_sub_le
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W V : ℝ × ℝ → ℂ) (hW : Continuous W) (hV : Continuous V)
    (N M : ℝ) (j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ x, ‖W x - V x‖ ≤ δ) :
    ‖primeEquidistributionIntegral I W N M j -
        primeEquidistributionIntegral I V N M j‖ ≤
      (δ / Real.log P) * P := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hWint := integrableOn_primeEquidistributionIntegrand hP hI hW N M j
  have hVint := integrableOn_primeEquidistributionIntegrand hP hI hV N M j
  unfold primeEquidistributionIntegral
  rw [← MeasureTheory.integral_sub hWint hVint]
  have hpoint : ∀ᵐ t ∂volume.restrict I,
      ‖W (N / t, M / t ^ j) / Real.log t -
        V (N / t, M / t ^ j) / Real.log t‖ ≤ δ / Real.log P := by
    filter_upwards [ae_restrict_mem hImeas] with t ht
    have htI := hI ht
    have htpos : 0 < t := hPpos.trans_le htI.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [hP, htI.1])
    have hlogmono : Real.log P ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn hPpos htpos htI.1
    rw [← sub_div, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
    exact (div_le_div_of_nonneg_right (happrox _) hlogt.le).trans
      (div_le_div_of_nonneg_left hδ hlogP hlogmono)
  have hIccFinite : volume (Set.Icc P (2 * P)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIfinite : volume I < ⊤ :=
    lt_of_le_of_lt (measure_mono hI) hIccFinite
  letI : IsFiniteMeasure (volume.restrict I) :=
    ⟨by simpa [Measure.restrict_apply hImeas] using hIfinite⟩
  have hraw := MeasureTheory.norm_integral_le_of_norm_le_const hpoint
  have hvolume : volume.real I ≤ P := volumeReal_le_scale hPpos.le hI
  calc
    ‖∫ t in I,
        (W (N / t, M / t ^ j) / Real.log t -
          V (N / t, M / t ^ j) / Real.log t)‖ ≤
        (δ / Real.log P) * (volume.restrict I).real Set.univ := hraw
    _ = (δ / Real.log P) * volume.real I := by
      rw [measureReal_restrict_apply_univ]
    _ ≤ (δ / Real.log P) * P :=
      mul_le_mul_of_nonneg_left hvolume (div_nonneg hδ hlogP.le)

/-- Exact stability of the Theorem 2.5 discrepancy under uniform
approximation of a continuous weight. -/
theorem norm_primeEquidistributionDiscrepancy_le_of_approx
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W V : ℝ × ℝ → ℂ) (hW : Continuous W) (hV : Continuous V)
    (N M : ℝ) (j : ℕ) {δ E : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ x, ‖W x - V x‖ ≤ δ)
    (hVerror : ‖primeEquidistributionSum P I V N M j -
        primeEquidistributionIntegral I V N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I W N M j -
        primeEquidistributionIntegral I W N M j‖ ≤
      (2 * P + 1) * δ + E + (δ / Real.log P) * P := by
  have hsumRaw := norm_primeEquidistributionSum_sub_le_card_mul
    P I W V N M j happrox
  have hsum : ‖primeEquidistributionSum P I W N M j -
      primeEquidistributionSum P I V N M j‖ ≤ (2 * P + 1) * δ :=
    hsumRaw.trans (mul_le_mul_of_nonneg_right
      (card_primesInScaleSet_le (by linarith) I) hδ)
  have hint := norm_primeEquidistributionIntegral_sub_le
    hP hImeas hI W V hW hV N M j hδ happrox
  have hdecomp :
      primeEquidistributionSum P I W N M j -
          primeEquidistributionIntegral I W N M j =
        (primeEquidistributionSum P I W N M j -
          primeEquidistributionSum P I V N M j) +
        (primeEquidistributionSum P I V N M j -
          primeEquidistributionIntegral I V N M j) +
        (primeEquidistributionIntegral I V N M j -
          primeEquidistributionIntegral I W N M j) := by ring
  rw [hdecomp]
  calc
    ‖(primeEquidistributionSum P I W N M j -
          primeEquidistributionSum P I V N M j) +
        (primeEquidistributionSum P I V N M j -
          primeEquidistributionIntegral I V N M j) +
        (primeEquidistributionIntegral I V N M j -
          primeEquidistributionIntegral I W N M j)‖ ≤
        (‖primeEquidistributionSum P I W N M j -
            primeEquidistributionSum P I V N M j‖ +
          ‖primeEquidistributionSum P I V N M j -
            primeEquidistributionIntegral I V N M j‖) +
          ‖primeEquidistributionIntegral I V N M j -
            primeEquidistributionIntegral I W N M j‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 * P + 1) * δ + E + (δ / Real.log P) * P := by
      apply add_le_add (add_le_add hsum hVerror)
      simpa [norm_sub_rev] using hint

/-- Source-facing specialization of approximation stability to a finite
Fourier polynomial; its continuity is discharged internally. -/
theorem norm_primeEquidistributionDiscrepancy_le_of_finiteFourierApprox
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    (W : ℝ × ℝ → ℂ) (hW : Continuous W)
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) {δ E : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ x, ‖W x - finiteFourierPolynomial s c x‖ ≤ δ)
    (hPolynomialError :
      ‖primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial s c) N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I W N M j -
        primeEquidistributionIntegral I W N M j‖ ≤
      (2 * P + 1) * δ + E + (δ / Real.log P) * P := by
  exact norm_primeEquidistributionDiscrepancy_le_of_approx
    hP hImeas hI W (finiteFourierPolynomial s c) hW
      (continuous_finiteFourierPolynomial s c) N M j hδ happrox hPolynomialError

/-- Exact finite truncation transfer: an estimate for the retained modes
extends to a larger finite polynomial at the explicit `ℓ¹` cost of its
discarded coefficients. -/
theorem norm_primeEquidistributionDiscrepancy_le_of_finiteFourierTruncation
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc P (2 * P))
    {s t : Finset (ℤ × ℤ)} (hst : s ⊆ t) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) {E : ℝ}
    (hRetainedError :
      ‖primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial s c) N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I (finiteFourierPolynomial t c) N M j -
        primeEquidistributionIntegral I
          (finiteFourierPolynomial t c) N M j‖ ≤
      (2 * P + 1) * (∑ q ∈ t \ s, ‖c q‖) + E +
        ((∑ q ∈ t \ s, ‖c q‖) / Real.log P) * P := by
  apply norm_primeEquidistributionDiscrepancy_le_of_finiteFourierApprox
    hP hImeas hI (finiteFourierPolynomial t c)
      (continuous_finiteFourierPolynomial t c) s c N M j
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) _ hRetainedError
  intro x
  exact norm_finiteFourierPolynomial_sub_le_tail hst c x

end

end Tao2026
