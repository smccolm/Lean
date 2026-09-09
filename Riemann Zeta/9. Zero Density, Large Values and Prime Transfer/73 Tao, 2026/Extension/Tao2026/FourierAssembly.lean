import Tao2026.LowFrequency
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite Fourier assembly for Theorem 2.5

The pinned proof reduces the smooth two-dimensional periodic weight to
characters `e(n x + m y)`.  This module records the exact finite algebra of
that reduction.  Approximation by a finite Fourier polynomial and decay of
the discarded coefficients remain separate analytic obligations.
-/

open Complex Finset MeasureTheory Set
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The two-dimensional Fourier character with integer frequency `q`. -/
def fourierMode2D (q : ℤ × ℤ) (x : ℝ × ℝ) : ℂ :=
  standardAdditiveCharacter ((q.1 : ℝ) * x.1 + (q.2 : ℝ) * x.2)

/-- A finite two-dimensional Fourier polynomial. -/
def finiteFourierPolynomial
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∑ q ∈ s, c q * fourierMode2D q x

/-- The square box of retained integer frequencies `|n|,|m| ≤ R`. -/
def fourierFrequencyBox (R : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(R : ℤ)) (R : ℤ) ×ˢ
    Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- Every two-dimensional Fourier character is continuous. -/
theorem continuous_fourierMode2D (q : ℤ × ℤ) :
    Continuous (fourierMode2D q) := by
  unfold fourierMode2D
  exact continuous_standardAdditiveCharacter.comp
    ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd))

/-- Every Fourier character has unit norm. -/
@[simp]
theorem norm_fourierMode2D (q : ℤ × ℤ) (x : ℝ × ℝ) :
    ‖fourierMode2D q x‖ = 1 := by
  exact norm_standardAdditiveCharacter _

/-- Pointwise `ℓ¹` bound for a finite Fourier polynomial. -/
theorem norm_finiteFourierPolynomial_le_sum_norm
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (x : ℝ × ℝ) :
    ‖finiteFourierPolynomial s c x‖ ≤ ∑ q ∈ s, ‖c q‖ := by
  unfold finiteFourierPolynomial
  calc
    ‖∑ q ∈ s, c q * fourierMode2D q x‖ ≤
        ∑ q ∈ s, ‖c q * fourierMode2D q x‖ := norm_sum_le _ _
    _ = ∑ q ∈ s, ‖c q‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [norm_mul, norm_fourierMode2D, mul_one]

/-- Enlarging the retained set splits a finite Fourier polynomial exactly
into the old polynomial and its discarded-mode tail. -/
theorem finiteFourierPolynomial_eq_sdiff_add
    {s t : Finset (ℤ × ℤ)} (hst : s ⊆ t) (c : ℤ × ℤ → ℂ) (x : ℝ × ℝ) :
    finiteFourierPolynomial t c x =
      finiteFourierPolynomial (t \ s) c x + finiteFourierPolynomial s c x := by
  unfold finiteFourierPolynomial
  exact (Finset.sum_sdiff hst).symm

/-- Deleting finitely many modes changes the polynomial uniformly by at most
the `ℓ¹` norm of the discarded coefficients. -/
theorem norm_finiteFourierPolynomial_sub_le_tail
    {s t : Finset (ℤ × ℤ)} (hst : s ⊆ t) (c : ℤ × ℤ → ℂ) (x : ℝ × ℝ) :
    ‖finiteFourierPolynomial t c x - finiteFourierPolynomial s c x‖ ≤
      ∑ q ∈ t \ s, ‖c q‖ := by
  rw [finiteFourierPolynomial_eq_sdiff_add hst]
  simp only [add_sub_cancel_right]
  exact norm_finiteFourierPolynomial_le_sum_norm (t \ s) c x

theorem mem_fourierFrequencyBox {R : ℕ} {q : ℤ × ℤ} :
    q ∈ fourierFrequencyBox R ↔
      |q.1| ≤ (R : ℤ) ∧ |q.2| ≤ (R : ℤ) := by
  simp [fourierFrequencyBox, abs_le]

/-- Exact number of modes in the retained square frequency box. -/
theorem card_fourierFrequencyBox (R : ℕ) :
    (fourierFrequencyBox R).card = (2 * R + 1) ^ 2 := by
  simp only [fourierFrequencyBox, Finset.card_product, Int.card_Icc]
  have hnormalize : (R : ℤ) + 1 - -(R : ℤ) = 1 + (R : ℤ) * 2 := by ring
  rw [hnormalize]
  have htoNat : (1 + (R : ℤ) * 2).toNat = 2 * R + 1 := by
    have heq : 1 + (R : ℤ) * 2 = ((2 * R + 1 : ℕ) : ℤ) := by
      push_cast
      ring_nf
    rw [heq]
    rfl
  rw [htoNat]
  simp [pow_two]

/-- A uniform coefficient envelope on the retained box bounds its `ℓ¹`
coefficient norm by the exact number of modes. -/
theorem sum_norm_fourierFrequencyBox_le
    (R : ℕ) (c : ℤ × ℤ → ℂ) {C : ℝ}
    (hcoeff : ∀ q ∈ fourierFrequencyBox R, ‖c q‖ ≤ C) :
    ∑ q ∈ fourierFrequencyBox R, ‖c q‖ ≤ ((2 * R + 1) ^ 2 : ℕ) * C := by
  calc
    ∑ q ∈ fourierFrequencyBox R, ‖c q‖ ≤
        ∑ _q ∈ fourierFrequencyBox R, C := by
      apply Finset.sum_le_sum
      intro q hq
      exact hcoeff q hq
    _ = ((fourierFrequencyBox R).card : ℝ) * C := by simp
    _ = ((2 * R + 1) ^ 2 : ℕ) * C := by
      rw [card_fourierFrequencyBox]

/-- Every integer Fourier mode is `ℤ²`-periodic. -/
theorem isZ2Periodic_fourierMode2D (q : ℤ × ℤ) :
    IsZ2Periodic (fourierMode2D q) := by
  intro x y m n
  unfold fourierMode2D
  have hargument :
      (q.1 : ℝ) * (x + m) + (q.2 : ℝ) * (y + n) =
        ((q.1 : ℝ) * x + (q.2 : ℝ) * y) +
          ((q.1 * m + q.2 * n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hargument, standardAdditiveCharacter_add_int]

/-- Every finite Fourier polynomial has the periodicity required in Tao's
smooth-weight statement. -/
theorem isZ2Periodic_finiteFourierPolynomial
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    IsZ2Periodic (finiteFourierPolynomial s c) := by
  intro x y m n
  unfold finiteFourierPolynomial
  apply Finset.sum_congr rfl
  intro q _hq
  rw [isZ2Periodic_fourierMode2D q x y m n]

/-- Every finite Fourier polynomial is continuous. -/
theorem continuous_finiteFourierPolynomial
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    Continuous (finiteFourierPolynomial s c) := by
  unfold finiteFourierPolynomial
  apply continuous_finsetSum s
  intro q _hq
  exact continuous_const.mul (continuous_fourierMode2D q)

/-- Evaluation of a Fourier mode on Tao's reciprocal pair is exactly one
reciprocal phase with the two parameters rescaled by the integer frequency. -/
theorem fourierMode2D_reciprocalPair
    (q : ℤ × ℤ) (N M t : ℝ) (j : ℕ) :
    fourierMode2D q (N / t, M / t ^ j) =
      standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) := by
  unfold fourierMode2D
  rw [reciprocalPhase_eq_div]
  congr 1
  ring

/-- The prime sum associated to a single Fourier mode. -/
def primeFourierModeSum
    (P : ℝ) (I : Set ℝ) (q : ℤ × ℤ)
    (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ p ∈ primesInScaleSet P I,
    standardAdditiveCharacter
      (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j p)

/-- The logarithmically weighted integral associated to a single Fourier
mode. -/
def fourierModeIntegral
    (I : Set ℝ) (q : ℤ × ℤ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∫ t in I,
    standardAdditiveCharacter
      (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
        Real.log t

/-- Under Tao's scale hypothesis, every Fourier-mode logarithmic integrand
is integrable on the source interval. -/
theorem integrableOn_fourierModeIntegrand
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P))
    (q : ℤ × ℤ) (N M : ℝ) (j : ℕ) :
    IntegrableOn
      (fun t => standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
          Real.log t) I := by
  have hPpos : 0 < P := by linarith
  have hcontinuous : ContinuousOn
      (fun t => standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
          Real.log t) (Set.Icc P (2 * P)) := by
    intro t ht
    have htpos : 0 < t := hPpos.trans_le ht.1
    have htone : 1 < t := lt_of_lt_of_le (by norm_num) (hP.trans ht.1)
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htone)
    have hphase : ContinuousAt
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j) t :=
      (differentiableAt_reciprocalPhase_of_pos _ _ _ htpos).continuousAt
    have hnumerator : ContinuousAt
        (fun u => standardAdditiveCharacter
          (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j u)) t :=
      continuous_standardAdditiveCharacter.continuousAt.comp hphase
    have hdenominator : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log htpos.ne')
    exact (hnumerator.div hdenominator (by exact_mod_cast hlog)).continuousWithinAt
  exact (hcontinuous.integrableOn_Icc).mono_set hI

/-- Exact interchange of the finite prime sum and a finite Fourier
polynomial. -/
theorem primeEquidistributionSum_finiteFourierPolynomial
    (P : ℝ) (I : Set ℝ) (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) :
    primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j =
      ∑ q ∈ s, c q * primeFourierModeSum P I q N M j := by
  unfold primeEquidistributionSum finiteFourierPolynomial primeFourierModeSum
  simp_rw [fourierMode2D_reciprocalPair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.mul_sum]

/-- Exact interchange of the logarithmically weighted integral and a finite
Fourier polynomial. -/
theorem primeEquidistributionIntegral_finiteFourierPolynomial
    (I : Set ℝ) (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ)
    (hIntegrable : ∀ q ∈ s, IntegrableOn
      (fun t => standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
          Real.log t) I) :
    primeEquidistributionIntegral I (finiteFourierPolynomial s c) N M j =
      ∑ q ∈ s, c q * fourierModeIntegral I q N M j := by
  unfold primeEquidistributionIntegral finiteFourierPolynomial fourierModeIntegral
  simp_rw [fourierMode2D_reciprocalPair, Finset.sum_div]
  simp_rw [div_eq_mul_inv, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _hq
    rw [MeasureTheory.integral_const_mul]
  · intro q hq
    simpa only [div_eq_mul_inv, mul_assoc] using
      (hIntegrable q hq).const_mul (c q)

/-- Source-facing integral interchange: Tao's scale and interval hypotheses
discharge all integrability obligations. -/
theorem primeEquidistributionIntegral_finiteFourierPolynomial_of_subset
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) :
    primeEquidistributionIntegral I (finiteFourierPolynomial s c) N M j =
      ∑ q ∈ s, c q * fourierModeIntegral I q N M j := by
  apply primeEquidistributionIntegral_finiteFourierPolynomial
  intro q _hq
  exact integrableOn_fourierModeIntegrand hP hI q N M j

/-- The error of a finite Fourier polynomial is bounded by the coefficient-
weighted sum of its modewise errors.  This is the triangle-inequality step in
the source's reduction of Proposition 1.12(ii) to part (i). -/
theorem norm_finiteFourierPolynomial_discrepancy_le
    (P : ℝ) (I : Set ℝ) (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ)
    (hIntegrable : ∀ q ∈ s, IntegrableOn
      (fun t => standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
          Real.log t) I) :
    ‖primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j -
        primeEquidistributionIntegral I (finiteFourierPolynomial s c) N M j‖ ≤
      ∑ q ∈ s, ‖c q‖ *
        ‖primeFourierModeSum P I q N M j -
          fourierModeIntegral I q N M j‖ := by
  rw [primeEquidistributionSum_finiteFourierPolynomial,
    primeEquidistributionIntegral_finiteFourierPolynomial
      I s c N M j hIntegrable,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ q ∈ s,
        (c q * primeFourierModeSum P I q N M j -
          c q * fourierModeIntegral I q N M j)‖ ≤
        ∑ q ∈ s,
          ‖c q * primeFourierModeSum P I q N M j -
            c q * fourierModeIntegral I q N M j‖ := norm_sum_le _ _
    _ = ∑ q ∈ s, ‖c q‖ *
        ‖primeFourierModeSum P I q N M j -
          fourierModeIntegral I q N M j‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [← mul_sub, norm_mul]

/-- Uniform modewise error form of the finite Fourier assembly. -/
theorem norm_finiteFourierPolynomial_discrepancy_le_uniform
    (P : ℝ) (I : Set ℝ) (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) {E : ℝ}
    (hIntegrable : ∀ q ∈ s, IntegrableOn
      (fun t => standardAdditiveCharacter
        (reciprocalPhase ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) j t) /
          Real.log t) I)
    (hmode : ∀ q ∈ s,
      ‖primeFourierModeSum P I q N M j -
        fourierModeIntegral I q N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j -
        primeEquidistributionIntegral I (finiteFourierPolynomial s c) N M j‖ ≤
      (∑ q ∈ s, ‖c q‖) * E := by
  refine (norm_finiteFourierPolynomial_discrepancy_le
    P I s c N M j hIntegrable).trans ?_
  calc
    ∑ q ∈ s, ‖c q‖ *
        ‖primeFourierModeSum P I q N M j -
          fourierModeIntegral I q N M j‖ ≤
        ∑ q ∈ s, ‖c q‖ * E := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hmode q hq) (norm_nonneg _)
    _ = (∑ q ∈ s, ‖c q‖) * E := by
      rw [Finset.sum_mul]

/-- Source-facing uniform Fourier assembly with integrability discharged from
`P ≥ 2` and `I ⊆ [P,2P]`. -/
theorem norm_finiteFourierPolynomial_discrepancy_le_uniform_of_subset
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (N M : ℝ) (j : ℕ) {E : ℝ}
    (hmode : ∀ q ∈ s,
      ‖primeFourierModeSum P I q N M j -
        fourierModeIntegral I q N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I (finiteFourierPolynomial s c) N M j -
        primeEquidistributionIntegral I (finiteFourierPolynomial s c) N M j‖ ≤
      (∑ q ∈ s, ‖c q‖) * E := by
  apply norm_finiteFourierPolynomial_discrepancy_le_uniform
  · intro q _hq
    exact integrableOn_fourierModeIntegrand hP hI q N M j
  · exact hmode

/-- Explicit retained-box version of the finite Fourier reduction.  A
coefficient envelope `C` and a uniform mode error `E` cost exactly
`(2R+1)² C E`. -/
theorem norm_fourierFrequencyBox_discrepancy_le
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Set.Icc P (2 * P))
    (R : ℕ) (c : ℤ × ℤ → ℂ) (N M : ℝ) (j : ℕ)
    {C E : ℝ} (hE : 0 ≤ E)
    (hcoeff : ∀ q ∈ fourierFrequencyBox R, ‖c q‖ ≤ C)
    (hmode : ∀ q ∈ fourierFrequencyBox R,
      ‖primeFourierModeSum P I q N M j -
        fourierModeIntegral I q N M j‖ ≤ E) :
    ‖primeEquidistributionSum P I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N M j -
        primeEquidistributionIntegral I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N M j‖ ≤
      ((2 * R + 1) ^ 2 : ℕ) * C * E := by
  refine (norm_finiteFourierPolynomial_discrepancy_le_uniform_of_subset
    hP hI (fourierFrequencyBox R) c N M j hmode).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_norm_fourierFrequencyBox_le R c hcoeff) hE

/-- Multiplying a frequency parameter by an integer of size at most `L`
preserves Tao's parameter bound after multiplying its explicit constant by
`L`.  This is the bookkeeping used for the retained Fourier modes. -/
theorem vinogradovParameterBound_int_mul
    {ε K P T L : ℝ} (hT : VinogradovParameterBound ε K P T)
    (q : ℤ) (hq : |(q : ℝ)| ≤ L) (hL : 0 ≤ L) :
    VinogradovParameterBound ε (L * K) P ((q : ℝ) * T) := by
  unfold VinogradovParameterBound at hT ⊢
  rw [abs_mul]
  calc
    |(q : ℝ)| * |T| ≤ L * |T| :=
      mul_le_mul_of_nonneg_right hq (abs_nonneg T)
    _ ≤ L * (K * Real.exp ((Real.log P) ^ (3 / 2 - ε))) :=
      mul_le_mul_of_nonneg_left hT hL
    _ = (L * K) * Real.exp ((Real.log P) ^ (3 / 2 - ε)) := by ring

/-- Both parameters of every retained Fourier mode satisfy one uniform
Vinogradov bound, with the explicit constant enlarged by `R+1`. -/
theorem vinogradovParameterBounds_of_mem_fourierFrequencyBox
    {ε K P N M : ℝ} (hN : VinogradovParameterBound ε K P N)
    (hM : VinogradovParameterBound ε K P M)
    {R : ℕ} {q : ℤ × ℤ} (hq : q ∈ fourierFrequencyBox R) :
    VinogradovParameterBound ε (((R : ℝ) + 1) * K) P ((q.1 : ℝ) * N) ∧
      VinogradovParameterBound ε (((R : ℝ) + 1) * K) P ((q.2 : ℝ) * M) := by
  have hqBounds := mem_fourierFrequencyBox.mp hq
  have hqOne : |(q.1 : ℝ)| ≤ (R : ℝ) + 1 := by
    have hqOneR : |(q.1 : ℝ)| ≤ (R : ℝ) := by
      exact_mod_cast hqBounds.1
    linarith
  have hqTwo : |(q.2 : ℝ)| ≤ (R : ℝ) + 1 := by
    have hqTwoR : |(q.2 : ℝ)| ≤ (R : ℝ) := by
      exact_mod_cast hqBounds.2
    linarith
  constructor
  · exact vinogradovParameterBound_int_mul hN q.1 hqOne (by positivity)
  · exact vinogradovParameterBound_int_mul hM q.2 hqTwo (by positivity)

theorem fourierFrequencyBox_parameterConstant_pos
    {K : ℝ} (hK : 0 < K) (R : ℕ) :
    0 < ((R : ℝ) + 1) * K := by positivity

end

end Tao2026
