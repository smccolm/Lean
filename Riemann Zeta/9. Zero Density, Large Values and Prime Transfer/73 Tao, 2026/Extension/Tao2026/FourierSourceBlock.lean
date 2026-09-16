import Tao2026.PrimeSourceBlock
import Tao2026.FourierAssembly
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quadratic Fourier source bridge

This module identifies every Fourier prime mode with the corresponding
unequal-parameter reciprocal-phase sum, records its derivative and elementary
same-sign nonstationarity, and specializes the completed analytic estimate to
the `(1,1)` mode.  For that diagonal mode it proves an explicit inverse-
frequency bound for the logarithmically weighted integral by integration by
parts.
-/

open Complex Filter MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

theorem hasDerivAt_quadraticReciprocalPhase
    (A B : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => reciprocalPhase A B 2 x)
      (-(A * t + 2 * B) / t ^ 3) t := by
  have hraw := (hasDerivAt_const t A).div (hasDerivAt_id t) ht |>.add
    ((hasDerivAt_const t B).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht))
  convert hraw using 1
  · ext x
    simp [reciprocalPhase_eq_div]
  · simp only [id_eq, Pi.pow_apply] at *
    field_simp
    ring

theorem hasDerivAt_standardAdditiveCharacter_quadratic
    (A B : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase A B 2 x))
      ((-2 * Real.pi * Complex.I * (A * t + 2 * B) / t ^ 3) *
        standardAdditiveCharacter (reciprocalPhase A B 2 t)) t := by
  unfold standardAdditiveCharacter
  have hphase := hasDerivAt_quadraticReciprocalPhase A B ht
  convert (Complex.hasDerivAt_exp _).comp t
    (((hasDerivAt_const t (2 * (Real.pi : ℂ) * Complex.I)).mul
      hphase.ofReal_comp)) using 1
  simp only [Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem quadraticReciprocalPhase_deriv_ne_zero_of_pos_nonneg
    {A B t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ht : 0 < t) :
    -(A * t + 2 * B) / t ^ 3 ≠ 0 := by
  have hs : 0 < A * t + 2 * B := by positivity
  exact div_ne_zero (neg_ne_zero.mpr hs.ne') (pow_ne_zero 3 ht.ne')

theorem quadraticReciprocalPhase_deriv_ne_zero_of_neg_nonpos
    {A B t : ℝ} (hA : A < 0) (hB : B ≤ 0) (ht : 0 < t) :
    -(A * t + 2 * B) / t ^ 3 ≠ 0 := by
  have hs : A * t + 2 * B < 0 := by
    have hAt : A * t < 0 := mul_neg_of_neg_of_pos hA ht
    nlinarith
  exact div_ne_zero (neg_ne_zero.mpr hs.ne) (pow_ne_zero 3 ht.ne')

theorem hasDerivAt_diagonalQuadraticReciprocalPhase
    (N : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => reciprocalPhase N N 2 x)
      (-N * (t + 2) / t ^ 3) t := by
  have hraw := (hasDerivAt_const t N).div (hasDerivAt_id t) ht |>.add
    ((hasDerivAt_const t N).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht))
  convert hraw using 1
  · ext x
    simp [reciprocalPhase_eq_div]
  · simp only [id_eq, Pi.pow_apply] at *
    field_simp
    ring

theorem hasDerivAt_standardAdditiveCharacter_diagonalQuadratic
    (N : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase N N 2 x))
      ((-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3) *
        standardAdditiveCharacter (reciprocalPhase N N 2 t)) t := by
  unfold standardAdditiveCharacter
  have hphase : HasDerivAt (fun x : ℝ => reciprocalPhase N N 2 x)
      (-N * (t + 2) / t ^ 3) t := by
    have hraw := (hasDerivAt_const t N).div (hasDerivAt_id t) ht |>.add
      ((hasDerivAt_const t N).div ((hasDerivAt_id t).pow 2)
        (pow_ne_zero 2 ht))
    convert hraw using 1
    · ext x
      simp [reciprocalPhase_eq_div]
    · simp only [id_eq, Pi.pow_apply] at *
      field_simp
      ring
  convert (Complex.hasDerivAt_exp _).comp t
    (((hasDerivAt_const t (2 * (Real.pi : ℂ) * Complex.I)).mul
      hphase.ofReal_comp)) using 1
  simp only [Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem primeFourierModeSum_Ico_one_one
    {P a b : ℕ} (hP : 2 ≤ P) (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (N : ℝ) :
    primeFourierModeSum (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
        ((1, 1) : ℤ × ℤ) N N 2 =
      primeReciprocalPhaseSum a b N N 2 := by
  classical
  have hsubset : Set.Ico (a : ℝ) (b : ℝ) ⊆
      Set.Icc (P : ℝ) (2 * P : ℝ) := by
    intro x hx
    constructor
    · exact (show (P : ℝ) ≤ a from by exact_mod_cast hPa).trans hx.1
    · exact hx.2.le.trans (by exact_mod_cast hbP)
  rw [primeReciprocalPhaseSum_eq_filter]
  unfold primeFourierModeSum
  apply Finset.sum_congr
  · ext n
    rw [mem_primesInScaleSet (by exact_mod_cast hP) hsubset,
      Finset.mem_filter, Finset.mem_Ico]
    aesop
  · intro n hn
    simp

/-- Every half-open Fourier prime sum is exactly a reciprocal-phase prime sum
with the two coefficients multiplied by the corresponding integer mode. -/
theorem primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    {P a b : ℕ} (hP : 2 ≤ P) (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (q : ℤ × ℤ) (N M : ℝ) :
    primeFourierModeSum (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
        q N M 2 =
      primeReciprocalPhaseSum a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 := by
  classical
  have hsubset : Set.Ico (a : ℝ) (b : ℝ) ⊆
      Set.Icc (P : ℝ) (2 * P : ℝ) := by
    intro x hx
    constructor
    · exact (show (P : ℝ) ≤ a from by exact_mod_cast hPa).trans hx.1
    · exact hx.2.le.trans (by exact_mod_cast hbP)
  rw [primeReciprocalPhaseSum_eq_filter]
  unfold primeFourierModeSum
  apply Finset.sum_congr
  · ext n
    rw [mem_primesInScaleSet (by exact_mod_cast hP) hsubset,
      Finset.mem_filter, Finset.mem_Ico]
    aesop
  · intro n hn
    rfl

def diagonalQuadraticIntegralAmplitude (t : ℝ) : ℝ :=
  t ^ 3 / ((t + 2) * Real.log t)

theorem hasDerivAt_diagonalQuadraticIntegralAmplitude
    {t : ℝ} (ht : 1 < t) :
    HasDerivAt diagonalQuadraticIntegralAmplitude
      (t ^ 2 * ((2 * t + 6) * Real.log t - (t + 2)) /
        (((t + 2) * Real.log t) ^ 2)) t := by
  unfold diagonalQuadraticIntegralAmplitude
  have hden : (t + 2) * Real.log t ≠ 0 := by
    have ht2 : 0 < t + 2 := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
    exact mul_ne_zero (ne_of_gt ht2) hlog
  convert ((hasDerivAt_id t).pow 3).div
    (((hasDerivAt_id t).add_const 2).mul (Real.hasDerivAt_log (by linarith)))
    hden using 1
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply] at *
  field_simp
  ring

theorem diagonalQuadraticIntegralAmplitudeDeriv_nonneg
    {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ t ^ 2 * ((2 * t + 6) * Real.log t - (t + 2)) /
      (((t + 2) * Real.log t) ^ 2) := by
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogMono : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) ht
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := hlogTwo.trans hlogMono
  have hcoef : 0 ≤ 2 * t + 6 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hcoef
  have hbracket : 0 ≤ (2 * t + 6) * Real.log t - (t + 2) := by
    nlinarith
  exact div_nonneg (mul_nonneg (sq_nonneg t) hbracket) (sq_nonneg _)

def diagonalQuadraticIntegralAmplitudeDeriv (t : ℝ) : ℝ :=
  t ^ 2 * ((2 * t + 6) * Real.log t - (t + 2)) /
    (((t + 2) * Real.log t) ^ 2)

def diagonalQuadraticIntegralFactor (N : ℝ) : ℂ :=
  -(1 / (2 * Real.pi * Complex.I * N))

def diagonalQuadraticIntegralWeight (N t : ℝ) : ℂ :=
  diagonalQuadraticIntegralFactor N * diagonalQuadraticIntegralAmplitude t

theorem hasDerivAt_diagonalQuadraticIntegralWeight
    (N : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (diagonalQuadraticIntegralWeight N)
      (diagonalQuadraticIntegralFactor N *
        diagonalQuadraticIntegralAmplitudeDeriv t) t := by
  have hamp : HasDerivAt diagonalQuadraticIntegralAmplitude
      (diagonalQuadraticIntegralAmplitudeDeriv t) t := by
    unfold diagonalQuadraticIntegralAmplitudeDeriv
    unfold diagonalQuadraticIntegralAmplitude
    have hden : (t + 2) * Real.log t ≠ 0 := by
      exact mul_ne_zero (by linarith) (ne_of_gt (Real.log_pos ht))
    convert ((hasDerivAt_id t).pow 3).div
      (((hasDerivAt_id t).add_const 2).mul
        (Real.hasDerivAt_log (by linarith))) hden using 1
    simp only [id_eq, Pi.pow_apply, Pi.mul_apply] at *
    field_simp
    ring
  unfold diagonalQuadraticIntegralWeight
  convert (hasDerivAt_const t (diagonalQuadraticIntegralFactor N)).mul
    hamp.ofReal_comp using 1
  simp

theorem diagonalQuadraticIntegralWeight_mul_characterDeriv
    (N : ℝ) {t : ℝ} (hN : N ≠ 0) (ht : 1 < t) :
    diagonalQuadraticIntegralWeight N t *
        ((-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3) *
          standardAdditiveCharacter (reciprocalPhase N N 2 t)) =
      standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t := by
  have ht0 : t ≠ 0 := by linarith
  have ht2 : t + 2 ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have ht2c : ((t + 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht2
  have hlogc : ((Real.log t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hsumc : (2 : ℂ) + (t : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 : ℝ) + t ≠ 0 by linarith)
  have hscalar : diagonalQuadraticIntegralWeight N t *
      (-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3) =
        (1 : ℂ) / Real.log t := by
    unfold diagonalQuadraticIntegralWeight diagonalQuadraticIntegralFactor
      diagonalQuadraticIntegralAmplitude
    push_cast
    field_simp [hNc, htc, ht2c, hlogc, hsumc]
    exact div_self (by exact_mod_cast ht2)
  calc
    diagonalQuadraticIntegralWeight N t *
        ((-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3) *
          standardAdditiveCharacter (reciprocalPhase N N 2 t)) =
        (diagonalQuadraticIntegralWeight N t *
          (-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3)) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t) := by ring
    _ = ((1 : ℂ) / Real.log t) *
          standardAdditiveCharacter (reciprocalPhase N N 2 t) := by rw [hscalar]
    _ = standardAdditiveCharacter (reciprocalPhase N N 2 t) /
          Real.log t := by ring

def diagonalQuadraticCharacterDeriv (N t : ℝ) : ℂ :=
  (-2 * Real.pi * Complex.I * N * (t + 2) / t ^ 3) *
    standardAdditiveCharacter (reciprocalPhase N N 2 t)

theorem diagonalQuadraticIntervalIntegral_eq_parts
    {N a b : ℝ} (hN : N ≠ 0) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t =
      diagonalQuadraticIntegralWeight N b *
          standardAdditiveCharacter (reciprocalPhase N N 2 b) -
        diagonalQuadraticIntegralWeight N a *
          standardAdditiveCharacter (reciprocalPhase N N 2 a) -
        ∫ t in a..b,
          (diagonalQuadraticIntegralFactor N *
              diagonalQuadraticIntegralAmplitudeDeriv t) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t) := by
  have hpoint : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (show 1 < a by linarith).trans_le ht.1
  have hu : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (diagonalQuadraticIntegralWeight N)
        (diagonalQuadraticIntegralFactor N *
          diagonalQuadraticIntegralAmplitudeDeriv t) t := by
    intro t ht
    exact hasDerivAt_diagonalQuadraticIntegralWeight N (hpoint t ht)
  have hv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt
        (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase N N 2 x))
        (diagonalQuadraticCharacterDeriv N t) t := by
    intro t ht
    unfold diagonalQuadraticCharacterDeriv
    exact hasDerivAt_standardAdditiveCharacter_diagonalQuadratic N
      (by linarith [hpoint t ht])
  have hu'int : IntervalIntegrable
      (fun t => diagonalQuadraticIntegralFactor N *
        diagonalQuadraticIntegralAmplitudeDeriv t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpoint t ht
    apply ContinuousAt.continuousWithinAt
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hden : (t + 2) * Real.log t ≠ 0 :=
      mul_ne_zero (by linarith) hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt (fun x : ℝ => (x + 2) * Real.log x) t :=
      (continuousAt_id.add continuousAt_const).mul hlogcont
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 * ((2 * x + 6) * Real.log x - (x + 2))) t := by
      fun_prop
    have hreal : ContinuousAt diagonalQuadraticIntegralAmplitudeDeriv t := by
      unfold diagonalQuadraticIntegralAmplitudeDeriv
      exact hnumcont.div (hdencont.pow 2) (pow_ne_zero 2 hden)
    exact continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hreal)
  have hv'int : IntervalIntegrable (diagonalQuadraticCharacterDeriv N)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpoint t ht
    apply ContinuousAt.continuousWithinAt
    unfold diagonalQuadraticCharacterDeriv
    have hphase : ContinuousAt
        (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase N N 2 x)) t :=
      (hasDerivAt_standardAdditiveCharacter_diagonalQuadratic N
        (by linarith)).continuousAt
    have htcast : ContinuousAt (fun x : ℝ => (x : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt
    have ht0c : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by linarith)
    have hcoeff : ContinuousAt
        (fun x : ℝ => -2 * (Real.pi : ℂ) * Complex.I * N * (x + 2) /
          (x : ℂ) ^ 3) t := by
      exact (((((continuousAt_const.mul continuousAt_const).mul continuousAt_const).mul
        continuousAt_const).mul (htcast.add continuousAt_const)).div
          (htcast.pow 3) (pow_ne_zero 3 ht0c))
    exact hcoeff.mul hphase
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu'int hv'int
  calc
    (∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t) =
        ∫ t in a..b,
          diagonalQuadraticIntegralWeight N t *
            diagonalQuadraticCharacterDeriv N t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (diagonalQuadraticIntegralWeight_mul_characterDeriv N hN
        (by linarith [ht.1])).symm
    _ = _ := hibp

theorem diagonalQuadraticIntegralAmplitude_nonneg
    {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ diagonalQuadraticIntegralAmplitude t := by
  unfold diagonalQuadraticIntegralAmplitude
  exact div_nonneg (by positivity)
    (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))

theorem intervalIntegral_diagonalQuadraticIntegralAmplitudeDeriv_eq_sub
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, diagonalQuadraticIntegralAmplitudeDeriv t =
      diagonalQuadraticIntegralAmplitude b -
        diagonalQuadraticIntegralAmplitude a := by
  have hpoint : ∀ t ∈ Set.Icc a b, 1 < t := by
    intro t ht
    exact (show 1 < a by linarith).trans_le ht.1
  have hcont : ContinuousOn diagonalQuadraticIntegralAmplitude
      (Set.Icc a b) := by
    intro t ht
    exact (hasDerivAt_diagonalQuadraticIntegralAmplitude
      (hpoint t ht)).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt diagonalQuadraticIntegralAmplitude
        (diagonalQuadraticIntegralAmplitudeDeriv t) t := by
    intro t ht
    exact hasDerivAt_diagonalQuadraticIntegralAmplitude
      ((show 1 < a by linarith).trans ht.1)
  have hint : IntervalIntegrable diagonalQuadraticIntegralAmplitudeDeriv
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := (show 1 < a by linarith).trans_le ht.1
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hden : (t + 2) * Real.log t ≠ 0 :=
      mul_ne_zero (by linarith) hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt (fun x : ℝ => (x + 2) * Real.log x) t :=
      (continuousAt_id.add continuousAt_const).mul hlogcont
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 * ((2 * x + 6) * Real.log x - (x + 2))) t := by
      fun_prop
    unfold diagonalQuadraticIntegralAmplitudeDeriv
    exact (hnumcont.div (hdencont.pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hcont hderiv hint

theorem norm_diagonalQuadraticIntervalIntegral_le
    {N a b : ℝ} (hN : N ≠ 0) (ha : 2 ≤ a) (hab : a ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t‖ ≤
      3 * ‖diagonalQuadraticIntegralFactor N‖ *
        diagonalQuadraticIntegralAmplitude b := by
  rw [diagonalQuadraticIntervalIntegral_eq_parts hN ha hab]
  have hampa : 0 ≤ diagonalQuadraticIntegralAmplitude a :=
    diagonalQuadraticIntegralAmplitude_nonneg ha
  have hampb : 0 ≤ diagonalQuadraticIntegralAmplitude b :=
    diagonalQuadraticIntegralAmplitude_nonneg (ha.trans hab)
  have hampDeriv : ∀ t ∈ Set.Icc a b,
      0 ≤ diagonalQuadraticIntegralAmplitudeDeriv t := by
    intro t ht
    exact diagonalQuadraticIntegralAmplitudeDeriv_nonneg (ha.trans ht.1)
  have hAmpInt :=
    intervalIntegral_diagonalQuadraticIntegralAmplitudeDeriv_eq_sub ha hab
  have hderivInt : IntervalIntegrable diagonalQuadraticIntegralAmplitudeDeriv
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := (show 1 < a by linarith).trans_le ht.1
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hden : (t + 2) * Real.log t ≠ 0 :=
      mul_ne_zero (by linarith) hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt (fun x : ℝ => (x + 2) * Real.log x) t :=
      (continuousAt_id.add continuousAt_const).mul hlogcont
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 * ((2 * x + 6) * Real.log x - (x + 2))) t := by
      fun_prop
    unfold diagonalQuadraticIntegralAmplitudeDeriv
    exact (hnumcont.div (hdencont.pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  have hgint : IntervalIntegrable
      (fun t => ‖diagonalQuadraticIntegralFactor N‖ *
        diagonalQuadraticIntegralAmplitudeDeriv t) volume a b :=
    hderivInt.const_mul _
  have hintegralNorm :
      ‖∫ t in a..b,
          (diagonalQuadraticIntegralFactor N *
              diagonalQuadraticIntegralAmplitudeDeriv t) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t)‖ ≤
        ‖diagonalQuadraticIntegralFactor N‖ *
          (diagonalQuadraticIntegralAmplitude b -
            diagonalQuadraticIntegralAmplitude a) := by
    calc
      ‖∫ t in a..b,
          (diagonalQuadraticIntegralFactor N *
              diagonalQuadraticIntegralAmplitudeDeriv t) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t)‖ ≤
          ∫ t in a..b, ‖diagonalQuadraticIntegralFactor N‖ *
            diagonalQuadraticIntegralAmplitudeDeriv t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hgint
        filter_upwards with t ht
        have ht2 : 2 ≤ t := ha.trans ht.1.le
        rw [norm_mul, norm_mul, norm_standardAdditiveCharacter, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hampDeriv t ⟨ht.1.le, ht.2⟩)]
      _ = ‖diagonalQuadraticIntegralFactor N‖ *
          (diagonalQuadraticIntegralAmplitude b -
            diagonalQuadraticIntegralAmplitude a) := by
        rw [intervalIntegral.integral_const_mul, hAmpInt]
  have hendpoint (t : ℝ) (ht : 2 ≤ t) :
      ‖diagonalQuadraticIntegralWeight N t *
          standardAdditiveCharacter (reciprocalPhase N N 2 t)‖ =
        ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude t := by
    rw [norm_mul, norm_standardAdditiveCharacter, mul_one]
    unfold diagonalQuadraticIntegralWeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (diagonalQuadraticIntegralAmplitude_nonneg ht)]
  calc
    ‖diagonalQuadraticIntegralWeight N b *
          standardAdditiveCharacter (reciprocalPhase N N 2 b) -
        diagonalQuadraticIntegralWeight N a *
          standardAdditiveCharacter (reciprocalPhase N N 2 a) -
        ∫ t in a..b,
          (diagonalQuadraticIntegralFactor N *
              diagonalQuadraticIntegralAmplitudeDeriv t) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t)‖ ≤
        ‖diagonalQuadraticIntegralWeight N b *
          standardAdditiveCharacter (reciprocalPhase N N 2 b)‖ +
        ‖diagonalQuadraticIntegralWeight N a *
          standardAdditiveCharacter (reciprocalPhase N N 2 a)‖ +
        ‖∫ t in a..b,
          (diagonalQuadraticIntegralFactor N *
              diagonalQuadraticIntegralAmplitudeDeriv t) *
            standardAdditiveCharacter (reciprocalPhase N N 2 t)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude b +
        ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude a +
        ‖diagonalQuadraticIntegralFactor N‖ *
          (diagonalQuadraticIntegralAmplitude b -
            diagonalQuadraticIntegralAmplitude a) := by
      rw [hendpoint b (ha.trans hab), hendpoint a ha]
      exact add_le_add le_rfl hintegralNorm
    _ = 2 * ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude b := by ring
    _ ≤ 3 * ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude b := by
      have hprod : 0 ≤ ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude b :=
        mul_nonneg (norm_nonneg _) hampb
      nlinarith

theorem norm_diagonalQuadraticIntegralFactor
    (N : ℝ) :
    ‖diagonalQuadraticIntegralFactor N‖ =
      (2 * Real.pi * |N|)⁻¹ := by
  unfold diagonalQuadraticIntegralFactor
  rw [norm_neg, div_eq_mul_inv, one_mul, norm_inv, norm_mul, norm_mul,
    norm_mul]
  simp only [norm_ofNat, norm_real, norm_I, norm_real, mul_one]
  rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos, Real.norm_eq_abs]

theorem diagonalQuadraticIntegralAmplitude_le_dyadic
    {P b : ℝ} (hP : 2 ≤ P) (hPb : P ≤ b) (hbP : b ≤ 2 * P) :
    diagonalQuadraticIntegralAmplitude b ≤
      4 * P ^ 2 / Real.log P := by
  have hPpos : 0 < P := by linarith
  have hbpos : 0 < b := hPpos.trans_le hPb
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlogle : Real.log P ≤ Real.log b :=
    Real.log_le_log hPpos hPb
  have hdenLower : b * Real.log P ≤ (b + 2) * Real.log b := by
    calc
      b * Real.log P ≤ b * Real.log b :=
        mul_le_mul_of_nonneg_left hlogle hbpos.le
      _ ≤ (b + 2) * Real.log b := by
        exact mul_le_mul_of_nonneg_right (by linarith) hlogb.le
  have hfirst : diagonalQuadraticIntegralAmplitude b ≤
      b ^ 3 / (b * Real.log P) := by
    unfold diagonalQuadraticIntegralAmplitude
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos hbpos hlogP) hdenLower
  have hbSq : b ^ 2 ≤ 4 * P ^ 2 := by nlinarith
  calc
    diagonalQuadraticIntegralAmplitude b ≤
        b ^ 3 / (b * Real.log P) := hfirst
    _ = b ^ 2 / Real.log P := by field_simp
    _ ≤ 4 * P ^ 2 / Real.log P :=
      div_le_div_of_nonneg_right hbSq hlogP.le

theorem norm_diagonalQuadraticIntervalIntegral_le_dyadic
    {N P a b : ℝ} (hN : N ≠ 0) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t‖ ≤
      6 * P ^ 2 / (|N| * Real.log P) := by
  have ha : 2 ≤ a := hP.trans hPa
  have hraw := norm_diagonalQuadraticIntervalIntegral_le hN ha hab
  have hamp := diagonalQuadraticIntegralAmplitude_le_dyadic hP
    (hPa.trans hab) hbP
  have hfactor := norm_diagonalQuadraticIntegralFactor N
  have hNabs : 0 < |N| := abs_pos.mpr hN
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase N N 2 t) / Real.log t‖ ≤
        3 * ‖diagonalQuadraticIntegralFactor N‖ *
          diagonalQuadraticIntegralAmplitude b := hraw
    _ ≤ 3 * ‖diagonalQuadraticIntegralFactor N‖ *
          (4 * P ^ 2 / Real.log P) := by gcongr
    _ = 12 * P ^ 2 /
          ((2 * Real.pi * |N|) * Real.log P) := by
      rw [hfactor]
      field_simp
      ring
    _ ≤ 6 * P ^ 2 / (|N| * Real.log P) := by
      have hpi : 2 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hnum : 0 ≤ 12 * P ^ 2 := by positivity
      have hden : 0 < |N| * Real.log P := mul_pos hNabs hlogP
      rw [mul_assoc]
      rw [show 12 * P ^ 2 / (2 * Real.pi * (|N| * Real.log P)) =
          (12 * P ^ 2 / (2 * Real.pi)) / (|N| * Real.log P) by
        field_simp]
      apply (div_le_div_iff_of_pos_right hden).2
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [sq_nonneg P]

theorem norm_fourierModeIntegral_Ico_one_one_le_dyadic
    {N P a b : ℝ} (hN : N ≠ 0) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) ((1, 1) : ℤ × ℤ) N N 2‖ ≤
      6 * P ^ 2 / (|N| * Real.log P) := by
  have hraw := norm_diagonalQuadraticIntervalIntegral_le_dyadic
    hN hP hPa hab hbP
  unfold fourierModeIntegral
  simp only [Int.cast_one, one_mul]
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact hraw

/-- The completed prime estimate and the oscillatory integral bound assemble
into the exact discrepancy for the diagonal `(1,1)` Fourier mode.  The
remaining general Fourier step must treat unequal mode coefficients. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_one_one_le_sourceRange
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N : ℝ),
      P ≤ a → a < b → b ≤ 2 * P → N ≠ 0 →
      2 * (b : ℝ) *
          (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ |N| →
      |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) ((1, 1) : ℤ × ℤ) N N 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ))
          ((1, 1) : ℤ × ℤ) N N 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          6 * (P : ℝ) ^ 2 / (|N| * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b N hPa hab hbP hN hlower hupper
  have hsum := primeFourierModeSum_Ico_one_one hP hPa hbP N
  have hprimeBound := hprimeP a b N hPa hab hbP hN hlower hupper
  have hintegralBound := norm_fourierModeIntegral_Ico_one_one_le_dyadic
    (N := N) (P := (P : ℝ)) (a := (a : ℝ)) (b := (b : ℝ))
    hN (by exact_mod_cast hP) (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

end
end Tao2026
