import Tao2026.UnequalPrimeSourceBlock
import Tao2026.FourierSourceBlock

/-!
# Unequal Fourier source bridge

This module begins the Fourier-side use of the unequal prime estimate.  It
proves the logarithmic oscillatory-integral bound when the linear coefficient
is positive and the quadratic coefficient is nonnegative, the basic
nonstationary same-sign chamber.
-/

open Complex Filter MeasureTheory Set
open scoped Interval ComplexConjugate

namespace Tao2026

noncomputable section

def unequalQuadraticIntegralAmplitude (A B t : ℝ) : ℝ :=
  t ^ 3 / ((A * t + 2 * B) * Real.log t)

def unequalQuadraticIntegralAmplitudeDeriv (A B t : ℝ) : ℝ :=
  t ^ 2 * ((2 * A * t + 6 * B) * Real.log t - (A * t + 2 * B)) /
    (((A * t + 2 * B) * Real.log t) ^ 2)

def unequalQuadraticIntegralFactor : ℂ :=
  -(1 / (2 * Real.pi * Complex.I))

def unequalQuadraticIntegralWeight (A B t : ℝ) : ℂ :=
  unequalQuadraticIntegralFactor * unequalQuadraticIntegralAmplitude A B t

def unequalQuadraticCharacterDeriv (A B t : ℝ) : ℂ :=
  ((-2 * Real.pi * Complex.I * (A * t + 2 * B) / t ^ 3) *
    standardAdditiveCharacter (reciprocalPhase A B 2 t))

theorem hasDerivAt_unequalQuadraticIntegralAmplitude
    {A B t : ℝ} (ht : 1 < t) (hlin : A * t + 2 * B ≠ 0) :
    HasDerivAt (unequalQuadraticIntegralAmplitude A B)
      (unequalQuadraticIntegralAmplitudeDeriv A B t) t := by
  unfold unequalQuadraticIntegralAmplitude unequalQuadraticIntegralAmplitudeDeriv
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hden : (A * t + 2 * B) * Real.log t ≠ 0 :=
    mul_ne_zero hlin hlog
  convert ((hasDerivAt_id t).pow 3).div
    ((((hasDerivAt_const t A).mul (hasDerivAt_id t)).add_const (2 * B)).mul
      (Real.hasDerivAt_log (by linarith))) hden using 1
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply] at *
  field_simp
  ring

theorem unequalQuadraticIntegralAmplitudeDeriv_nonneg
    {A B t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ht : 2 ≤ t) :
    0 ≤ unequalQuadraticIntegralAmplitudeDeriv A B t := by
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogMono : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) ht
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := hlogTwo.trans hlogMono
  have hcoef : 0 ≤ 2 * A * t + 6 * B := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hcoef
  have hbracket :
      0 ≤ (2 * A * t + 6 * B) * Real.log t - (A * t + 2 * B) := by
    nlinarith
  unfold unequalQuadraticIntegralAmplitudeDeriv
  exact div_nonneg (mul_nonneg (sq_nonneg t) hbracket) (sq_nonneg _)

theorem unequalQuadraticIntegralAmplitude_nonneg
    {A B t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ht : 2 ≤ t) :
    0 ≤ unequalQuadraticIntegralAmplitude A B t := by
  unfold unequalQuadraticIntegralAmplitude
  have hlin : 0 ≤ A * t + 2 * B := by positivity
  exact div_nonneg (by positivity)
    (mul_nonneg hlin (Real.log_nonneg (by linarith)))

theorem hasDerivAt_unequalQuadraticIntegralWeight
    {A B t : ℝ} (ht : 1 < t) (hlin : A * t + 2 * B ≠ 0) :
    HasDerivAt (unequalQuadraticIntegralWeight A B)
      (unequalQuadraticIntegralFactor *
        unequalQuadraticIntegralAmplitudeDeriv A B t) t := by
  have hamp := hasDerivAt_unequalQuadraticIntegralAmplitude ht hlin
  unfold unequalQuadraticIntegralWeight
  convert (hasDerivAt_const t unequalQuadraticIntegralFactor).mul
    hamp.ofReal_comp using 1
  simp

theorem unequalQuadraticIntegralWeight_mul_characterDeriv
    {A B t : ℝ} (ht : 1 < t) (hlin : A * t + 2 * B ≠ 0) :
    unequalQuadraticIntegralWeight A B t *
        unequalQuadraticCharacterDeriv A B t =
      standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hlinc : ((A * t + 2 * B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlin
  have hlogc : ((Real.log t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hscalar : unequalQuadraticIntegralWeight A B t *
      (-2 * Real.pi * Complex.I * (A * t + 2 * B) / t ^ 3) =
        (1 : ℂ) / Real.log t := by
    unfold unequalQuadraticIntegralWeight unequalQuadraticIntegralFactor
      unequalQuadraticIntegralAmplitude
    push_cast
    field_simp [htc, hlinc, hlogc]
    exact div_self (by simpa [mul_comm] using hlinc)
  unfold unequalQuadraticCharacterDeriv
  calc
    unequalQuadraticIntegralWeight A B t *
        ((-2 * Real.pi * Complex.I * (A * t + 2 * B) / t ^ 3) *
          standardAdditiveCharacter (reciprocalPhase A B 2 t)) =
        (unequalQuadraticIntegralWeight A B t *
          (-2 * Real.pi * Complex.I * (A * t + 2 * B) / t ^ 3)) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t) := by ring
    _ = ((1 : ℂ) / Real.log t) *
          standardAdditiveCharacter (reciprocalPhase A B 2 t) := by rw [hscalar]
    _ = standardAdditiveCharacter (reciprocalPhase A B 2 t) /
          Real.log t := by ring

theorem unequalQuadraticIntervalIntegral_eq_parts_of_linear_ne
    {A B a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.uIcc a b, A * t + 2 * B ≠ 0) :
    ∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t =
      unequalQuadraticIntegralWeight A B b *
          standardAdditiveCharacter (reciprocalPhase A B 2 b) -
        unequalQuadraticIntegralWeight A B a *
          standardAdditiveCharacter (reciprocalPhase A B 2 a) -
        ∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t) := by
  have hpoint : ∀ t ∈ Set.uIcc a b, 1 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (show 1 < a by linarith).trans_le ht.1
  have hu : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (unequalQuadraticIntegralWeight A B)
        (unequalQuadraticIntegralFactor *
          unequalQuadraticIntegralAmplitudeDeriv A B t) t := by
    intro t ht
    exact hasDerivAt_unequalQuadraticIntegralWeight (hpoint t ht) (hlin t ht)
  have hv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt
        (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase A B 2 x))
        (unequalQuadraticCharacterDeriv A B t) t := by
    intro t ht
    unfold unequalQuadraticCharacterDeriv
    exact hasDerivAt_standardAdditiveCharacter_quadratic A B
      (by linarith [hpoint t ht])
  have hu'int : IntervalIntegrable
      (fun t => unequalQuadraticIntegralFactor *
        unequalQuadraticIntegralAmplitudeDeriv A B t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpoint t ht
    apply ContinuousAt.continuousWithinAt
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hlin0 : A * t + 2 * B ≠ 0 := hlin t ht
    have hden : (A * t + 2 * B) * Real.log t ≠ 0 :=
      mul_ne_zero hlin0 hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt
        (fun x : ℝ => (A * x + 2 * B) * Real.log x) t := by fun_prop
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 *
          ((2 * A * x + 6 * B) * Real.log x - (A * x + 2 * B))) t := by
      fun_prop
    have hreal : ContinuousAt (unequalQuadraticIntegralAmplitudeDeriv A B) t := by
      unfold unequalQuadraticIntegralAmplitudeDeriv
      exact hnumcont.div (hdencont.pow 2) (pow_ne_zero 2 hden)
    exact continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp hreal)
  have hv'int : IntervalIntegrable (unequalQuadraticCharacterDeriv A B)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpoint t ht
    apply ContinuousAt.continuousWithinAt
    unfold unequalQuadraticCharacterDeriv
    have hphase : ContinuousAt
        (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase A B 2 x)) t :=
      (hasDerivAt_standardAdditiveCharacter_quadratic A B
        (by linarith)).continuousAt
    have htcast : ContinuousAt (fun x : ℝ => (x : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt
    have ht0c : (t : ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by linarith)
    have hcoeff : ContinuousAt
        (fun x : ℝ => -2 * (Real.pi : ℂ) * Complex.I *
          ((A : ℂ) * x + 2 * B) / (x : ℂ) ^ 3) t := by
      have hnum : ContinuousAt
          (fun x : ℝ => -2 * (Real.pi : ℂ) * Complex.I *
            ((A : ℂ) * x + 2 * B)) t := by fun_prop
      exact hnum.div (htcast.pow 3) (pow_ne_zero 3 ht0c)
    exact hcoeff.mul hphase
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu'int hv'int
  calc
    (∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) =
        ∫ t in a..b,
          unequalQuadraticIntegralWeight A B t *
            unequalQuadraticCharacterDeriv A B t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      have htu : t ∈ Set.uIcc a b := by
        rw [uIcc_of_le hab]
        exact ht
      have hlin0 : A * t + 2 * B ≠ 0 := hlin t htu
      exact (unequalQuadraticIntegralWeight_mul_characterDeriv
        (by linarith [ht.1]) hlin0).symm
    _ = _ := hibp

theorem unequalQuadraticIntervalIntegral_eq_parts
    {A B a b : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t =
      unequalQuadraticIntegralWeight A B b *
          standardAdditiveCharacter (reciprocalPhase A B 2 b) -
        unequalQuadraticIntegralWeight A B a *
          standardAdditiveCharacter (reciprocalPhase A B 2 a) -
        ∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t) := by
  apply unequalQuadraticIntervalIntegral_eq_parts_of_linear_ne ha hab
  intro t ht
  rw [uIcc_of_le hab] at ht
  have htpos : 0 < t := lt_of_lt_of_le (by linarith : 0 < a) ht.1
  exact ne_of_gt (by positivity)

theorem intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub_of_linear_ne
    {A B a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0) :
    ∫ t in a..b, unequalQuadraticIntegralAmplitudeDeriv A B t =
      unequalQuadraticIntegralAmplitude A B b -
        unequalQuadraticIntegralAmplitude A B a := by
  have hpoint : ∀ t ∈ Set.Icc a b, 1 < t := by
    intro t ht
    exact (show 1 < a by linarith).trans_le ht.1
  have hcont : ContinuousOn (unequalQuadraticIntegralAmplitude A B)
      (Set.Icc a b) := by
    intro t ht
    exact (hasDerivAt_unequalQuadraticIntegralAmplitude
      (hpoint t ht) (hlin t ht)).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (unequalQuadraticIntegralAmplitude A B)
        (unequalQuadraticIntegralAmplitudeDeriv A B t) t := by
    intro t ht
    apply hasDerivAt_unequalQuadraticIntegralAmplitude
    · exact (show 1 < a by linarith).trans ht.1
    · exact hlin t ⟨ht.1.le, ht.2.le⟩
  have hint : IntervalIntegrable (unequalQuadraticIntegralAmplitudeDeriv A B)
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := (show 1 < a by linarith).trans_le ht.1
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hlin0 : A * t + 2 * B ≠ 0 := hlin t ht
    have hden : (A * t + 2 * B) * Real.log t ≠ 0 :=
      mul_ne_zero hlin0 hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt
        (fun x : ℝ => (A * x + 2 * B) * Real.log x) t := by fun_prop
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 *
          ((2 * A * x + 6 * B) * Real.log x - (A * x + 2 * B))) t := by
      fun_prop
    unfold unequalQuadraticIntegralAmplitudeDeriv
    exact (hnumcont.div (hdencont.pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hcont hderiv hint

theorem intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub
    {A B a b : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, unequalQuadraticIntegralAmplitudeDeriv A B t =
      unequalQuadraticIntegralAmplitude A B b -
        unequalQuadraticIntegralAmplitude A B a := by
  apply intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub_of_linear_ne
    ha hab
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le (by linarith : 0 < a) ht.1
  exact ne_of_gt (by positivity)

theorem norm_unequalQuadraticIntervalIntegral_le
    {A B a b : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (ha : 2 ≤ a) (hab : a ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      3 * ‖unequalQuadraticIntegralFactor‖ *
        unequalQuadraticIntegralAmplitude A B b := by
  rw [unequalQuadraticIntervalIntegral_eq_parts hA hB ha hab]
  have hampa : 0 ≤ unequalQuadraticIntegralAmplitude A B a :=
    unequalQuadraticIntegralAmplitude_nonneg hA hB ha
  have hampb : 0 ≤ unequalQuadraticIntegralAmplitude A B b :=
    unequalQuadraticIntegralAmplitude_nonneg hA hB (ha.trans hab)
  have hampDeriv : ∀ t ∈ Set.Icc a b,
      0 ≤ unequalQuadraticIntegralAmplitudeDeriv A B t := by
    intro t ht
    exact unequalQuadraticIntegralAmplitudeDeriv_nonneg hA hB (ha.trans ht.1)
  have hAmpInt :=
    intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub
      hA hB ha hab
  have hderivInt : IntervalIntegrable
      (unequalQuadraticIntegralAmplitudeDeriv A B) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := (show 1 < a by linarith).trans_le ht.1
    have htpos : 0 < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have hlin0 : A * t + 2 * B ≠ 0 := by positivity
    have hden : (A * t + 2 * B) * Real.log t ≠ 0 :=
      mul_ne_zero hlin0 hlog
    have hlogcont : ContinuousAt Real.log t :=
      Real.continuousAt_log htpos.ne'
    have hdencont : ContinuousAt
        (fun x : ℝ => (A * x + 2 * B) * Real.log x) t := by fun_prop
    have hnumcont : ContinuousAt
        (fun x : ℝ => x ^ 2 *
          ((2 * A * x + 6 * B) * Real.log x - (A * x + 2 * B))) t := by
      fun_prop
    unfold unequalQuadraticIntegralAmplitudeDeriv
    exact (hnumcont.div (hdencont.pow 2)
      (pow_ne_zero 2 hden)).continuousWithinAt
  have hgint : IntervalIntegrable
      (fun t => ‖unequalQuadraticIntegralFactor‖ *
        unequalQuadraticIntegralAmplitudeDeriv A B t) volume a b :=
    hderivInt.const_mul _
  have hintegralNorm :
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
        ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B b -
            unequalQuadraticIntegralAmplitude A B a) := by
    calc
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
          ∫ t in a..b, ‖unequalQuadraticIntegralFactor‖ *
            unequalQuadraticIntegralAmplitudeDeriv A B t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hgint
        filter_upwards with t ht
        have ht2 : 2 ≤ t := ha.trans ht.1.le
        rw [norm_mul, norm_mul, norm_standardAdditiveCharacter, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hampDeriv t ⟨ht.1.le, ht.2⟩)]
      _ = ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B b -
            unequalQuadraticIntegralAmplitude A B a) := by
        rw [intervalIntegral.integral_const_mul, hAmpInt]
  have hendpoint (t : ℝ) (ht : 2 ≤ t) :
      ‖unequalQuadraticIntegralWeight A B t *
          standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ =
        ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B t := by
    rw [norm_mul, norm_standardAdditiveCharacter, mul_one]
    unfold unequalQuadraticIntegralWeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (unequalQuadraticIntegralAmplitude_nonneg hA hB ht)]
  calc
    ‖unequalQuadraticIntegralWeight A B b *
          standardAdditiveCharacter (reciprocalPhase A B 2 b) -
        unequalQuadraticIntegralWeight A B a *
          standardAdditiveCharacter (reciprocalPhase A B 2 a) -
        ∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
        ‖unequalQuadraticIntegralWeight A B b *
          standardAdditiveCharacter (reciprocalPhase A B 2 b)‖ +
        ‖unequalQuadraticIntegralWeight A B a *
          standardAdditiveCharacter (reciprocalPhase A B 2 a)‖ +
        ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B b +
        ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B a +
        ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B b -
            unequalQuadraticIntegralAmplitude A B a) := by
      rw [hendpoint b (ha.trans hab), hendpoint a ha]
      exact add_le_add le_rfl hintegralNorm
    _ = 2 * ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B b := by ring
    _ ≤ 3 * ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B b := by
      have hprod : 0 ≤ ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B b :=
        mul_nonneg (norm_nonneg _) hampb
      nlinarith

theorem norm_unequalQuadraticIntegralFactor :
    ‖unequalQuadraticIntegralFactor‖ = (2 * Real.pi)⁻¹ := by
  unfold unequalQuadraticIntegralFactor
  rw [norm_neg, div_eq_mul_inv, one_mul, norm_inv, norm_mul, norm_mul]
  simp only [norm_ofNat, norm_real, norm_I, mul_one]
  rw [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem unequalQuadraticIntegralAmplitude_le_dyadic
    {A B P b : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hP : 2 ≤ P) (hPb : P ≤ b) (hbP : b ≤ 2 * P) :
    unequalQuadraticIntegralAmplitude A B b ≤
      4 * P ^ 2 / (A * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hbpos : 0 < b := hPpos.trans_le hPb
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlogle : Real.log P ≤ Real.log b :=
    Real.log_le_log hPpos hPb
  have hlinLower : A * b ≤ A * b + 2 * B := by linarith
  have hdenLower : (A * b) * Real.log P ≤
      (A * b + 2 * B) * Real.log b := by
    calc
      (A * b) * Real.log P ≤ (A * b) * Real.log b :=
        mul_le_mul_of_nonneg_left hlogle (mul_nonneg hA.le hbpos.le)
      _ ≤ (A * b + 2 * B) * Real.log b :=
        mul_le_mul_of_nonneg_right hlinLower hlogb.le
  have hfirst : unequalQuadraticIntegralAmplitude A B b ≤
      b ^ 3 / ((A * b) * Real.log P) := by
    unfold unequalQuadraticIntegralAmplitude
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (mul_pos hA hbpos) hlogP) hdenLower
  have hbSq : b ^ 2 ≤ 4 * P ^ 2 := by nlinarith
  calc
    unequalQuadraticIntegralAmplitude A B b ≤
        b ^ 3 / ((A * b) * Real.log P) := hfirst
    _ = b ^ 2 / (A * Real.log P) := by field_simp
    _ ≤ 4 * P ^ 2 / (A * Real.log P) :=
      div_le_div_of_nonneg_right hbSq (mul_pos hA hlogP).le

theorem norm_unequalQuadraticIntervalIntegral_le_dyadic_of_pos_nonneg
    {A B P a b : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      6 * P ^ 2 / (A * Real.log P) := by
  have ha : 2 ≤ a := hP.trans hPa
  have hraw := norm_unequalQuadraticIntervalIntegral_le hA hB ha hab
  have hamp := unequalQuadraticIntegralAmplitude_le_dyadic
    hA hB hP (hPa.trans hab) hbP
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        3 * ‖unequalQuadraticIntegralFactor‖ *
          unequalQuadraticIntegralAmplitude A B b := hraw
    _ ≤ 3 * ‖unequalQuadraticIntegralFactor‖ *
          (4 * P ^ 2 / (A * Real.log P)) := by gcongr
    _ = 12 * P ^ 2 / ((2 * Real.pi) * (A * Real.log P)) := by
      rw [norm_unequalQuadraticIntegralFactor]
      field_simp
      ring
    _ ≤ 6 * P ^ 2 / (A * Real.log P) := by
      have hpi : 2 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hden : 0 < A * Real.log P := mul_pos hA hlogP
      rw [show 12 * P ^ 2 / ((2 * Real.pi) * (A * Real.log P)) =
          (12 * P ^ 2 / (2 * Real.pi)) / (A * Real.log P) by field_simp]
      apply (div_le_div_iff_of_pos_right hden).2
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [sq_nonneg P]

theorem norm_intervalIntegral_quadratic_eq_neg_coefficients
    (A B a b : ℝ) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ =
      ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase (-A) (-B) 2 t) /
          Real.log t‖ := by
  have hphase (t : ℝ) :
      reciprocalPhase A B 2 t =
        -reciprocalPhase (-A) (-B) 2 t := by
    unfold reciprocalPhase
    simp
    ring
  have hfun :
      (fun t : ℝ =>
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) =
      (fun t : ℝ => conj
        (standardAdditiveCharacter (reciprocalPhase (-A) (-B) 2 t) /
          Real.log t)) := by
    funext t
    rw [hphase, standardAdditiveCharacter_neg]
    simp
  rw [hfun]
  unfold intervalIntegral
  rw [integral_conj, integral_conj, ← map_sub]
  exact norm_conj _

theorem norm_unequalQuadraticIntervalIntegral_le_dyadic_of_neg_nonpos
    {A B P a b : ℝ} (hA : A < 0) (hB : B ≤ 0) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      6 * P ^ 2 / (|A| * Real.log P) := by
  rw [norm_intervalIntegral_quadratic_eq_neg_coefficients A B a b]
  have hraw := norm_unequalQuadraticIntervalIntegral_le_dyadic_of_pos_nonneg
    (A := -A) (B := -B) (by linarith) (by linarith) hP hPa hab hbP
  simpa [abs_of_neg hA] using hraw

theorem norm_fourierModeIntegral_Ico_le_dyadic_of_coeff_pos_nonneg
    {q : ℤ × ℤ} {N M P a b : ℝ}
    (hlinear : 0 < (q.1 : ℝ) * N) (hquadratic : 0 ≤ (q.2 : ℝ) * M)
    (hP : 2 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      6 * P ^ 2 / (((q.1 : ℝ) * N) * Real.log P) := by
  have hraw := norm_unequalQuadraticIntervalIntegral_le_dyadic_of_pos_nonneg
    hlinear hquadratic hP hPa hab hbP
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact hraw

theorem norm_fourierModeIntegral_Ico_le_dyadic_of_coeff_neg_nonpos
    {q : ℤ × ℤ} {N M P a b : ℝ}
    (hlinear : (q.1 : ℝ) * N < 0) (hquadratic : (q.2 : ℝ) * M ≤ 0)
    (hP : 2 ≤ P) (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      6 * P ^ 2 / (|(q.1 : ℝ) * N| * Real.log P) := by
  have hraw := norm_unequalQuadraticIntervalIntegral_le_dyadic_of_neg_nonpos
    hlinear hquadratic hP hPa hab hbP
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact hraw

/-- The unequal prime estimate and the nonstationary integral estimate in the
positive same-sign chamber, assembled for one literal Fourier mode. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_coeff_pos
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      0 < (q.1 : ℝ) * N → 0 < (q.2 : ℝ) * M →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
          (4 * (P : ℝ)) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          6 * (P : ℝ) ^ 2 /
            (((q.1 : ℝ) * N) * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M hPa hab hbP hlinear hquadratic hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic.ne' hlower hNupper hMupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_dyadic_of_coeff_pos_nonneg
      (q := q) (N := N) (M := M) (P := (P : ℝ))
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear hquadratic.le
      (by exact_mod_cast hP) (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_coeff_neg
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N < 0 → (q.2 : ℝ) * M < 0 →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
          (4 * (P : ℝ)) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          6 * (P : ℝ) ^ 2 /
            (|(q.1 : ℝ) * N| * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M hPa hab hbP hlinear hquadratic hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic.ne hlower hNupper hMupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_dyadic_of_coeff_neg_nonpos
      (q := q) (N := N) (M := M) (P := (P : ℝ))
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear hquadratic.le
      (by exact_mod_cast hP) (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

/-- Complete same-sign nonstationary chamber for a nonzero Fourier mode. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_sameSign
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      ((0 < (q.1 : ℝ) * N ∧ 0 < (q.2 : ℝ) * M) ∨
        ((q.1 : ℝ) * N < 0 ∧ (q.2 : ℝ) * M < 0)) →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
          (4 * (P : ℝ)) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-S) +
          6 * (P : ℝ) ^ 2 /
            (|(q.1 : ℝ) * N| * Real.log P) := by
  have hpos :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_coeff_pos
      hVinogradov hA₀ hε haexp hS
  have hneg :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_coeff_neg
      hVinogradov hA₀ hε haexp hS
  filter_upwards [hpos, hneg] with P hposP hnegP
  intro a b q N M hPa hab hbP hsign hlower hNupper hMupper
  rcases hsign with hsign | hsign
  · simpa [abs_of_pos hsign.1] using
      hposP a b q N M hPa hab hbP hsign.1 hsign.2
        hlower hNupper hMupper
  · exact hnegP a b q N M hPa hab hbP hsign.1 hsign.2
      hlower hNupper hMupper

end
end Tao2026
