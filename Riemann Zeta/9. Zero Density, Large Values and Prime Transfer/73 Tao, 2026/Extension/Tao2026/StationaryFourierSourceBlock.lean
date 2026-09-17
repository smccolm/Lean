import Tao2026.UnequalFourierSourceBlock

/-!
# Opposite-sign Fourier stationary geometry

This module isolates the unique critical point of the unequal quadratic
reciprocal phase and begins the quantitative near/far split needed for the
opposite-sign Fourier chamber.
-/

open Complex Filter MeasureTheory Set
open scoped Interval ComplexConjugate

namespace Tao2026

noncomputable section

def quadraticReciprocalStationaryPoint (A B : ℝ) : ℝ :=
  -2 * B / A

theorem quadraticReciprocalStationaryPoint_spec
    {A B : ℝ} (hA : A ≠ 0) :
    A * quadraticReciprocalStationaryPoint A B + 2 * B = 0 := by
  unfold quadraticReciprocalStationaryPoint
  field_simp
  ring

/-- With the two source parameters equal, a nonzero Fourier mode's stationary
point depends only on the integer frequency ratio. -/
theorem quadraticReciprocalStationaryPoint_same_parameter
    (q : ℤ × ℤ) {N : ℝ} (hq₁ : q.1 ≠ 0) (hN : N ≠ 0) :
    quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) =
      -2 * (q.2 : ℝ) / (q.1 : ℝ) := by
  unfold quadraticReciprocalStationaryPoint
  have hq₁' : (q.1 : ℝ) ≠ 0 := by exact_mod_cast hq₁
  field_simp [hq₁', hN]

/-- A stationary point belonging to a frequency box of radius `R` is at most
`2R` when the two source parameters agree. -/
theorem quadraticReciprocalStationaryPoint_same_parameter_le_two_mul
    {q : ℤ × ℤ} {N R : ℝ} (hq₁ : q.1 ≠ 0) (hN : N ≠ 0)
    (hq₂ : |(q.2 : ℝ)| ≤ R) :
    quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * N) ≤ 2 * R := by
  rw [quadraticReciprocalStationaryPoint_same_parameter q hq₁ hN]
  have hq₁abs : 1 ≤ |(q.1 : ℝ)| := by
    exact_mod_cast Int.one_le_abs hq₁
  calc
    -2 * (q.2 : ℝ) / (q.1 : ℝ) ≤
        |-2 * (q.2 : ℝ) / (q.1 : ℝ)| := le_abs_self _
    _ = 2 * |(q.2 : ℝ)| / |(q.1 : ℝ)| := by
      rw [abs_div, abs_mul]
      norm_num
    _ ≤ 2 * |(q.2 : ℝ)| := by
      exact div_le_self (by positivity) hq₁abs
    _ ≤ 2 * R := by gcongr

theorem quadraticReciprocalLinearFactor_eq
    {A B : ℝ} (hA : A ≠ 0) (t : ℝ) :
    A * t + 2 * B =
      A * (t - quadraticReciprocalStationaryPoint A B) := by
  rw [mul_sub]
  have hspec := quadraticReciprocalStationaryPoint_spec (B := B) hA
  linarith

theorem abs_quadraticReciprocalLinearFactor_eq
    {A B : ℝ} (hA : A ≠ 0) (t : ℝ) :
    |A * t + 2 * B| =
      |A| * |t - quadraticReciprocalStationaryPoint A B| := by
  rw [quadraticReciprocalLinearFactor_eq hA, abs_mul]

theorem quadraticReciprocalSecondLinearFactor_eq
    {A B : ℝ} (hA : A ≠ 0) (t : ℝ) :
    2 * A * t + 6 * B =
      A * (2 * t - 3 * quadraticReciprocalStationaryPoint A B) := by
  have hspec := quadraticReciprocalStationaryPoint_spec (B := B) hA
  nlinarith

theorem unequalQuadraticIntegralAmplitudeDeriv_nonpos_left_of_stationaryPoint
    {A B t : ℝ} (hA : 0 < A) (ht : 2 ≤ t)
    (hts : t ≤ quadraticReciprocalStationaryPoint A B) :
    unequalQuadraticIntegralAmplitudeDeriv A B t ≤ 0 := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hs : 0 ≤ s := by linarith
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hlogTwo.trans (Real.log_le_log (by norm_num) ht)
  have hcoef : 2 * t - 3 * s ≤ 0 := by linarith
  have hmul : (2 * t - 3 * s) * Real.log t ≤
      (2 * t - 3 * s) * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonpos_left hlogHalf hcoef
  have hcore :
      (2 * t - 3 * s) * Real.log t - (t - s) ≤ 0 := by
    nlinarith
  have hbracket :
      (2 * A * t + 6 * B) * Real.log t - (A * t + 2 * B) ≤ 0 := by
    rw [quadraticReciprocalSecondLinearFactor_eq hA0,
      quadraticReciprocalLinearFactor_eq hA0]
    nlinarith
  unfold unequalQuadraticIntegralAmplitudeDeriv
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hbracket) (sq_nonneg _)

theorem unequalQuadraticIntegralAmplitudeDeriv_nonpos_right_near_stationaryPoint
    {A B t : ℝ} (hA : 0 < A) (ht : 2 ≤ t)
    (hst : quadraticReciprocalStationaryPoint A B ≤ t)
    (hts : t ≤ 3 * quadraticReciprocalStationaryPoint A B / 2) :
    unequalQuadraticIntegralAmplitudeDeriv A B t ≤ 0 := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hcoef : 2 * t - 3 * s ≤ 0 := by linarith
  have hcore :
      (2 * t - 3 * s) * Real.log t - (t - s) ≤ 0 := by
    have hfirst : (2 * t - 3 * s) * Real.log t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hlog
    linarith
  have hbracket :
      (2 * A * t + 6 * B) * Real.log t - (A * t + 2 * B) ≤ 0 := by
    rw [quadraticReciprocalSecondLinearFactor_eq hA0,
      quadraticReciprocalLinearFactor_eq hA0]
    nlinarith
  unfold unequalQuadraticIntegralAmplitudeDeriv
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hbracket) (sq_nonneg _)

theorem intervalIntegrable_unequalQuadraticIntegralAmplitudeDeriv_of_linear_ne
    {A B a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0) :
    IntervalIntegrable (unequalQuadraticIntegralAmplitudeDeriv A B)
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

/-- A nonpositive integration-by-parts amplitude derivative gives a
two-endpoint first-derivative-test bound. -/
theorem norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonpos
    {A B a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0)
    (hderiv : ∀ t ∈ Set.Icc a b,
      unequalQuadraticIntegralAmplitudeDeriv A B t ≤ 0) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      2 * ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b|) := by
  have hlinU : ∀ t ∈ Set.uIcc a b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hlin t ht
  rw [unequalQuadraticIntervalIntegral_eq_parts_of_linear_ne ha hab hlinU]
  have hAmpInt :=
    intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub_of_linear_ne
      ha hab hlin
  have hderivInt :=
    intervalIntegrable_unequalQuadraticIntegralAmplitudeDeriv_of_linear_ne
      ha hab hlin
  have hgint : IntervalIntegrable
      (fun t => ‖unequalQuadraticIntegralFactor‖ *
        (-unequalQuadraticIntegralAmplitudeDeriv A B t)) volume a b :=
    hderivInt.neg.const_mul _
  have hintegralNorm :
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
        ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B a -
            unequalQuadraticIntegralAmplitude A B b) := by
    calc
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
          ∫ t in a..b, ‖unequalQuadraticIntegralFactor‖ *
            (-unequalQuadraticIntegralAmplitudeDeriv A B t) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hgint
        filter_upwards with t ht
        have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
        rw [norm_mul, norm_mul, norm_standardAdditiveCharacter, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (hderiv t htIcc)]
      _ = ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B a -
            unequalQuadraticIntegralAmplitude A B b) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_neg, hAmpInt]
        ring
  have hendpoint (t : ℝ) :
      ‖unequalQuadraticIntegralWeight A B t *
          standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ =
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B t| := by
    rw [norm_mul, norm_standardAdditiveCharacter, mul_one]
    unfold unequalQuadraticIntegralWeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hvariation :
      unequalQuadraticIntegralAmplitude A B a -
          unequalQuadraticIntegralAmplitude A B b ≤
        |unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b| := by
    nlinarith [le_abs_self (unequalQuadraticIntegralAmplitude A B a),
      neg_le_abs (unequalQuadraticIntegralAmplitude A B b)]
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
          |unequalQuadraticIntegralAmplitude A B b| +
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B a| +
        ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B a -
            unequalQuadraticIntegralAmplitude A B b) := by
      rw [hendpoint b, hendpoint a]
      exact add_le_add le_rfl hintegralNorm
    _ ≤ 2 * ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b|) := by
      have hfactor : 0 ≤ ‖unequalQuadraticIntegralFactor‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hvariation hfactor]

/-- A nonnegative integration-by-parts amplitude derivative gives the same
two-endpoint bounded-variation estimate. -/
theorem norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonneg
    {A B a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0)
    (hderiv : ∀ t ∈ Set.Icc a b,
      0 ≤ unequalQuadraticIntegralAmplitudeDeriv A B t) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      2 * ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b|) := by
  have hlinU : ∀ t ∈ Set.uIcc a b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hlin t ht
  rw [unequalQuadraticIntervalIntegral_eq_parts_of_linear_ne ha hab hlinU]
  have hAmpInt :=
    intervalIntegral_unequalQuadraticIntegralAmplitudeDeriv_eq_sub_of_linear_ne
      ha hab hlin
  have hderivInt :=
    intervalIntegrable_unequalQuadraticIntegralAmplitudeDeriv_of_linear_ne
      ha hab hlin
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
        have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
        rw [norm_mul, norm_mul, norm_standardAdditiveCharacter, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hderiv t htIcc)]
      _ = ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B b -
            unequalQuadraticIntegralAmplitude A B a) := by
        rw [intervalIntegral.integral_const_mul, hAmpInt]
  have hendpoint (t : ℝ) :
      ‖unequalQuadraticIntegralWeight A B t *
          standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ =
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B t| := by
    rw [norm_mul, norm_standardAdditiveCharacter, mul_one]
    unfold unequalQuadraticIntegralWeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hvariation :
      unequalQuadraticIntegralAmplitude A B b -
          unequalQuadraticIntegralAmplitude A B a ≤
        |unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b| := by
    nlinarith [le_abs_self (unequalQuadraticIntegralAmplitude A B b),
      neg_le_abs (unequalQuadraticIntegralAmplitude A B a)]
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
          |unequalQuadraticIntegralAmplitude A B b| +
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B a| +
        ‖unequalQuadraticIntegralFactor‖ *
          (unequalQuadraticIntegralAmplitude A B b -
            unequalQuadraticIntegralAmplitude A B a) := by
      rw [hendpoint b, hendpoint a]
      exact add_le_add le_rfl hintegralNorm
    _ ≤ 2 * ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b|) := by
      have hfactor : 0 ≤ ‖unequalQuadraticIntegralFactor‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hvariation hfactor]

theorem norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_abs_le
    {A B a b D : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0)
    (hderiv : ∀ t ∈ Set.Icc a b,
      |unequalQuadraticIntegralAmplitudeDeriv A B t| ≤ D) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b| + (b - a) * D) := by
  have hlinU : ∀ t ∈ Set.uIcc a b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hlin t ht
  rw [unequalQuadraticIntervalIntegral_eq_parts_of_linear_ne ha hab hlinU]
  have hintegralNorm :
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
        ‖unequalQuadraticIntegralFactor‖ * D * (b - a) := by
    calc
      ‖∫ t in a..b,
          (unequalQuadraticIntegralFactor *
              unequalQuadraticIntegralAmplitudeDeriv A B t) *
            standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ ≤
          (‖unequalQuadraticIntegralFactor‖ * D) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le hab] at ht
        have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
        rw [norm_mul, norm_mul, norm_standardAdditiveCharacter, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hderiv t htIcc) (norm_nonneg _)
      _ = ‖unequalQuadraticIntegralFactor‖ * D * (b - a) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  have hendpoint (t : ℝ) :
      ‖unequalQuadraticIntegralWeight A B t *
          standardAdditiveCharacter (reciprocalPhase A B 2 t)‖ =
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B t| := by
    rw [norm_mul, norm_standardAdditiveCharacter, mul_one]
    unfold unequalQuadraticIntegralWeight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
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
          |unequalQuadraticIntegralAmplitude A B b| +
        ‖unequalQuadraticIntegralFactor‖ *
          |unequalQuadraticIntegralAmplitude A B a| +
        ‖unequalQuadraticIntegralFactor‖ * D * (b - a) := by
      rw [hendpoint b, hendpoint a]
      exact add_le_add le_rfl hintegralNorm
    _ = ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B a| +
          |unequalQuadraticIntegralAmplitude A B b| + (b - a) * D) := by
      ring

theorem quadraticReciprocalLinearFactor_eq_zero_iff
    {A B t : ℝ} (hA : A ≠ 0) :
    A * t + 2 * B = 0 ↔
      t = quadraticReciprocalStationaryPoint A B := by
  rw [quadraticReciprocalLinearFactor_eq hA, mul_eq_zero,
    or_iff_right hA, sub_eq_zero]

theorem quadraticReciprocalPhase_deriv_eq_zero_iff
    {A B t : ℝ} (hA : A ≠ 0) (ht : t ≠ 0) :
    -(A * t + 2 * B) / t ^ 3 = 0 ↔
      t = quadraticReciprocalStationaryPoint A B := by
  rw [div_eq_zero_iff, neg_eq_zero, quadraticReciprocalLinearFactor_eq_zero_iff hA]
  simp [ht]

theorem abs_quadraticReciprocalPhase_deriv_eq
    {A B t : ℝ} (hA : A ≠ 0) (ht : 0 < t) :
    |-(A * t + 2 * B) / t ^ 3| =
      |A| * |t - quadraticReciprocalStationaryPoint A B| / t ^ 3 := by
  rw [abs_div, abs_neg, abs_pow, abs_of_pos ht,
    abs_quadraticReciprocalLinearFactor_eq hA]

theorem abs_quadraticReciprocalPhase_deriv_lower_of_dyadic_far
    {A B P t δ : ℝ} (hA : A ≠ 0) (hP : 0 < P)
    (hPt : P ≤ t) (htP : t ≤ 2 * P) (hδ : 0 ≤ δ)
    (hfar : δ ≤ |t - quadraticReciprocalStationaryPoint A B|) :
    |A| * δ / (8 * P ^ 3) ≤ |-(A * t + 2 * B) / t ^ 3| := by
  have ht : 0 < t := hP.trans_le hPt
  rw [abs_quadraticReciprocalPhase_deriv_eq hA ht]
  have htCube : t ^ 3 ≤ 8 * P ^ 3 := by
    calc
      t ^ 3 ≤ (2 * P) ^ 3 := pow_le_pow_left₀ ht.le htP 3
      _ = 8 * P ^ 3 := by ring
  have hnum : |A| * δ ≤
      |A| * |t - quadraticReciprocalStationaryPoint A B| :=
    mul_le_mul_of_nonneg_left hfar (abs_nonneg A)
  calc
    |A| * δ / (8 * P ^ 3) ≤ |A| * δ / t ^ 3 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (abs_nonneg A) hδ) (pow_pos ht 3) htCube
    _ ≤ |A| * |t - quadraticReciprocalStationaryPoint A B| / t ^ 3 :=
      div_le_div_of_nonneg_right hnum (pow_pos ht 3).le

theorem abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    {A B P t δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hPt : P ≤ t) (htP : t ≤ 2 * P) (hδ : 0 < δ)
    (hfar : δ ≤ |t - quadraticReciprocalStationaryPoint A B|) :
    |unequalQuadraticIntegralAmplitude A B t| ≤
      8 * P ^ 3 / (A * δ * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have ht : 0 < t := hPpos.trans_le hPt
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t :=
    hlogP.trans_le (Real.log_le_log hPpos hPt)
  have htCube : t ^ 3 ≤ 8 * P ^ 3 := by
    calc
      t ^ 3 ≤ (2 * P) ^ 3 := pow_le_pow_left₀ ht.le htP 3
      _ = 8 * P ^ 3 := by ring
  have hdenLower : A * δ * Real.log P ≤
      (A * |t - quadraticReciprocalStationaryPoint A B|) * Real.log t := by
    calc
      A * δ * Real.log P ≤
          A * |t - quadraticReciprocalStationaryPoint A B| * Real.log P := by
        gcongr
      _ ≤ (A * |t - quadraticReciprocalStationaryPoint A B|) *
          Real.log t := by
        gcongr
  unfold unequalQuadraticIntegralAmplitude
  rw [abs_div, abs_pow, abs_of_pos ht, abs_mul,
    abs_quadraticReciprocalLinearFactor_eq hA.ne', abs_of_pos hA,
    abs_of_pos hlogt]
  exact div_le_div₀ (by positivity) htCube
    (mul_pos (mul_pos hA hδ) hlogP) hdenLower

theorem norm_quadraticIntervalIntegral_left_of_stationaryPoint_le
    {A B P a δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P) (hPa : P ≤ a)
    (hδ : 0 < δ)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - δ)
    (hstationaryUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    ‖∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      32 * P ^ 3 / (A * δ * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hcP : s - δ ≤ 2 * P := by linarith
  have hlin : ∀ t ∈ Set.Icc a (s - δ), A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [quadraticReciprocalLinearFactor_eq hA0]
    exact mul_ne_zero hA0 (sub_ne_zero.mpr (ne_of_lt (by linarith [ht.2])))
  have hderiv : ∀ t ∈ Set.Icc a (s - δ),
      unequalQuadraticIntegralAmplitudeDeriv A B t ≤ 0 := by
    intro t ht
    apply unequalQuadraticIntegralAmplitudeDeriv_nonpos_left_of_stationaryPoint
      hA (hP.trans (hPa.trans ht.1))
    dsimp only [s] at ht ⊢
    linarith [ht.2]
  have hraw := norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonpos
    (A := A) (B := B) (a := a) (b := s - δ)
    (hP.trans hPa) hleft hlin hderiv
  have hfarA : δ ≤ |a - s| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hfarC : δ ≤ |(s - δ) - s| := by
    rw [show (s - δ) - s = -δ by ring, abs_neg, abs_of_pos hδ]
  have hampA := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPa (hleft.trans hcP) hδ hfarA
  have hPleft : P ≤ s - δ := hPa.trans hleft
  have hampC := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPleft hcP hδ hfarC
  have hfactor : ‖unequalQuadraticIntegralFactor‖ ≤ 1 := by
    rw [norm_unequalQuadraticIntegralFactor]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  calc
    ‖∫ t in a..(s - δ),
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        2 * ‖unequalQuadraticIntegralFactor‖ *
          (|unequalQuadraticIntegralAmplitude A B a| +
            |unequalQuadraticIntegralAmplitude A B (s - δ)|) := hraw
    _ ≤ 2 * 1 *
          (8 * P ^ 3 / (A * δ * Real.log P) +
            8 * P ^ 3 / (A * δ * Real.log P)) := by gcongr
    _ = 32 * P ^ 3 / (A * δ * Real.log P) := by ring

theorem norm_quadraticIntervalIntegral_right_near_stationaryPoint_le
    {A B P b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hPleft : P ≤ quadraticReciprocalStationaryPoint A B + δ)
    (hδ : 0 < δ)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b)
    (hbturn : b ≤ 3 * quadraticReciprocalStationaryPoint A B / 2)
    (hbP : b ≤ 2 * P) :
    ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      32 * P ^ 3 / (A * δ * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hlin : ∀ t ∈ Set.Icc (s + δ) b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [quadraticReciprocalLinearFactor_eq hA0]
    exact mul_ne_zero hA0 (sub_ne_zero.mpr (ne_of_gt (by linarith [ht.1])))
  have hderiv : ∀ t ∈ Set.Icc (s + δ) b,
      unequalQuadraticIntegralAmplitudeDeriv A B t ≤ 0 := by
    intro t ht
    apply
      unequalQuadraticIntegralAmplitudeDeriv_nonpos_right_near_stationaryPoint
        hA (hP.trans (hPleft.trans ht.1))
    · dsimp only [s] at ht ⊢
      linarith [ht.1]
    · exact ht.2.trans hbturn
  have hraw := norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonpos
    (A := A) (B := B) (a := s + δ) (b := b)
    (hP.trans hPleft) hright hlin hderiv
  have hfarLeft : δ ≤ |(s + δ) - s| := by
    rw [show (s + δ) - s = δ by ring, abs_of_pos hδ]
  have hfarB : δ ≤ |b - s| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hampLeft := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPleft (hright.trans hbP) hδ hfarLeft
  have hPb : P ≤ b := hPleft.trans hright
  have hampB := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPb hbP hδ hfarB
  have hfactor : ‖unequalQuadraticIntegralFactor‖ ≤ 1 := by
    rw [norm_unequalQuadraticIntegralFactor]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  calc
    ‖∫ t in (s + δ)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        2 * ‖unequalQuadraticIntegralFactor‖ *
          (|unequalQuadraticIntegralAmplitude A B (s + δ)| +
            |unequalQuadraticIntegralAmplitude A B b|) := hraw
    _ ≤ 2 * 1 *
          (8 * P ^ 3 / (A * δ * Real.log P) +
            8 * P ^ 3 / (A * δ * Real.log P)) := by gcongr
    _ = 32 * P ^ 3 / (A * δ * Real.log P) := by ring

/-- Beyond the amplitude turning point, the integration-by-parts amplitude
derivative has a uniform dyadic bound. -/
theorem abs_unequalQuadraticIntegralAmplitudeDeriv_le_right_turning
    {A B P t : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (htLower : 3 * quadraticReciprocalStationaryPoint A B / 2 ≤ t)
    (htUpper : t ≤ 2 * P) :
    |unequalQuadraticIntegralAmplitudeDeriv A B t| ≤
      64 * P / (A * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hPpos : 0 < P := by linarith
  have hspos : 0 < s := hPpos.trans_le hsLower
  have htpos : 0 < t := by linarith
  have hgapLower : P / 2 ≤ t - s := by linarith
  have hgapPos : 0 < t - s := by linarith
  have hgapUpper : t - s ≤ P := by linarith
  have hturnNonneg : 0 ≤ 2 * t - 3 * s := by linarith
  have hturnUpper : 2 * t - 3 * s ≤ P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have htwoPpos : 0 < 2 * P := by positivity
  have hlogUpper : Real.log t ≤ 2 * Real.log P := by
    calc
      Real.log t ≤ Real.log (2 * P) := Real.log_le_log htpos htUpper
      _ ≤ Real.log (P ^ 2) := by
        apply Real.log_le_log htwoPpos
        nlinarith
      _ = 2 * Real.log P := by rw [Real.log_pow]; norm_num
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log P := by
    have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hlogTwo.trans (Real.log_le_log (by norm_num) hP)
  have hturnLog :
      (2 * t - 3 * s) * Real.log t ≤ 2 * P * Real.log P := by
    calc
      (2 * t - 3 * s) * Real.log t ≤ P * (2 * Real.log P) := by
        gcongr
      _ = 2 * P * Real.log P := by ring
  have hgapLog : t - s ≤ 2 * P * Real.log P := by
    calc
      t - s ≤ P := hgapUpper
      _ ≤ 2 * P * Real.log P := by nlinarith
  have hcoreAbs :
      |(2 * t - 3 * s) * Real.log t - (t - s)| ≤
        4 * P * Real.log P := by
    calc
      |(2 * t - 3 * s) * Real.log t - (t - s)| ≤
          |(2 * t - 3 * s) * Real.log t| + |t - s| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le ((2 * t - 3 * s) * Real.log t) (-(t - s)))
      _ = (2 * t - 3 * s) * Real.log t + (t - s) := by
        rw [abs_of_nonneg (mul_nonneg hturnNonneg hlogt.le),
          abs_of_pos hgapPos]
      _ ≤ 4 * P * Real.log P := by nlinarith
  have htSq : t ^ 2 ≤ 4 * P ^ 2 := by nlinarith [sq_nonneg (2 * P - t)]
  have hnum :
      t ^ 2 * A * |(2 * t - 3 * s) * Real.log t - (t - s)| ≤
        16 * A * P ^ 3 * Real.log P := by
    calc
      t ^ 2 * A * |(2 * t - 3 * s) * Real.log t - (t - s)| ≤
          (4 * P ^ 2) * A * (4 * P * Real.log P) := by gcongr
      _ = 16 * A * P ^ 3 * Real.log P := by ring
  have hden :
      A ^ 2 * (P / 2) ^ 2 * (Real.log P) ^ 2 ≤
        (A * (t - s) * Real.log t) ^ 2 := by
    have hlogMono : Real.log P ≤ Real.log t :=
      Real.log_le_log hPpos (by linarith)
    have hbaseNonneg : 0 ≤ A * (P / 2) * Real.log P := by positivity
    have hbaseLe : A * (P / 2) * Real.log P ≤
        A * (t - s) * Real.log t := by gcongr
    nlinarith [mul_self_le_mul_self hbaseNonneg hbaseLe]
  have hformula :
      |unequalQuadraticIntegralAmplitudeDeriv A B t| =
        t ^ 2 * A * |(2 * t - 3 * s) * Real.log t - (t - s)| /
          (A * (t - s) * Real.log t) ^ 2 := by
    have hgapActual : 0 < t - quadraticReciprocalStationaryPoint A B := hgapPos
    unfold unequalQuadraticIntegralAmplitudeDeriv
    rw [quadraticReciprocalSecondLinearFactor_eq hA0,
      quadraticReciprocalLinearFactor_eq hA0]
    rw [show A * (2 * t - 3 * s) * Real.log t - A * (t - s) =
        A * ((2 * t - 3 * s) * Real.log t - (t - s)) by ring]
    simp only [abs_div, abs_mul, abs_pow, abs_of_pos htpos,
      abs_of_pos hA, abs_of_pos hgapActual, abs_of_pos hlogt]
    ring
  rw [hformula]
  have hdenPos : 0 < A ^ 2 * (P / 2) ^ 2 * (Real.log P) ^ 2 := by positivity
  calc
    t ^ 2 * A * |(2 * t - 3 * s) * Real.log t - (t - s)| /
        (A * (t - s) * Real.log t) ^ 2 ≤
      (16 * A * P ^ 3 * Real.log P) /
        (A ^ 2 * (P / 2) ^ 2 * (Real.log P) ^ 2) := by
      exact div_le_div₀ (by positivity) hnum hdenPos hden
    _ = 64 * P / (A * Real.log P) := by
      field_simp
      ring

theorem norm_quadraticIntervalIntegral_right_tail_le
    {A B P b : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hstart : 3 * quadraticReciprocalStationaryPoint A B / 2 ≤ b)
    (hbP : b ≤ 2 * P) :
    ‖∫ t in (3 * quadraticReciprocalStationaryPoint A B / 2)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      160 * P ^ 2 / (A * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hspos : 0 < s := hPpos.trans_le hsLower
  have hstartP : P ≤ 3 * s / 2 := by linarith
  have hlin : ∀ t ∈ Set.Icc (3 * s / 2) b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [quadraticReciprocalLinearFactor_eq hA0]
    exact mul_ne_zero hA0 (sub_ne_zero.mpr (ne_of_gt (by linarith [ht.1])))
  have hderiv : ∀ t ∈ Set.Icc (3 * s / 2) b,
      |unequalQuadraticIntegralAmplitudeDeriv A B t| ≤
        64 * P / (A * Real.log P) := by
    intro t ht
    apply abs_unequalQuadraticIntegralAmplitudeDeriv_le_right_turning
      hA hP hsLower
    · dsimp only [s] at ht ⊢
      exact ht.1
    · exact ht.2.trans hbP
  have hraw := norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_abs_le
    (A := A) (B := B) (a := 3 * s / 2) (b := b)
    (hP.trans hstartP) hstart hlin hderiv
  have hδ : 0 < P / 2 := by positivity
  have hfarStart : P / 2 ≤ |(3 * s / 2) - s| := by
    rw [show (3 * s / 2) - s = s / 2 by ring, abs_of_pos (by positivity)]
    linarith
  have hfarB : P / 2 ≤ |b - s| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hampStart := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hstartP (hstart.trans hbP) hδ hfarStart
  have hPb : P ≤ b := hstartP.trans hstart
  have hampB := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPb hbP hδ hfarB
  have hfactor : ‖unequalQuadraticIntegralFactor‖ ≤ 1 := by
    rw [norm_unequalQuadraticIntegralFactor]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  have hlength : b - 3 * s / 2 ≤ 2 * P := by linarith
  have hDnonneg : 0 ≤ 64 * P / (A * Real.log P) := by positivity
  calc
    ‖∫ t in (3 * s / 2)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      ‖unequalQuadraticIntegralFactor‖ *
        (|unequalQuadraticIntegralAmplitude A B (3 * s / 2)| +
          |unequalQuadraticIntegralAmplitude A B b| +
            (b - 3 * s / 2) * (64 * P / (A * Real.log P))) := hraw
    _ ≤ 1 *
        (8 * P ^ 3 / (A * (P / 2) * Real.log P) +
          8 * P ^ 3 / (A * (P / 2) * Real.log P) +
            (2 * P) * (64 * P / (A * Real.log P))) := by
      gcongr
    _ = 160 * P ^ 2 / (A * Real.log P) := by
      field_simp
      ring

theorem quadraticReciprocalStationaryPoint_pos_of_pos_neg
    {A B : ℝ} (hA : 0 < A) (hB : B < 0) :
    0 < quadraticReciprocalStationaryPoint A B := by
  unfold quadraticReciprocalStationaryPoint
  exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hB) hA

theorem quadraticReciprocalStationaryPoint_pos_of_neg_pos
    {A B : ℝ} (hA : A < 0) (hB : 0 < B) :
    0 < quadraticReciprocalStationaryPoint A B := by
  unfold quadraticReciprocalStationaryPoint
  exact div_pos_of_neg_of_neg (by linarith) hA

theorem abs_quadraticCoefficient_eq_abs_linear_mul_stationaryPoint_div_two
    {A B : ℝ} (hA : A ≠ 0) :
    |B| = |A| * |quadraticReciprocalStationaryPoint A B| / 2 := by
  have hspec := quadraticReciprocalStationaryPoint_spec (B := B) hA
  have hB : B = -(A * quadraticReciprocalStationaryPoint A B) / 2 := by
    linarith
  calc
    |B| = |-(A * quadraticReciprocalStationaryPoint A B) / 2| :=
      congrArg abs hB
    _ = |A| * |quadraticReciprocalStationaryPoint A B| / 2 := by
      rw [abs_div, abs_neg, abs_mul]
      norm_num

theorem abs_quadraticCoefficient_le_abs_linear_mul_scale_of_stationaryPoint
    {A B P : ℝ} (hA : A ≠ 0) (hstationaryNonneg :
      0 ≤ quadraticReciprocalStationaryPoint A B)
    (hstationaryUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    |B| ≤ |A| * P := by
  rw [abs_quadraticCoefficient_eq_abs_linear_mul_stationaryPoint_div_two hA,
    abs_of_nonneg hstationaryNonneg]
  have hAabs : 0 ≤ |A| := abs_nonneg A
  nlinarith

theorem reciprocalPhaseScale_le_five_mul_abs_linear_div_sixteen
    {A B P : ℝ} (hA : A ≠ 0) (hP : 0 < P)
    (hstationaryNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hstationaryUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    reciprocalPhaseScale A B 2 (4 * P) ≤
      5 * |A| / (16 * P) := by
  have hB :=
    abs_quadraticCoefficient_le_abs_linear_mul_scale_of_stationaryPoint
      hA hstationaryNonneg hstationaryUpper
  unfold reciprocalPhaseScale
  norm_num [mul_pow]
  have hP2 : 0 < P ^ 2 := sq_pos_of_pos hP
  have hterm : |B| / (16 * P ^ 2) ≤ (|A| * P) / (16 * P ^ 2) :=
    div_le_div_of_nonneg_right hB (by positivity)
  calc
    |A| / (4 * P) + |B| / (16 * P ^ 2) ≤
        |A| / (4 * P) + (|A| * P) / (16 * P ^ 2) :=
      add_le_add le_rfl hterm
    _ = 5 * |A| / (16 * P) := by field_simp; ring

theorem abs_linear_lower_of_phaseScale_lower_of_stationaryPoint
    {A B P L : ℝ} (hA : A ≠ 0) (hP : 0 < P)
    (hstationaryNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hstationaryUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hL : L ≤ reciprocalPhaseScale A B 2 (4 * P)) :
    (16 / 5) * P * L ≤ |A| := by
  have hupper := reciprocalPhaseScale_le_five_mul_abs_linear_div_sixteen
    hA hP hstationaryNonneg hstationaryUpper
  have hLP : L ≤ 5 * |A| / (16 * P) := hL.trans hupper
  have hden : 0 < 16 * P := by positivity
  have hmul : L * (16 * P) ≤ 5 * |A| :=
    (le_div_iff₀ hden).mp hLP
  nlinarith

/-- Away from the unique stationary point, the source phase-scale lower bound
becomes a quantitative first-derivative lower bound on the dyadic interval. -/
theorem abs_quadraticReciprocalPhase_deriv_lower_of_sourceScale_far
    {A B P t δ L : ℝ} (hA : A ≠ 0) (hP : 0 < P)
    (hstationaryNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hstationaryUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hL : L ≤ reciprocalPhaseScale A B 2 (4 * P))
    (hPt : P ≤ t) (htP : t ≤ 2 * P) (hδ : 0 ≤ δ)
    (hfar : δ ≤ |t - quadraticReciprocalStationaryPoint A B|) :
    (2 / 5) * L * δ / P ^ 2 ≤
      |-(A * t + 2 * B) / t ^ 3| := by
  have hAlower :=
    abs_linear_lower_of_phaseScale_lower_of_stationaryPoint
      hA hP hstationaryNonneg hstationaryUpper hL
  have hmul : (16 / 5) * P * L * δ ≤ |A| * δ := by
    exact mul_le_mul_of_nonneg_right hAlower hδ
  have hden : 0 ≤ 8 * P ^ 3 := by positivity
  calc
    (2 / 5) * L * δ / P ^ 2 =
        ((16 / 5) * P * L * δ) / (8 * P ^ 3) := by
      field_simp
      ring
    _ ≤ |A| * δ / (8 * P ^ 3) :=
      div_le_div_of_nonneg_right hmul hden
    _ ≤ |-(A * t + 2 * B) / t ^ 3| :=
      abs_quadraticReciprocalPhase_deriv_lower_of_dyadic_far
        hA hP hPt htP hδ hfar

/-- On any subinterval of `[P,2P]`, the logarithmic phase integral is bounded
by interval length divided by `log P`, without using oscillation. -/
theorem norm_quadraticIntervalIntegral_le_length_div_log
    (A B : ℝ) {P c d : ℝ} (hP : 2 ≤ P)
    (hPc : P ≤ c) (hcd : c ≤ d) :
    ‖∫ t in c..d,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      (d - c) / Real.log P := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  calc
    ‖∫ t in c..d,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        (Real.log P)⁻¹ * |d - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hcd] at ht
      have hPt : P ≤ t := hPc.trans ht.1.le
      have htpos : 0 < t := hPpos.trans_le hPt
      have hlogle : Real.log P ≤ Real.log t :=
        Real.log_le_log hPpos hPt
      have hlogt : 0 < Real.log t := hlogP.trans_le hlogle
      rw [norm_div, norm_standardAdditiveCharacter, one_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
      exact inv_anti₀ hlogP hlogle
    _ = (d - c) / Real.log P := by
      rw [abs_of_nonneg (sub_nonneg.mpr hcd)]
      ring

/-- The contribution of an interval contained in a radius-`δ` neighborhood
of the stationary point is controlled solely by its length. -/
theorem norm_quadraticIntervalIntegral_le_two_mul_radius_div_log
    (A B : ℝ) {P c d δ : ℝ} (hP : 2 ≤ P) (hPc : P ≤ c)
    (hcd : c ≤ d)
    (hc : quadraticReciprocalStationaryPoint A B - δ ≤ c)
    (hd : d ≤ quadraticReciprocalStationaryPoint A B + δ) :
    ‖∫ t in c..d,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      2 * δ / Real.log P := by
  have hraw := norm_quadraticIntervalIntegral_le_length_div_log
    A B hP hPc hcd
  have hlen : d - c ≤ 2 * δ := by linarith
  have hlogP : 0 ≤ Real.log P := (Real.log_pos (by linarith)).le
  exact hraw.trans (div_le_div_of_nonneg_right hlen hlogP)

theorem intervalIntegrable_quadraticLogIntegrand
    (A B : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t => standardAdditiveCharacter (reciprocalPhase A B 2 t) /
        Real.log t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have htpos : 0 < t := by linarith
  apply ContinuousAt.continuousWithinAt
  have hphase : ContinuousAt
      (fun x : ℝ => standardAdditiveCharacter (reciprocalPhase A B 2 x)) t :=
    (hasDerivAt_standardAdditiveCharacter_quadratic A B htpos.ne').continuousAt
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have hlogcont : ContinuousAt (fun x : ℝ => (Real.log x : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log htpos.ne')
  exact hphase.div hlogcont (by exact_mod_cast hlog)

/-- The entire right-hand far interval is controlled by the monotone segment
up to the amplitude turning point and the crude post-turning tail. -/
theorem norm_quadraticIntervalIntegral_right_of_stationaryPoint_le
    {A B P b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hδ : 0 < δ) (hδUpper : δ ≤ P / 2)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b)
    (hbP : b ≤ 2 * P) :
    ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      32 * P ^ 3 / (A * δ * Real.log P) +
        160 * P ^ 2 / (A * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hPpos : 0 < P := by linarith
  have hspos : 0 < s := hPpos.trans_le hsLower
  have hPleft : P ≤ s + δ := by linarith
  have hbeforeTurn : s + δ ≤ 3 * s / 2 := by linarith
  by_cases hbturn : b ≤ 3 * s / 2
  · have hnear := norm_quadraticIntervalIntegral_right_near_stationaryPoint_le
      (A := A) (B := B) (P := P) (b := b) (δ := δ)
      hA hP hPleft hδ hright hbturn hbP
    calc
      ‖∫ t in (s + δ)..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        32 * P ^ 3 / (A * δ * Real.log P) := hnear
      _ ≤ 32 * P ^ 3 / (A * δ * Real.log P) +
          160 * P ^ 2 / (A * Real.log P) := by
        have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
        have htailNonneg : 0 ≤ 160 * P ^ 2 / (A * Real.log P) := by positivity
        linarith
  · have hturn : 3 * s / 2 ≤ b := (lt_of_not_ge hbturn).le
    have hturnP : 3 * s / 2 ≤ 2 * P := hturn.trans hbP
    have hnear := norm_quadraticIntervalIntegral_right_near_stationaryPoint_le
      (A := A) (B := B) (P := P) (b := 3 * s / 2) (δ := δ)
      hA hP hPleft hδ hbeforeTurn le_rfl hturnP
    have htail := norm_quadraticIntervalIntegral_right_tail_le
      (A := A) (B := B) (P := P) (b := b)
      hA hP hsLower hturn hbP
    have hstart : 1 < s + δ := by linarith
    have hturnStart : 1 < 3 * s / 2 := by linarith
    have hintNear := intervalIntegrable_quadraticLogIntegrand A B
      hstart hbeforeTurn
    have hintTail := intervalIntegrable_quadraticLogIntegrand A B
      hturnStart hturn
    have hadd := intervalIntegral.integral_add_adjacent_intervals hintNear hintTail
    calc
      ‖∫ t in (s + δ)..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ =
        ‖(∫ t in (s + δ)..(3 * s / 2),
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
          ∫ t in (3 * s / 2)..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ := by
          rw [hadd]
      _ ≤ ‖∫ t in (s + δ)..(3 * s / 2),
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ +
          ‖∫ t in (3 * s / 2)..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ :=
        norm_add_le _ _
      _ ≤ 32 * P ^ 3 / (A * δ * Real.log P) +
          160 * P ^ 2 / (A * Real.log P) := add_le_add hnear htail

/-- Exact three-piece decomposition around a stationary neighborhood wholly
contained in the interval. -/
theorem quadraticIntervalIntegral_eq_stationarySplit
    (A B : ℝ) {a b δ : ℝ} (ha : 1 < a) (hδ : 0 ≤ δ)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - δ)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b) :
    ∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t =
      (∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
      (∫ t in (quadraticReciprocalStationaryPoint A B - δ)..
          (quadraticReciprocalStationaryPoint A B + δ),
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
      ∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t := by
  let s := quadraticReciprocalStationaryPoint A B
  have hmid : s - δ ≤ s + δ := by dsimp only [s]; linarith
  have hstartMid : 1 < s - δ := ha.trans_le hleft
  have hstartRight : 1 < s + δ := hstartMid.trans_le hmid
  have h₁ := intervalIntegrable_quadraticLogIntegrand A B ha hleft
  have h₂ := intervalIntegrable_quadraticLogIntegrand A B hstartMid hmid
  have h₃ := intervalIntegrable_quadraticLogIntegrand A B hstartRight hright
  have h₁₂ := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have h₁₂₃ := intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂) h₃
  dsimp only [s] at h₁₂ h₁₂₃ ⊢
  rw [← h₁₂₃, ← h₁₂]

/-- Near/far reduction for an interior stationary point.  The central piece
is paid for by length; only the two nonstationary outer integrals remain. -/
theorem norm_quadraticIntervalIntegral_le_stationaryFar_add_near
    (A B : ℝ) {P a b δ : ℝ} (hP : 2 ≤ P) (hPa : P ≤ a)
    (hδ : 0 ≤ δ)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - δ)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      ‖∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ +
        2 * δ / Real.log P +
      ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) /
            Real.log t‖ := by
  have ha : 1 < a := (show 1 < P by linarith).trans_le hPa
  rw [quadraticIntervalIntegral_eq_stationarySplit A B ha hδ hleft hright]
  have hmid : quadraticReciprocalStationaryPoint A B - δ ≤
      quadraticReciprocalStationaryPoint A B + δ := by linarith
  have hPleft : P ≤ quadraticReciprocalStationaryPoint A B - δ :=
    hPa.trans hleft
  have hnear := norm_quadraticIntervalIntegral_le_two_mul_radius_div_log
    A B hP hPleft hmid le_rfl le_rfl
  calc
    ‖(∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
        (∫ t in (quadraticReciprocalStationaryPoint A B - δ)..
            (quadraticReciprocalStationaryPoint A B + δ),
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
        ∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        ‖∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ +
          ‖∫ t in (quadraticReciprocalStationaryPoint A B - δ)..
              (quadraticReciprocalStationaryPoint A B + δ),
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ +
          ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ +
          2 * δ / Real.log P +
        ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ := by
      gcongr

/-- Quantitative stationary-phase estimate before optimizing the cutoff
radius.  The first term is the two monotone far pieces, the second is the
central neighborhood, and the last is the post-turning tail. -/
theorem norm_quadraticIntervalIntegral_le_stationary_raw
    {A B P a b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hδ : 0 < δ) (hδUpper : δ ≤ P / 2)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - δ)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      64 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        160 * P ^ 2 / (A * Real.log P) := by
  have hreduce := norm_quadraticIntervalIntegral_le_stationaryFar_add_near
    A B hP hPa hδ.le hleft hright
  have hleftBound := norm_quadraticIntervalIntegral_left_of_stationaryPoint_le
    (A := A) (B := B) (P := P) (a := a) (δ := δ)
    hA hP hPa hδ hleft hsUpper
  have hrightBound := norm_quadraticIntervalIntegral_right_of_stationaryPoint_le
    (A := A) (B := B) (P := P) (b := b) (δ := δ)
    hA hP hsLower hδ hδUpper hright hbP
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      ‖∫ t in a..(quadraticReciprocalStationaryPoint A B - δ),
          standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ +
        2 * δ / Real.log P +
      ‖∫ t in (quadraticReciprocalStationaryPoint A B + δ)..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) /
            Real.log t‖ := hreduce
    _ ≤ 32 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        (32 * P ^ 3 / (A * δ * Real.log P) +
          160 * P ^ 2 / (A * Real.log P)) := by
      gcongr
    _ = 64 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        160 * P ^ 2 / (A * Real.log P) := by ring

/-- Insert the coefficient lower bound forced by the source phase scale. -/
theorem norm_quadraticIntervalIntegral_le_stationary_sourceScale
    {A B P L a b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P) (hL : 0 < L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ A)
    (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hδ : 0 < δ) (hδUpper : δ ≤ P / 2)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - δ)
    (hright : quadraticReciprocalStationaryPoint A B + δ ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      20 * P ^ 2 / (L * δ * Real.log P) + 2 * δ / Real.log P +
        50 * P / (L * Real.log P) := by
  have hraw := norm_quadraticIntervalIntegral_le_stationary_raw
    hA hP hPa hbP hsLower hsUpper hδ hδUpper hleft hright
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hsourcePos : 0 < (16 / 5 : ℝ) * P * L := by positivity
  have hfarDen : (16 / 5 : ℝ) * P * L * δ * Real.log P ≤
      A * δ * Real.log P := by gcongr
  have htailDen : (16 / 5 : ℝ) * P * L * Real.log P ≤
      A * Real.log P := by gcongr
  have hfar : 64 * P ^ 3 / (A * δ * Real.log P) ≤
      20 * P ^ 2 / (L * δ * Real.log P) := by
    calc
      64 * P ^ 3 / (A * δ * Real.log P) ≤
          64 * P ^ 3 /
            ((16 / 5 : ℝ) * P * L * δ * Real.log P) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (by positivity) hfarDen
      _ = 20 * P ^ 2 / (L * δ * Real.log P) := by
        field_simp
        ring
  have htail : 160 * P ^ 2 / (A * Real.log P) ≤
      50 * P / (L * Real.log P) := by
    calc
      160 * P ^ 2 / (A * Real.log P) ≤
          160 * P ^ 2 /
            ((16 / 5 : ℝ) * P * L * Real.log P) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (by positivity) htailDen
      _ = 50 * P / (L * Real.log P) := by
        field_simp
        ring
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      64 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        160 * P ^ 2 / (A * Real.log P) := hraw
    _ ≤ 20 * P ^ 2 / (L * δ * Real.log P) + 2 * δ / Real.log P +
        50 * P / (L * Real.log P) := by gcongr

/-- Optimizing at `δ = P / sqrt L` gives square-root cancellation in the
source phase-scale parameter. -/
theorem norm_quadraticIntervalIntegral_le_stationary_optimized
    {A B P L a b : ℝ} (hA : 0 < A) (hP : 2 ≤ P) (hL : 4 ≤ L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ A)
    (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hleft : a ≤ quadraticReciprocalStationaryPoint A B - P / Real.sqrt L)
    (hright : quadraticReciprocalStationaryPoint A B + P / Real.sqrt L ≤ b) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  let S := Real.sqrt L
  have hPpos : 0 < P := by linarith
  have hLpos : 0 < L := by linarith
  have hSpos : 0 < S := by
    dsimp only [S]
    exact Real.sqrt_pos.2 hLpos
  have hSsq : S ^ 2 = L := by
    dsimp only [S]
    exact Real.sq_sqrt hLpos.le
  have hSTwo : 2 ≤ S := by
    nlinarith [sq_nonneg (S - 2)]
  have hδ : 0 < P / S := div_pos hPpos hSpos
  have hδUpper : P / S ≤ P / 2 :=
    div_le_div_of_nonneg_left hPpos.le (by norm_num) hSTwo
  have hsource := norm_quadraticIntervalIntegral_le_stationary_sourceScale
    hA hP hLpos hAsource hPa hbP hsLower hsUpper hδ hδUpper hleft hright
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hfarEq :
      20 * P ^ 2 / (L * (P / S) * Real.log P) =
        20 * P / (S * Real.log P) := by
    rw [← hSsq]
    field_simp
  have hnearEq : 2 * (P / S) / Real.log P =
      2 * P / (S * Real.log P) := by
    field_simp
  have htailLe : 50 * P / (L * Real.log P) ≤
      25 * P / (S * Real.log P) := by
    rw [← hSsq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hnonneg : 0 ≤ (S - 2) * (25 * P * S * Real.log P) := by positivity
    nlinarith
  rw [hfarEq, hnearEq] at hsource
  change ‖∫ t in a..b,
      standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
    50 * P / (S * Real.log P)
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      20 * P / (S * Real.log P) + 2 * P / (S * Real.log P) +
        50 * P / (L * Real.log P) := hsource
    _ ≤ 20 * P / (S * Real.log P) + 2 * P / (S * Real.log P) +
        25 * P / (S * Real.log P) := by gcongr
    _ = 47 * (P / (S * Real.log P)) := by ring
    _ ≤ 50 * (P / (S * Real.log P)) := by gcongr; norm_num
    _ = 50 * P / (S * Real.log P) := by ring

/-- The raw stationary estimate remains valid when the radius-`δ`
neighborhood is clipped by either endpoint of the integration interval. -/
theorem norm_quadraticIntervalIntegral_le_stationary_raw_clipped
    {A B P a b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint A B)
    (hsb : quadraticReciprocalStationaryPoint A B ≤ b)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hδ : 0 < δ) (hδUpper : δ ≤ P / 2) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      64 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        160 * P ^ 2 / (A * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have ha1 : 1 < a := (show 1 < P by linarith).trans_le hPa
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hfarNonneg : 0 ≤ 32 * P ^ 3 / (A * δ * Real.log P) := by positivity
  have hfar64Eq : 64 * P ^ 3 / (A * δ * Real.log P) =
      2 * (32 * P ^ 3 / (A * δ * Real.log P)) := by ring
  have htailNonneg : 0 ≤ 160 * P ^ 2 / (A * Real.log P) := by positivity
  by_cases hleft : a ≤ s - δ
  · by_cases hright : s + δ ≤ b
    · exact norm_quadraticIntervalIntegral_le_stationary_raw
        hA hP hPa hbP hsLower hsUpper hδ hδUpper hleft hright
    · have hbNear : b ≤ s + δ := (le_of_not_ge hright)
      have hmidb : s - δ ≤ b := by linarith
      have hPmid : P ≤ s - δ := hPa.trans hleft
      have hleftBound :=
        norm_quadraticIntervalIntegral_left_of_stationaryPoint_le
          (A := A) (B := B) (P := P) (a := a) (δ := δ)
          hA hP hPa hδ hleft hsUpper
      have hnear := norm_quadraticIntervalIntegral_le_two_mul_radius_div_log
        A B hP hPmid hmidb le_rfl hbNear
      have hmid1 : 1 < s - δ := ha1.trans_le hleft
      have hintLeft := intervalIntegrable_quadraticLogIntegrand A B ha1 hleft
      have hintNear := intervalIntegrable_quadraticLogIntegrand A B hmid1 hmidb
      have hadd := intervalIntegral.integral_add_adjacent_intervals hintLeft hintNear
      calc
        ‖∫ t in a..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ =
          ‖(∫ t in a..(s - δ),
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
            ∫ t in (s - δ)..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ := by
            rw [hadd]
        _ ≤ ‖∫ t in a..(s - δ),
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ +
            ‖∫ t in (s - δ)..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ :=
          norm_add_le _ _
        _ ≤ 32 * P ^ 3 / (A * δ * Real.log P) +
            2 * δ / Real.log P := add_le_add hleftBound hnear
        _ ≤ 64 * P ^ 3 / (A * δ * Real.log P) +
            2 * δ / Real.log P + 160 * P ^ 2 / (A * Real.log P) := by
          rw [hfar64Eq]
          linarith
  · have haNear : s - δ ≤ a := le_of_not_ge hleft
    by_cases hright : s + δ ≤ b
    · have hasRight : a ≤ s + δ := by linarith
      have hPright : P ≤ s + δ := by linarith
      have hnear := norm_quadraticIntervalIntegral_le_two_mul_radius_div_log
        A B hP hPa hasRight haNear le_rfl
      have hrightBound :=
        norm_quadraticIntervalIntegral_right_of_stationaryPoint_le
          (A := A) (B := B) (P := P) (b := b) (δ := δ)
          hA hP hsLower hδ hδUpper hright hbP
      have hright1 : 1 < s + δ := ha1.trans_le hasRight
      have hintNear := intervalIntegrable_quadraticLogIntegrand A B ha1 hasRight
      have hintRight := intervalIntegrable_quadraticLogIntegrand A B hright1 hright
      have hadd := intervalIntegral.integral_add_adjacent_intervals hintNear hintRight
      calc
        ‖∫ t in a..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ =
          ‖(∫ t in a..(s + δ),
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t) +
            ∫ t in (s + δ)..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ := by
            rw [hadd]
        _ ≤ ‖∫ t in a..(s + δ),
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ +
            ‖∫ t in (s + δ)..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ :=
          norm_add_le _ _
        _ ≤ 2 * δ / Real.log P +
            (32 * P ^ 3 / (A * δ * Real.log P) +
              160 * P ^ 2 / (A * Real.log P)) :=
          add_le_add hnear hrightBound
        _ = 32 * P ^ 3 / (A * δ * Real.log P) +
            2 * δ / Real.log P + 160 * P ^ 2 / (A * Real.log P) := by ring
        _ ≤ 64 * P ^ 3 / (A * δ * Real.log P) +
            2 * δ / Real.log P + 160 * P ^ 2 / (A * Real.log P) := by
          rw [hfar64Eq]
          linarith
    · have hbNear : b ≤ s + δ := le_of_not_ge hright
      have hnear := norm_quadraticIntervalIntegral_le_two_mul_radius_div_log
        A B hP hPa hab haNear hbNear
      calc
        ‖∫ t in a..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
          2 * δ / Real.log P := hnear
        _ ≤ 64 * P ^ 3 / (A * δ * Real.log P) +
            2 * δ / Real.log P + 160 * P ^ 2 / (A * Real.log P) := by
          have hfar64 : 0 ≤ 64 * P ^ 3 / (A * δ * Real.log P) := by positivity
          linarith

theorem stationaryRawMajorant_le_sourceScale
    {A P L δ : ℝ} (hP : 2 ≤ P) (hL : 0 < L)
    (hδ : 0 < δ) (hAsource : (16 / 5 : ℝ) * P * L ≤ A) :
    64 * P ^ 3 / (A * δ * Real.log P) + 2 * δ / Real.log P +
        160 * P ^ 2 / (A * Real.log P) ≤
      20 * P ^ 2 / (L * δ * Real.log P) + 2 * δ / Real.log P +
        50 * P / (L * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hfarDen : (16 / 5 : ℝ) * P * L * δ * Real.log P ≤
      A * δ * Real.log P := by gcongr
  have htailDen : (16 / 5 : ℝ) * P * L * Real.log P ≤
      A * Real.log P := by gcongr
  have hfar : 64 * P ^ 3 / (A * δ * Real.log P) ≤
      20 * P ^ 2 / (L * δ * Real.log P) := by
    calc
      64 * P ^ 3 / (A * δ * Real.log P) ≤
          64 * P ^ 3 /
            ((16 / 5 : ℝ) * P * L * δ * Real.log P) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfarDen
      _ = 20 * P ^ 2 / (L * δ * Real.log P) := by
        field_simp
        ring
  have htail : 160 * P ^ 2 / (A * Real.log P) ≤
      50 * P / (L * Real.log P) := by
    calc
      160 * P ^ 2 / (A * Real.log P) ≤
          160 * P ^ 2 /
            ((16 / 5 : ℝ) * P * L * Real.log P) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) htailDen
      _ = 50 * P / (L * Real.log P) := by
        field_simp
        ring
  gcongr

theorem norm_quadraticIntervalIntegral_le_stationary_sourceScale_clipped
    {A B P L a b δ : ℝ} (hA : 0 < A) (hP : 2 ≤ P) (hL : 0 < L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ A)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint A B)
    (hsb : quadraticReciprocalStationaryPoint A B ≤ b)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P)
    (hδ : 0 < δ) (hδUpper : δ ≤ P / 2) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      20 * P ^ 2 / (L * δ * Real.log P) + 2 * δ / Real.log P +
        50 * P / (L * Real.log P) := by
  exact (norm_quadraticIntervalIntegral_le_stationary_raw_clipped
    hA hP hPa hab hbP hsa hsb hsLower hsUpper hδ hδUpper).trans
      (stationaryRawMajorant_le_sourceScale hP hL hδ hAsource)

theorem stationarySourceScaleMajorant_optimized
    {P L : ℝ} (hP : 2 ≤ P) (hL : 4 ≤ L) :
    20 * P ^ 2 / (L * (P / Real.sqrt L) * Real.log P) +
        2 * (P / Real.sqrt L) / Real.log P +
        50 * P / (L * Real.log P) ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  let S := Real.sqrt L
  have hPpos : 0 < P := by linarith
  have hLpos : 0 < L := by linarith
  have hSpos : 0 < S := by
    dsimp only [S]
    exact Real.sqrt_pos.2 hLpos
  have hSsq : S ^ 2 = L := by
    dsimp only [S]
    exact Real.sq_sqrt hLpos.le
  have hSTwo : 2 ≤ S := by nlinarith [sq_nonneg (S - 2)]
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hfarEq :
      20 * P ^ 2 / (L * (P / S) * Real.log P) =
        20 * P / (S * Real.log P) := by
    rw [← hSsq]
    field_simp
  have hnearEq : 2 * (P / S) / Real.log P =
      2 * P / (S * Real.log P) := by field_simp
  have htailLe : 50 * P / (L * Real.log P) ≤
      25 * P / (S * Real.log P) := by
    rw [← hSsq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hnonneg : 0 ≤ (S - 2) * (25 * P * S * Real.log P) := by positivity
    nlinarith
  change 20 * P ^ 2 / (L * (P / S) * Real.log P) +
      2 * (P / S) / Real.log P + 50 * P / (L * Real.log P) ≤
    50 * P / (S * Real.log P)
  rw [hfarEq, hnearEq]
  calc
    20 * P / (S * Real.log P) + 2 * P / (S * Real.log P) +
        50 * P / (L * Real.log P) ≤
      20 * P / (S * Real.log P) + 2 * P / (S * Real.log P) +
        25 * P / (S * Real.log P) := by gcongr
    _ = 47 * (P / (S * Real.log P)) := by ring
    _ ≤ 50 * (P / (S * Real.log P)) := by gcongr; norm_num
    _ = 50 * P / (S * Real.log P) := by ring

/-- Optimized stationary cancellation with no interior-neighborhood
restriction: the stationary point may lie arbitrarily close to either
endpoint. -/
theorem norm_quadraticIntervalIntegral_le_stationary_optimized_clipped
    {A B P L a b : ℝ} (hA : 0 < A) (hP : 2 ≤ P) (hL : 4 ≤ L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ A)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint A B)
    (hsb : quadraticReciprocalStationaryPoint A B ≤ b)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  have hLpos : 0 < L := by linarith
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsqrtTwo : 2 ≤ Real.sqrt L := by
    nlinarith [Real.sq_sqrt hLpos.le, Real.sqrt_nonneg L]
  have hδ : 0 < P / Real.sqrt L := by positivity
  have hδUpper : P / Real.sqrt L ≤ P / 2 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hsqrtTwo
  exact (norm_quadraticIntervalIntegral_le_stationary_sourceScale_clipped
    hA hP hLpos hAsource hPa hab hbP hsa hsb hsLower hsUpper hδ hδUpper).trans
      (stationarySourceScaleMajorant_optimized hP hL)

theorem quadraticReciprocalStationaryPoint_neg_coefficients (A B : ℝ) :
    quadraticReciprocalStationaryPoint (-A) (-B) =
      quadraticReciprocalStationaryPoint A B := by
  unfold quadraticReciprocalStationaryPoint
  ring

theorem norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_of_neg
    {A B P L a b : ℝ} (hA : A < 0) (hP : 2 ≤ P) (hL : 4 ≤ L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ -A)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint A B)
    (hsb : quadraticReciprocalStationaryPoint A B ≤ b)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  rw [norm_intervalIntegral_quadratic_eq_neg_coefficients A B a b]
  apply norm_quadraticIntervalIntegral_le_stationary_optimized_clipped
    (A := -A) (B := -B) (P := P) (L := L)
  · linarith
  · exact hP
  · exact hL
  · exact hAsource
  · exact hPa
  · exact hab
  · exact hbP
  · simpa only [quadraticReciprocalStationaryPoint_neg_coefficients] using hsa
  · simpa only [quadraticReciprocalStationaryPoint_neg_coefficients] using hsb
  · simpa only [quadraticReciprocalStationaryPoint_neg_coefficients] using hsLower
  · simpa only [quadraticReciprocalStationaryPoint_neg_coefficients] using hsUpper

theorem norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
    {A B P L a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P) (hL : 4 ≤ L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ |A|)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint A B)
    (hsb : quadraticReciprocalStationaryPoint A B ≤ b)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  by_cases hApos : 0 < A
  · apply norm_quadraticIntervalIntegral_le_stationary_optimized_clipped
      hApos hP hL
    · simpa only [abs_of_pos hApos] using hAsource
    · exact hPa
    · exact hab
    · exact hbP
    · exact hsa
    · exact hsb
    · exact hsLower
    · exact hsUpper
  · have hAneg : A < 0 := lt_of_le_of_ne (le_of_not_gt hApos) hA
    apply norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_of_neg
      hAneg hP hL
    · simpa only [abs_of_neg hAneg] using hAsource
    · exact hPa
    · exact hab
    · exact hbP
    · exact hsa
    · exact hsb
    · exact hsLower
    · exact hsUpper

/-- Optimized stationary cancellation on an arbitrary subinterval of the
ambient dyadic block.  The stationary point need only lie in `[P,2P]`; when
it lies outside `[a,b]`, subtract two intervals having the stationary point
as a common endpoint. -/
theorem norm_quadraticIntervalIntegral_le_stationary_optimized_dyadic
    {A B P L a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P) (hL : 4 ≤ L)
    (hAsource : (16 / 5 : ℝ) * P * L ≤ |A|)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint A B)
    (hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      100 * P / (Real.sqrt L * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have ha1 : 1 < a := (show 1 < P by linarith).trans_le hPa
  have hs1 : 1 < s := (show 1 < P by linarith).trans_le hsLower
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hRnonneg :
      0 ≤ 50 * P / (Real.sqrt L * Real.log P) := by positivity
  by_cases hsa : a ≤ s
  · by_cases hsb : s ≤ b
    · have hmain :=
        norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
          hA hP hL hAsource hPa hab hbP hsa hsb hsLower hsUpper
      calc
        _ ≤ 50 * P / (Real.sqrt L * Real.log P) := hmain
        _ ≤ 100 * P / (Real.sqrt L * Real.log P) := by
          rw [show 100 * P / (Real.sqrt L * Real.log P) =
            2 * (50 * P / (Real.sqrt L * Real.log P)) by ring]
          linarith
    · have hbs : b ≤ s := le_of_not_ge hsb
      have hPb : P ≤ b := hPa.trans hab
      have hb1 : 1 < b := ha1.trans_le hab
      have hleft :=
        norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
          hA hP hL hAsource hPa hsa hsUpper hsa le_rfl hsLower hsUpper
      have hright :=
        norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
          hA hP hL hAsource hPb hbs hsUpper hbs le_rfl hsLower hsUpper
      have hintLeft := intervalIntegrable_quadraticLogIntegrand A B ha1 hab
      have hintRight := intervalIntegrable_quadraticLogIntegrand A B hb1 hbs
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight
      calc
        ‖∫ t in a..b,
            standardAdditiveCharacter (reciprocalPhase A B 2 t) /
              Real.log t‖ =
            ‖(∫ t in a..s,
                standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                  Real.log t) -
              ∫ t in b..s,
                standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                  Real.log t‖ := by
              rw [← hadd]
              simp
        _ ≤ ‖∫ t in a..s,
                standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                  Real.log t‖ +
              ‖∫ t in b..s,
                standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                  Real.log t‖ := norm_sub_le _ _
        _ ≤ 100 * P / (Real.sqrt L * Real.log P) := by
          rw [show 100 * P / (Real.sqrt L * Real.log P) =
            50 * P / (Real.sqrt L * Real.log P) +
              50 * P / (Real.sqrt L * Real.log P) by ring]
          exact add_le_add hleft hright
  · have hsa' : s ≤ a := le_of_not_ge hsa
    have hsb : s ≤ b := hsa'.trans hab
    have hfirst :=
      norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
        hA hP hL hAsource hsLower hsb hbP le_rfl hsb hsLower hsUpper
    have hsecond :=
      norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
        hA hP hL hAsource hsLower hsa' (hab.trans hbP) le_rfl hsa'
          hsLower hsUpper
    have hintSecond := intervalIntegrable_quadraticLogIntegrand A B hs1 hsa'
    have hintMain := intervalIntegrable_quadraticLogIntegrand A B ha1 hab
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals hintSecond hintMain
    calc
      ‖∫ t in a..b,
          standardAdditiveCharacter (reciprocalPhase A B 2 t) /
            Real.log t‖ =
          ‖(∫ t in s..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                Real.log t) -
            ∫ t in s..a,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                Real.log t‖ := by
            rw [← hadd]
            simp
      _ ≤ ‖∫ t in s..b,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                Real.log t‖ +
            ‖∫ t in s..a,
              standardAdditiveCharacter (reciprocalPhase A B 2 t) /
                Real.log t‖ := norm_sub_le _ _
      _ ≤ 100 * P / (Real.sqrt L * Real.log P) := by
        rw [show 100 * P / (Real.sqrt L * Real.log P) =
          50 * P / (Real.sqrt L * Real.log P) +
            50 * P / (Real.sqrt L * Real.log P) by ring]
        exact add_le_add hfirst hsecond

/-- Far to the right of a nonnegative stationary point, the integration-by-
parts amplitude is increasing once the logarithm is at least two. -/
theorem unequalQuadraticIntegralAmplitudeDeriv_nonneg_right_far
    {A B t : ℝ} (hA : 0 < A)
    (hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hlog : 2 ≤ Real.log t)
    (hsep : 2 * quadraticReciprocalStationaryPoint A B ≤ t) :
    0 ≤ unequalQuadraticIntegralAmplitudeDeriv A B t := by
  let s := quadraticReciprocalStationaryPoint A B
  have hA0 : A ≠ 0 := hA.ne'
  have ht : 0 ≤ t := by dsimp only [s] at hsep ⊢; linarith
  have hcoef : 0 ≤ 2 * t - 3 * s := by
    dsimp only [s] at hsNonneg hsep ⊢
    linarith
  have hmul : 2 * (2 * t - 3 * s) ≤
      (2 * t - 3 * s) * Real.log t := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlog hcoef
  have hcore : 0 ≤
      (2 * t - 3 * s) * Real.log t - (t - s) := by
    dsimp only [s] at hsNonneg hsep hmul ⊢
    linarith
  have hbracket : 0 ≤
      (2 * A * t + 6 * B) * Real.log t - (A * t + 2 * B) := by
    rw [quadraticReciprocalSecondLinearFactor_eq hA0,
      quadraticReciprocalLinearFactor_eq hA0]
    change 0 ≤ A * (2 * t - 3 * s) * Real.log t - A * (t - s)
    rw [show A * (2 * t - 3 * s) * Real.log t - A * (t - s) =
      A * ((2 * t - 3 * s) * Real.log t - (t - s)) by ring]
    exact mul_nonneg hA.le hcore
  unfold unequalQuadraticIntegralAmplitudeDeriv
  exact div_nonneg (mul_nonneg (sq_nonneg t) hbracket) (sq_nonneg _)

/-- First-derivative cancellation when a nonnegative stationary point lies at
least a half-block to the left of the dyadic interval. -/
theorem norm_quadraticIntervalIntegral_le_of_stationaryPoint_le_half
    {A B P a b : ℝ} (hA : 0 < A) (hP : 2 ≤ P)
    (hlogP : 2 ≤ Real.log P)
    (hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hsFar : quadraticReciprocalStationaryPoint A B ≤ P / 2)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      64 * P ^ 2 / (A * Real.log P) := by
  let s := quadraticReciprocalStationaryPoint A B
  have hPpos : 0 < P := by linarith
  have hlogPpos : 0 < Real.log P := by linarith
  have hdelta : 0 < P / 2 := by positivity
  have hlin : ∀ t ∈ Set.Icc a b, A * t + 2 * B ≠ 0 := by
    intro t ht
    rw [quadraticReciprocalLinearFactor_eq hA.ne']
    apply mul_ne_zero hA.ne'
    apply sub_ne_zero.mpr
    dsimp only [s] at hsFar ⊢
    nlinarith [hPa.trans ht.1]
  have hderiv : ∀ t ∈ Set.Icc a b,
      0 ≤ unequalQuadraticIntegralAmplitudeDeriv A B t := by
    intro t ht
    apply unequalQuadraticIntegralAmplitudeDeriv_nonneg_right_far hA hsNonneg
    · exact hlogP.trans
        (Real.log_le_log hPpos (hPa.trans ht.1))
    · dsimp only [s] at hsFar ⊢
      nlinarith [hPa.trans ht.1]
  have hraw := norm_quadraticIntervalIntegral_le_of_amplitudeDeriv_nonneg
    (A := A) (B := B) (a := a) (b := b) (hP.trans hPa) hab hlin hderiv
  have hfarA : P / 2 ≤ |a - s| := by
    rw [abs_of_nonneg]
    · dsimp only [s] at hsFar ⊢
      linarith
    · dsimp only [s] at hsFar ⊢
      nlinarith
  have hfarB : P / 2 ≤ |b - s| := by
    rw [abs_of_nonneg]
    · dsimp only [s] at hsFar ⊢
      linarith [hPa.trans hab]
    · dsimp only [s] at hsFar ⊢
      nlinarith [hPa.trans hab]
  have hampA := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP hPa (hab.trans hbP) hdelta hfarA
  have hampB := abs_unequalQuadraticIntegralAmplitude_le_of_dyadic_far
    hA hP (hPa.trans hab) hbP hdelta hfarB
  have hfactor : ‖unequalQuadraticIntegralFactor‖ ≤ 1 := by
    rw [norm_unequalQuadraticIntegralFactor]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        2 * ‖unequalQuadraticIntegralFactor‖ *
          (|unequalQuadraticIntegralAmplitude A B a| +
            |unequalQuadraticIntegralAmplitude A B b|) := hraw
    _ ≤ 2 * 1 *
          (8 * P ^ 3 / (A * (P / 2) * Real.log P) +
            8 * P ^ 3 / (A * (P / 2) * Real.log P)) := by gcongr
    _ = 64 * P ^ 2 / (A * Real.log P) := by
      field_simp
      ring

theorem norm_quadraticIntervalIntegral_le_of_stationaryPoint_le_half_abs
    {A B P a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P)
    (hlogP : 2 ≤ Real.log P)
    (hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hsFar : quadraticReciprocalStationaryPoint A B ≤ P / 2)
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      64 * P ^ 2 / (|A| * Real.log P) := by
  by_cases hApos : 0 < A
  · simpa only [abs_of_pos hApos] using
      norm_quadraticIntervalIntegral_le_of_stationaryPoint_le_half
        hApos hP hlogP hsNonneg hsFar hPa hab hbP
  · have hAneg : A < 0 := lt_of_le_of_ne (le_of_not_gt hApos) hA
    rw [norm_intervalIntegral_quadratic_eq_neg_coefficients A B a b]
    have hraw :=
      norm_quadraticIntervalIntegral_le_of_stationaryPoint_le_half
        (A := -A) (B := -B) (by linarith) hP hlogP
        (by simpa only [quadraticReciprocalStationaryPoint_neg_coefficients]
          using hsNonneg)
        (by simpa only [quadraticReciprocalStationaryPoint_neg_coefficients]
          using hsFar)
        hPa hab hbP
    simpa only [abs_of_neg hAneg, neg_neg] using hraw

/-- Source-scale version of the exterior-left first-derivative bound. -/
theorem norm_quadraticIntervalIntegral_le_sourceScale_of_stationaryPoint_le_half
    {A B P L a b : ℝ} (hA : A ≠ 0) (hP : 2 ≤ P)
    (hlogP : 2 ≤ Real.log P) (hL : 0 < L)
    (hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint A B)
    (hsFar : quadraticReciprocalStationaryPoint A B ≤ P / 2)
    (hscale : L ≤ reciprocalPhaseScale A B 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
      20 * P / (L * Real.log P) := by
  have hPpos : 0 < P := by linarith
  have hlogPpos : 0 < Real.log P := by linarith
  have hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P := by
    linarith
  have hAsource := abs_linear_lower_of_phaseScale_lower_of_stationaryPoint
    hA hPpos hsNonneg hsUpper hscale
  have hraw :=
    norm_quadraticIntervalIntegral_le_of_stationaryPoint_le_half_abs
      hA hP hlogP hsNonneg hsFar hPa hab hbP
  calc
    ‖∫ t in a..b,
        standardAdditiveCharacter (reciprocalPhase A B 2 t) / Real.log t‖ ≤
        64 * P ^ 2 / (|A| * Real.log P) := hraw
    _ ≤ 64 * P ^ 2 /
        (((16 / 5 : ℝ) * P * L) * Real.log P) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hAsource hlogPpos.le
    _ = 20 * P / (L * Real.log P) := by
      field_simp
      ring

theorem norm_fourierModeIntegral_Ico_le_stationary_optimized_clipped
    {q : ℤ × ℤ} {N M P L a b : ℝ}
    (hlinear : (q.1 : ℝ) * N ≠ 0)
    (hP : 2 ≤ P) (hL : 4 ≤ L) (hPa : P ≤ a) (hab : a ≤ b)
    (hbP : b ≤ 2 * P)
    (hsa : a ≤ quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M))
    (hsb : quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ b)
    (hscale : L ≤ reciprocalPhaseScale
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * P)) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      50 * P / (Real.sqrt L * Real.log P) := by
  let A := (q.1 : ℝ) * N
  let B := (q.2 : ℝ) * M
  have hsLower : P ≤ quadraticReciprocalStationaryPoint A B := hPa.trans hsa
  have hsUpper : quadraticReciprocalStationaryPoint A B ≤ 2 * P := hsb.trans hbP
  have hAsource := abs_linear_lower_of_phaseScale_lower_of_stationaryPoint
    (A := A) (B := B) hlinear (by linarith)
      (by linarith : 0 ≤ quadraticReciprocalStationaryPoint A B)
      hsUpper hscale
  have hraw := norm_quadraticIntervalIntegral_le_stationary_optimized_clipped_abs
    (A := A) (B := B) hlinear hP hL hAsource hPa hab hbP hsa hsb
      hsLower hsUpper
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact hraw

/-- Fourier-mode form of the stationary estimate on any subinterval of the
dyadic block containing the stationary point. -/
theorem norm_fourierModeIntegral_Ico_le_stationary_optimized_dyadic
    {q : ℤ × ℤ} {N M P L a b : ℝ}
    (hlinear : (q.1 : ℝ) * N ≠ 0)
    (hP : 2 ≤ P) (hL : 4 ≤ L) (hPa : P ≤ a) (hab : a ≤ b)
    (hbP : b ≤ 2 * P)
    (hsLower : P ≤ quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M))
    (hsUpper : quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ 2 * P)
    (hscale : L ≤ reciprocalPhaseScale
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * P)) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      100 * P / (Real.sqrt L * Real.log P) := by
  let A := (q.1 : ℝ) * N
  let B := (q.2 : ℝ) * M
  have hAsource := abs_linear_lower_of_phaseScale_lower_of_stationaryPoint
    (A := A) (B := B) hlinear (by linarith)
      ((by linarith) : 0 ≤ quadraticReciprocalStationaryPoint A B)
      hsUpper hscale
  have hraw := norm_quadraticIntervalIntegral_le_stationary_optimized_dyadic
    (A := A) (B := B) hlinear hP hL hAsource hPa hab hbP hsLower hsUpper
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact hraw

/-- Fourier-mode exterior-left estimate: the nonnegative stationary point is
at most `P/2`, hence the whole dyadic interval is nonstationary. -/
theorem norm_fourierModeIntegral_Ico_le_sourceScale_of_stationaryPoint_le_half
    {q : ℤ × ℤ} {N M P L a b : ℝ}
    (hlinear : (q.1 : ℝ) * N ≠ 0)
    (hP : 2 ≤ P) (hlogP : 2 ≤ Real.log P) (hL : 0 < L)
    (hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M))
    (hsFar : quadraticReciprocalStationaryPoint
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ P / 2)
    (hscale : L ≤ reciprocalPhaseScale
      ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * P))
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P) :
    ‖fourierModeIntegral (Set.Ico a b) q N M 2‖ ≤
      20 * P / (L * Real.log P) := by
  have hraw :=
    norm_quadraticIntervalIntegral_le_sourceScale_of_stationaryPoint_le_half
      (A := (q.1 : ℝ) * N) (B := (q.2 : ℝ) * M)
      hlinear hP hlogP hL hsNonneg hsFar hscale hPa hab hbP
  unfold fourierModeIntegral
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact hraw

/-- Literal Fourier-mode discrepancy in the stationary chamber.  The scale
`L` is left explicit so later Fourier summation can choose its logarithmic
power without reopening the stationary calculation. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_stationary
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M L : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N ≠ 0 → (q.2 : ℝ) * M ≠ 0 → 4 ≤ L →
      (a : ℝ) ≤ quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) →
      quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ (b : ℝ) →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ L →
      L ≤ reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
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
          50 * (P : ℝ) / (Real.sqrt L * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M L hPa hab hbP hlinear hquadratic hL hsa hsb
    hlogLower hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic (hlogLower.trans hlower) hNupper hMupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_stationary_optimized_clipped
      (q := q) (N := N) (M := M) (P := (P : ℝ)) (L := L)
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear
      (by exact_mod_cast hP) hL (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
      hsa hsb hlower
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

/-- The stationary high-frequency Fourier estimate only requires the
stationary point to lie in the ambient dyadic block, not in the particular
subinterval being summed. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_stationary_dyadic
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M L : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N ≠ 0 → (q.2 : ℝ) * M ≠ 0 → 4 ≤ L →
      (P : ℝ) ≤ quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) →
      quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ 2 * (P : ℝ) →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ L →
      L ≤ reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
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
          100 * (P : ℝ) / (Real.sqrt L * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with P hprimeP hP
  intro a b q N M L hPa hab hbP hlinear hquadratic hL hsLower hsUpper
    hlogLower hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic (hlogLower.trans hlower) hNupper hMupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_stationary_optimized_dyadic
      (q := q) (N := N) (M := M) (P := (P : ℝ)) (L := L)
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear
      (by exact_mod_cast hP) hL (by exact_mod_cast hPa)
      (by exact_mod_cast hab.le) (by exact_mod_cast hbP)
      hsLower hsUpper hlower
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

/-- Prime-minus-integral estimate in the exterior-left opposite-sign chamber.
The phase stationary point is nonnegative but lies at most at `P/2`. -/
theorem eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_stationary_left
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M L : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (q.1 : ℝ) * N ≠ 0 → (q.2 : ℝ) * M ≠ 0 → 4 ≤ L →
      0 ≤ quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) →
      quadraticReciprocalStationaryPoint
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ (P : ℝ) / 2 →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤ L →
      L ≤ reciprocalPhaseScale ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2
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
          20 * (P : ℝ) / (L * Real.log P) := by
  have hprime := eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    hVinogradov hA₀ hε haexp hS
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hprime, hlogLarge, eventually_ge_atTop (2 : ℕ)] with
      P hprimeP hlogP hP
  intro a b q N M L hPa hab hbP hlinear hquadratic hL hsNonneg hsFar
    hlogLower hlower hNupper hMupper
  have hsum := primeFourierModeSum_Ico_eq_reciprocalPhaseSum
    hP hPa hbP q N M
  have hprimeBound := hprimeP a b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M)
    hPa hab hbP hquadratic (hlogLower.trans hlower) hNupper hMupper
  have hintegralBound :=
    norm_fourierModeIntegral_Ico_le_sourceScale_of_stationaryPoint_le_half
      (q := q) (N := N) (M := M) (P := (P : ℝ)) (L := L)
      (a := (a : ℝ)) (b := (b : ℝ)) hlinear
      (by exact_mod_cast hP) hlogP (by linarith) hsNonneg hsFar hlower
      (by exact_mod_cast hPa) (by exact_mod_cast hab.le)
      (by exact_mod_cast hbP)
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hprimeBound hintegralBound)

end
end Tao2026
