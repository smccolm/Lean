import Tao2026.LowFrequency
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Low-frequency discrete-to-continuous bridge

This module isolates the elementary part of the classical-PNT branch in
Tao's Proposition 1.12.  It compares the logarithmically weighted integer
reciprocal-phase sum with the corresponding interval integral.  No prime
number theorem input is used here.
-/

open Complex Finset MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace Tao2026

noncomputable section

/-- An interval integral with natural endpoints is the exact sum of its
unit-cell interval integrals. -/
theorem sum_Ico_intervalIntegral_nat_cells_complex
    (f : ℝ → ℂ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b,
        ∫ t in (n : ℝ)..(n + 1 : ℝ), f t) =
      ∫ t in (a : ℝ)..(b : ℝ), f t := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab',
          intervalIntegral.integral_add_adjacent_intervals
            (hf (a : ℝ) (b : ℝ)) (hf (b : ℝ) (b + 1 : ℝ))]
        norm_num
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- The inverse logarithm has a uniform Lipschitz constant on a positive
dyadic interval. -/
theorem abs_inv_log_sub_le_dyadic
    {P s t : ℝ} (hP : 2 ≤ P)
    (hs : s ∈ Set.Icc P (2 * P)) (ht : t ∈ Set.Icc P (2 * P)) :
    |(Real.log t)⁻¹ - (Real.log s)⁻¹| ≤
      (1 / (P * (Real.log P) ^ 2)) * |t - s| := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hdiff : ∀ x ∈ Set.Icc P (2 * P),
      DifferentiableAt ℝ (fun y : ℝ => (Real.log y)⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := hPpos.trans_le hx.1
    have hxone : 1 < x := (by norm_num : (1 : ℝ) < 2).trans_le (hP.trans hx.1)
    exact ((Real.hasDerivAt_log hxpos.ne').inv
      (ne_of_gt (Real.log_pos hxone))).differentiableAt
  have hbound : ∀ x ∈ Set.Icc P (2 * P),
      ‖deriv (fun y : ℝ => (Real.log y)⁻¹) x‖ ≤
        1 / (P * (Real.log P) ^ 2) := by
    intro x hx
    have hxpos : 0 < x := hPpos.trans_le hx.1
    have hxone : 1 < x := (by norm_num : (1 : ℝ) < 2).trans_le (hP.trans hx.1)
    have hlogx : 0 < Real.log x := Real.log_pos hxone
    have hlogPx : Real.log P ≤ Real.log x :=
      Real.log_le_log hPpos hx.1
    have hderiv := (Real.hasDerivAt_log hxpos.ne').inv hlogx.ne'
    have hderiv' : deriv (fun y : ℝ => (Real.log y)⁻¹) x =
        -x⁻¹ / Real.log x ^ 2 := hderiv.deriv
    rw [hderiv', Real.norm_eq_abs, abs_div, abs_neg,
      abs_inv, abs_of_pos hxpos, abs_pow, abs_of_pos hlogx,
      one_div]
    rw [div_eq_mul_inv, ← mul_inv]
    apply inv_anti₀
    · positivity
    · exact mul_le_mul hx.1 (pow_le_pow_left₀ hlogP.le hlogPx 2)
        (sq_nonneg _) hxpos.le
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc P (2 * P)) hs ht)

/-- On a positive dyadic interval, the logarithmically weighted reciprocal
character varies by the phase variation plus the inverse-logarithm
variation. -/
theorem norm_reciprocalPhaseLogWeight_sub_le_dyadic
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P s t : ℝ} (hP : 2 ≤ P)
    (hs : s ∈ Set.Icc P (2 * P)) (ht : t ∈ Set.Icc P (2 * P)) :
    ‖standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t -
        standardAdditiveCharacter (reciprocalPhase N M j s) / Real.log s‖ ≤
      (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) * |t - s| := by
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have htpos : 0 < t := hPpos.trans_le ht.1
  have hlogt : 0 < Real.log t := Real.log_pos
    ((by norm_num : (1 : ℝ) < 2).trans_le (hP.trans ht.1))
  have hlogPt : Real.log P ≤ Real.log t := Real.log_le_log hPpos ht.1
  let zt := standardAdditiveCharacter (reciprocalPhase N M j t)
  let zs := standardAdditiveCharacter (reciprocalPhase N M j s)
  have hchar : ‖zt - zs‖ ≤
      2 * Real.pi *
        (((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) * |t - s|) := by
    simpa only [zt, zs] using
      norm_standardAdditiveCharacter_reciprocalPhase_sub_le
        N M hj hPpos hs ht
  have hloginv : |(Real.log t)⁻¹ - (Real.log s)⁻¹| ≤
      (1 / (P * (Real.log P) ^ 2)) * |t - s| :=
    abs_inv_log_sub_le_dyadic hP hs ht
  have hinv : (Real.log t)⁻¹ ≤ (Real.log P)⁻¹ :=
    inv_anti₀ hlogP hlogPt
  have hnormInv :
      ‖((Real.log t : ℂ)⁻¹) - ((Real.log s : ℂ)⁻¹)‖ =
        |(Real.log t)⁻¹ - (Real.log s)⁻¹| := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdecomp :
      zt / (Real.log t : ℂ) - zs / (Real.log s : ℂ) =
        (zt - zs) * ((Real.log t : ℂ)⁻¹) +
          zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  change ‖zt / (Real.log t : ℂ) - zs / (Real.log s : ℂ)‖ ≤ _
  rw [hdecomp]
  calc
    ‖(zt - zs) * ((Real.log t : ℂ)⁻¹) +
        zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ)‖ ≤
        ‖zt - zs‖ * (Real.log t)⁻¹ +
          |(Real.log t)⁻¹ - (Real.log s)⁻¹| := by
      calc
        _ ≤ ‖(zt - zs) * ((Real.log t : ℂ)⁻¹)‖ +
              ‖zs * (((Real.log t)⁻¹ - (Real.log s)⁻¹ : ℝ) : ℂ)‖ :=
          norm_add_le _ _
        _ = _ := by
          simp [zt, zs, norm_standardAdditiveCharacter,
            norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogt,
            hnormInv]
    _ ≤ (2 * Real.pi *
          (((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) * |t - s|)) *
          (Real.log P)⁻¹ +
        (1 / (P * (Real.log P) ^ 2)) * |t - s| := by
      exact add_le_add
        (mul_le_mul hchar hinv (inv_nonneg.mpr hlogt.le) (by
          have hscale : 0 ≤ reciprocalPhaseScale N M j P :=
            reciprocalPhaseScale_nonneg N M j hPpos
          positivity))
        hloginv
    _ = (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) * |t - s| := by
      rw [div_eq_mul_inv]
      ring

/-- The logarithmically weighted reciprocal character is interval integrable
on every interval lying strictly to the right of `1`. -/
theorem intervalIntegrable_reciprocalPhaseLogWeight_of_one_lt
    (N M : ℝ) (j : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ =>
        standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t)
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have htpos : 0 < t := by
    have hat : a ≤ t := ht.1
    linarith
  have htone : 1 < t := by
    exact ha.trans_le ht.1
  have hphase : ContinuousAt (reciprocalPhase N M j) t := by
    have hlinear : ContinuousAt (fun x : ℝ => N / x) t :=
      continuousAt_const.div continuousAt_id htpos.ne'
    have hhigher : ContinuousAt (fun x : ℝ => M / x ^ j) t :=
      continuousAt_const.div (continuousAt_id.pow j) (pow_ne_zero j htpos.ne')
    have heq : reciprocalPhase N M j =
        fun x : ℝ => N / x + M / x ^ j := by
      funext x
      exact reciprocalPhase_eq_div N M j x
    rw [heq]
    exact hlinear.add hhigher
  have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htone)
  have hlogtc : (Real.log t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogt
  exact ((continuous_standardAdditiveCharacter.continuousAt.comp hphase).div
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log htpos.ne')) hlogtc).continuousWithinAt

/-- On one integer cell inside a positive dyadic interval, replacing the
left-endpoint logarithmically weighted reciprocal character by its cell
integral costs at most the dyadic Lipschitz constant. -/
theorem norm_reciprocalPhaseLogWeight_sub_integral_natCell_le_dyadic
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {n : ℕ} (hnlow : P ≤ (n : ℝ))
    (hnhigh : (n : ℝ) + 1 ≤ 2 * P) :
    ‖standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n -
        ∫ t in (n : ℝ)..((n : ℝ) + 1),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
      2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2) := by
  let f : ℝ → ℂ := fun t =>
    standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t
  let C : ℝ :=
    2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
        Real.log P +
      1 / (P * (Real.log P) ^ 2)
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hnmem : (n : ℝ) ∈ Set.Icc P (2 * P) := by
    constructor
    · exact hnlow
    · linarith
  have hC : 0 ≤ C := by
    have hscale : 0 ≤ reciprocalPhaseScale N M j P :=
      reciprocalPhaseScale_nonneg N M j hPpos
    dsimp [C]
    positivity
  have hint : IntervalIntegrable f volume (n : ℝ) ((n : ℝ) + 1) := by
    dsimp [f]
    apply intervalIntegrable_reciprocalPhaseLogWeight_of_one_lt N M j
    · linarith
    · linarith
  have hconst :
      (∫ _t in (n : ℝ)..((n : ℝ) + 1), f n) = f n := by
    rw [intervalIntegral.integral_const]
    norm_num
  change ‖f n - ∫ t in (n : ℝ)..((n : ℝ) + 1), f t‖ ≤ C
  rw [← hconst, ← intervalIntegral.integral_sub intervalIntegrable_const hint]
  calc
    ‖∫ t in (n : ℝ)..((n : ℝ) + 1), f n - f t‖ ≤
        C * |((n : ℝ) + 1) - n| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have horder : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      rw [Set.uIoc_of_le horder] at ht
      have htdyadic : t ∈ Set.Icc P (2 * P) := by
        constructor
        · exact hnlow.trans ht.1.le
        · exact ht.2.trans hnhigh
      have hdist : |t - (n : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
        apply sub_le_iff_le_add.mpr
        simpa [add_comm] using ht.2
      have hpoint := norm_reciprocalPhaseLogWeight_sub_le_dyadic
        N M hj hP hnmem htdyadic
      change ‖f n - f t‖ ≤ C
      calc
        ‖f n - f t‖ = ‖f t - f n‖ := norm_sub_rev _ _
        _ ≤ C * |t - (n : ℝ)| := by
          simpa only [f, C] using hpoint
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hdist hC
        _ = C := mul_one C
    _ = C := by norm_num

/-- Exact telescoping of the logarithmically weighted reciprocal character
over an integer interval lying to the right of its logarithmic singularity. -/
theorem sum_Ico_reciprocalPhaseLogWeight_eq_integral
    (N M : ℝ) (j : ℕ) {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b,
        ∫ t in (n : ℝ)..((n : ℝ) + 1),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t) =
      ∫ t in (a : ℝ)..(b : ℝ),
        standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t := by
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab',
          intervalIntegral.integral_add_adjacent_intervals]
        · norm_num
        · apply intervalIntegrable_reciprocalPhaseLogWeight_of_one_lt N M j
          · exact_mod_cast (show 1 < a by omega)
          · exact_mod_cast hab'
        · apply intervalIntegrable_reciprocalPhaseLogWeight_of_one_lt N M j
          · exact_mod_cast (show 1 < b by omega)
          · norm_num
      · have haeq : a = b + 1 := by omega
        subst a
        simp

/-- Summing the unit-cell estimate compares the complete logarithmically
weighted integer reciprocal-phase sum with its interval integral.  The
factor `P` is the maximum number of cells in a dyadic interval. -/
theorem norm_reciprocalPhaseLogWeightSum_sub_integral_le_dyadic
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {a b : ℕ} (hab : a ≤ b) (halow : P ≤ (a : ℝ))
    (hbhigh : (b : ℝ) ≤ 2 * P) :
    ‖(∑ n ∈ Finset.Ico a b,
          standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n) -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
      P * (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) := by
  let f : ℝ → ℂ := fun t =>
    standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t
  let C : ℝ :=
    2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
        Real.log P +
      1 / (P * (Real.log P) ^ 2)
  have hPpos : 0 < P := by linarith
  have ha : 2 ≤ a := by
    have : (2 : ℝ) ≤ (a : ℝ) := hP.trans halow
    exact_mod_cast this
  have hC : 0 ≤ C := by
    have hscale : 0 ≤ reciprocalPhaseScale N M j P :=
      reciprocalPhaseScale_nonneg N M j hPpos
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    dsimp [C]
    positivity
  have htel := sum_Ico_reciprocalPhaseLogWeight_eq_integral
    N M j ha hab
  have hcard : ((Finset.Ico a b).card : ℝ) ≤ P := by
    rw [Nat.card_Ico, Nat.cast_sub hab]
    linarith
  change ‖(∑ n ∈ Finset.Ico a b, f n) -
      ∫ t in (a : ℝ)..(b : ℝ), f t‖ ≤ P * C
  rw [← htel]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Ico a b,
        (f n - ∫ t in (n : ℝ)..((n : ℝ) + 1), f t)‖ ≤
        ∑ n ∈ Finset.Ico a b,
          ‖f n - ∫ t in (n : ℝ)..((n : ℝ) + 1), f t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico a b, C := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hnlow : P ≤ (n : ℝ) := by
        exact halow.trans (by exact_mod_cast hn.1)
      have hnhigh : (n : ℝ) + 1 ≤ 2 * P := by
        have hnb : n + 1 ≤ b := by omega
        exact (by exact_mod_cast hnb : (n : ℝ) + 1 ≤ (b : ℝ)).trans hbhigh
      simpa only [f, C] using
        norm_reciprocalPhaseLogWeight_sub_integral_natCell_le_dyadic
          N M hj hP hnlow hnhigh
    _ = ((Finset.Ico a b).card : ℝ) * C := by simp
    _ ≤ P * C := mul_le_mul_of_nonneg_right hcard hC

/-- Expanded form of the discrete-to-continuous error: the dyadic interval
length cancels the `P⁻¹` in the cellwise Lipschitz constant. -/
theorem norm_reciprocalPhaseLogWeightSum_sub_integral_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {a b : ℕ} (hab : a ≤ b) (halow : P ≤ (a : ℝ))
    (hbhigh : (b : ℝ) ≤ 2 * P) :
    ‖(∑ n ∈ Finset.Ico a b,
          standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n) -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
      2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
          Real.log P +
        1 / (Real.log P) ^ 2 := by
  have hPne : P ≠ 0 := ne_of_gt (by linarith : 0 < P)
  calc
    _ ≤ P * (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
          Real.log P +
        1 / (P * (Real.log P) ^ 2)) :=
      norm_reciprocalPhaseLogWeightSum_sub_integral_le_dyadic
        N M hj hP hab halow hbhigh
    _ = _ := by
      field_simp

/-- The logarithmically weighted integer reciprocal-phase sum used in the
low-frequency comparison. -/
def integerLogWeightedReciprocalPhaseSum
    (N M : ℝ) (j a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a b,
    standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n

/-- The corresponding von-Mangoldt sum with the logarithmic weight removed
pointwise. Prime powers will be separated from this sum in the next layer. -/
def mangoldtLogWeightedReciprocalPhaseSum
    (N M : ℝ) (j a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a b,
    standardAdditiveCharacter (reciprocalPhase N M j n) * (Λ n : ℂ) /
      Real.log n

/-- The weighted Mangoldt discrepancy is exactly the difference between the
Mangoldt/log sum and the integer/log sum. -/
theorem mangoldtLogWeightedReciprocalPhaseSum_sub_integer_eq
    (N M : ℝ) (j a b : ℕ) :
    mangoldtLogWeightedReciprocalPhaseSum N M j a b -
        integerLogWeightedReciprocalPhaseSum N M j a b =
      ∑ n ∈ Finset.Ico a b,
        (standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n) •
          mangoldtDiscrepancyTerm n := by
  unfold mangoldtLogWeightedReciprocalPhaseSum
    integerLogWeightedReciprocalPhaseSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [mangoldtDiscrepancyTerm, smul_eq_mul]
  ring_nf

/-- Total variation of the logarithmically weighted reciprocal character on
a dyadic integer interval. -/
theorem sum_norm_reciprocalPhaseLogWeight_succ_sub_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {a b : ℕ} (hab : a < b) (halow : P ≤ (a : ℝ))
    (hbhigh : (b : ℝ) ≤ 2 * P) :
    ∑ n ∈ Finset.Ico a (b - 1),
        ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) /
              Real.log (n + 1) -
            standardAdditiveCharacter (reciprocalPhase N M j n) /
              Real.log n‖ ≤
      2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
          Real.log P +
        1 / (Real.log P) ^ 2 := by
  let C : ℝ :=
    2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j P / P) /
        Real.log P +
      1 / (P * (Real.log P) ^ 2)
  have hPpos : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hab' : a ≤ b - 1 := by omega
  have hC : 0 ≤ C := by
    have hscale : 0 ≤ reciprocalPhaseScale N M j P :=
      reciprocalPhaseScale_nonneg N M j hPpos
    dsimp [C]
    positivity
  have hcard : ((Finset.Ico a (b - 1)).card : ℝ) ≤ P := by
    rw [Nat.card_Ico, Nat.cast_sub hab']
    have hcast : ((b - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (Nat.sub_le b 1)
    linarith
  calc
    _ ≤ ∑ _n ∈ Finset.Ico a (b - 1), C := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hnmem : (n : ℝ) ∈ Set.Icc P (2 * P) := by
        constructor
        · exact halow.trans (by exact_mod_cast hn.1)
        · have hnb : n ≤ b := by omega
          exact (by exact_mod_cast hnb : (n : ℝ) ≤ (b : ℝ)).trans hbhigh
      have hnsuccmem : ((n + 1 : ℕ) : ℝ) ∈ Set.Icc P (2 * P) := by
        constructor
        · exact hnmem.1.trans (by exact_mod_cast (Nat.le_succ n))
        · have hnb : n + 1 ≤ b := by omega
          exact (by exact_mod_cast hnb : ((n + 1 : ℕ) : ℝ) ≤ (b : ℝ)).trans
            hbhigh
      have hpoint := norm_reciprocalPhaseLogWeight_sub_le_dyadic
        N M hj hP hnmem hnsuccmem
      simpa only [C, Nat.cast_add, Nat.cast_one, abs_one,
        add_sub_cancel_left, mul_one] using hpoint
    _ = ((Finset.Ico a (b - 1)).card : ℝ) * C := by simp
    _ ≤ P * C := mul_le_mul_of_nonneg_right hcard hC
    _ = 2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
          Real.log P +
        1 / (Real.log P) ^ 2 := by
      dsimp [C]
      field_simp

/-- Abel summation with the quantitative PNT discrepancy left as an explicit
input. The cost is the endpoint inverse logarithm plus the total variation
proved above. -/
theorem norm_mangoldtLogWeightedReciprocalPhaseSum_sub_integer_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {a b : ℕ} (hab : a < b) (halow : P ≤ (a : ℝ))
    (hbhigh : (b : ℝ) ≤ 2 * P) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
        integerLogWeightedReciprocalPhaseSum N M j a b‖ ≤
      (1 / Real.log P +
        (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
            Real.log P +
          1 / (Real.log P) ^ 2)) * B := by
  let f : ℕ → ℂ := fun n =>
    standardAdditiveCharacter (reciprocalPhase N M j n) / Real.log n
  have habel := norm_sum_Ico_complex_smul_le_endpoint_add_variation
    f mangoldtDiscrepancyTerm hab (fun k hak hkb => by
      simpa [mangoldtDiscrepancyPartialSum] using hpartial k hak hkb)
  have hvariation := sum_norm_reciprocalPhaseLogWeight_succ_sub_le
    N M hj hP hab halow hbhigh
  have hbpred : a ≤ b - 1 := by omega
  have hbpredlow : P ≤ ((b - 1 : ℕ) : ℝ) :=
    halow.trans (by exact_mod_cast hbpred)
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hpredpos : 0 < ((b - 1 : ℕ) : ℝ) := by linarith
  have hlogpred : 0 < Real.log ((b - 1 : ℕ) : ℝ) :=
    Real.log_pos ((by linarith : (1 : ℝ) < P).trans_le hbpredlow)
  have hlogle : Real.log P ≤ Real.log ((b - 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hbpredlow
  have hendpoint : ‖f (b - 1)‖ ≤ 1 / Real.log P := by
    dsimp [f]
    rw [norm_div, norm_standardAdditiveCharacter, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlogpred]
    simpa [one_div] using inv_anti₀ hlogP hlogle
  rw [mangoldtLogWeightedReciprocalPhaseSum_sub_integer_eq]
  change ‖∑ n ∈ Finset.Ico a b, f n • mangoldtDiscrepancyTerm n‖ ≤ _
  calc
    _ ≤ ‖f (b - 1)‖ * B +
        ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ * B := habel
    _ ≤ (1 / Real.log P) * B +
        (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
            Real.log P +
          1 / (Real.log P) ^ 2) * B := by
      rw [← Finset.sum_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hendpoint hB)
        (mul_le_mul_of_nonneg_right (by
          simpa only [f, Nat.cast_add, Nat.cast_one] using hvariation) hB)
    _ = _ := by ring

/-- Complete conditional low-frequency Mangoldt/log-to-integral comparison.
Only the explicit partial-sum discrepancy `B` remains analytic. -/
theorem norm_mangoldtLogWeightedReciprocalPhaseSum_sub_integral_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {P : ℝ} (hP : 2 ≤ P)
    {a b : ℕ} (hab : a < b) (halow : P ≤ (a : ℝ))
    (hbhigh : (b : ℝ) ≤ 2 * P) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
        ∫ t in (a : ℝ)..(b : ℝ),
          standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
      (1 / Real.log P +
        (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
            Real.log P +
          1 / (Real.log P) ^ 2)) * B +
        (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
            Real.log P +
          1 / (Real.log P) ^ 2) := by
  calc
    _ ≤ ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
          integerLogWeightedReciprocalPhaseSum N M j a b‖ +
        ‖integerLogWeightedReciprocalPhaseSum N M j a b -
          ∫ t in (a : ℝ)..(b : ℝ),
            standardAdditiveCharacter (reciprocalPhase N M j t) /
              Real.log t‖ := by
      rw [show mangoldtLogWeightedReciprocalPhaseSum N M j a b -
          (∫ t in (a : ℝ)..(b : ℝ),
            standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t) =
          (mangoldtLogWeightedReciprocalPhaseSum N M j a b -
            integerLogWeightedReciprocalPhaseSum N M j a b) +
          (integerLogWeightedReciprocalPhaseSum N M j a b -
            ∫ t in (a : ℝ)..(b : ℝ),
              standardAdditiveCharacter (reciprocalPhase N M j t) /
                Real.log t) by ring]
      exact norm_add_le _ _
    _ ≤ (1 / Real.log P +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) * B +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2) := by
      apply add_le_add
      · exact norm_mangoldtLogWeightedReciprocalPhaseSum_sub_integer_le
          N M hj hP hab halow hbhigh hB hpartial
      · simpa [integerLogWeightedReciprocalPhaseSum] using
          norm_reciprocalPhaseLogWeightSum_sub_integral_le
            N M hj hP hab.le halow hbhigh

end

end Tao2026
