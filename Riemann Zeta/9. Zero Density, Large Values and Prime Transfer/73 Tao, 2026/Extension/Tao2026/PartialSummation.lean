import Tao2026.PrimePowerReduction
import Tao2026.TypeIReduction
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite partial summation on integer intervals

This module isolates the exact Abel-summation step used twice in the proof of
the pinned prime-equidistribution theorem: to pass between prime and
logarithmically weighted prime sums, and to deduce the alternate Type I sum
with a logarithmic inner coefficient from the unweighted Type I estimate.

The statements are finite and quantitative.  In particular, the logarithmic
weight costs at most the explicit factor `2 * log b` once all interval partial
sums are bounded by the same number.
-/

open Complex Finset Set
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- Partial sum of `w` on the half-open natural interval `[a,k)`. -/
def intervalPartialSum (w : ℕ → ℂ) (a k : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a k, w n

/-- A forward difference telescopes on a half-open interval. -/
theorem sum_Ico_forwardDifference (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f (n + 1) - f n) = f b - f a := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab']
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- Backward-difference form of the same telescoping identity. -/
theorem sum_Ico_backwardDifference (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  calc
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) =
        -(∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = -(f b - f a) := by rw [sum_Ico_forwardDifference f hab]
    _ = f a - f b := by ring

/-- Exact finite Abel summation written in terms of interval partial sums.
The coefficient ring is `ℝ` and the target is `ℂ`, matching the real
logarithmic weight and complex phase sums in the source. -/
theorem sum_Ico_smul_eq_endpoint_sub_differences
    (f : ℕ → ℝ) (w : ℕ → ℂ) {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Finset.Ico a b, f n • w n =
      f (b - 1) • intervalPartialSum w a b -
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1) := by
  let w' : ℕ → ℂ := fun n => if a ≤ n then w n else 0
  have hprefix (k : ℕ) (hak : a ≤ k) :
      ∑ n ∈ Finset.range k, w' n = intervalPartialSum w a k := by
    unfold w' intervalPartialSum
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    · intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp hn).1
      simp
  have hraw := Finset.sum_Ico_by_parts f w' hab
  rw [hprefix b hab.le, hprefix a le_rfl] at hraw
  have hsum :
      ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • ∑ i ∈ Finset.range (n + 1), w' i =
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    have han : a ≤ n := (Finset.mem_Ico.mp hn).1
    rw [hprefix (n + 1) (han.trans (Nat.le_succ n))]
  rw [hsum] at hraw
  simp only [intervalPartialSum, Finset.Ico_self, Finset.sum_empty, smul_zero,
    sub_zero] at hraw
  calc
    ∑ n ∈ Finset.Ico a b, f n • w n =
        ∑ n ∈ Finset.Ico a b, f n • w' n := by
      apply Finset.sum_congr rfl
      intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp hn).1
      simp [w', han]
    _ = _ := hraw

/-- Norm bound obtained from finite Abel summation.  It keeps the exact total
variation of the coefficient sequence visible. -/
theorem norm_sum_Ico_smul_le_endpoint_add_variation
    (f : ℕ → ℝ) (w : ℕ → ℂ) {a b : ℕ} {B : ℝ}
    (hab : a < b)
    (hpartial : ∀ k, a < k → k ≤ b → ‖intervalPartialSum w a k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤
      |f (b - 1)| * B +
        ∑ n ∈ Finset.Ico a (b - 1), |f (n + 1) - f n| * B := by
  rw [sum_Ico_smul_eq_endpoint_sub_differences f w hab]
  calc
    ‖f (b - 1) • intervalPartialSum w a b -
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ ≤
        ‖f (b - 1) • intervalPartialSum w a b‖ +
          ‖∑ n ∈ Finset.Ico a (b - 1),
            (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ :=
      norm_sub_le _ _
    _ ≤ |f (b - 1)| * B +
        ∑ n ∈ Finset.Ico a (b - 1), |f (n + 1) - f n| * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hpartial b hab le_rfl) (abs_nonneg _)
      · calc
          ‖∑ n ∈ Finset.Ico a (b - 1),
              (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ ≤
              ∑ n ∈ Finset.Ico a (b - 1),
                ‖(f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ico a (b - 1),
                |f (n + 1) - f n| * B := by
            apply Finset.sum_le_sum
            intro n hn
            rw [norm_smul, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply hpartial (n + 1)
            · exact Nat.lt_succ_of_le (Finset.mem_Ico.mp hn).1
            · have hnTop := (Finset.mem_Ico.mp hn).2
              omega

/-- Complex-coefficient finite Abel summation.  This companion to the
real-coefficient identity is the form needed when the slowly varying factor
is an additive character and the partial sums are Mangoldt discrepancies. -/
theorem sum_Ico_complex_smul_eq_endpoint_sub_differences
    (f w : ℕ → ℂ) {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Finset.Ico a b, f n • w n =
      f (b - 1) • intervalPartialSum w a b -
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1) := by
  let w' : ℕ → ℂ := fun n => if a ≤ n then w n else 0
  have hprefix (k : ℕ) (hak : a ≤ k) :
      ∑ n ∈ Finset.range k, w' n = intervalPartialSum w a k := by
    unfold w' intervalPartialSum
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    · intro n hn
      simp
  have hraw := Finset.sum_Ico_by_parts f w' hab
  rw [hprefix b hab.le, hprefix a le_rfl] at hraw
  have hsum :
      ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • ∑ i ∈ Finset.range (n + 1), w' i =
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    have han : a ≤ n := (Finset.mem_Ico.mp hn).1
    rw [hprefix (n + 1) (han.trans (Nat.le_succ n))]
  rw [hsum] at hraw
  simp only [intervalPartialSum, Finset.Ico_self, Finset.sum_empty, smul_zero,
    sub_zero] at hraw
  calc
    ∑ n ∈ Finset.Ico a b, f n • w n =
        ∑ n ∈ Finset.Ico a b, f n • w' n := by
      apply Finset.sum_congr rfl
      intro n hn
      have han : a ≤ n := (Finset.mem_Ico.mp hn).1
      simp [w', han]
    _ = _ := hraw

/-- Norm form of complex-coefficient Abel summation, retaining the exact
endpoint and total-variation factors. -/
theorem norm_sum_Ico_complex_smul_le_endpoint_add_variation
    (f w : ℕ → ℂ) {a b : ℕ} {B : ℝ}
    (hab : a < b)
    (hpartial : ∀ k, a < k → k ≤ b → ‖intervalPartialSum w a k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤
      ‖f (b - 1)‖ * B +
        ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ * B := by
  rw [sum_Ico_complex_smul_eq_endpoint_sub_differences f w hab]
  calc
    ‖f (b - 1) • intervalPartialSum w a b -
        ∑ n ∈ Finset.Ico a (b - 1),
          (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ ≤
        ‖f (b - 1) • intervalPartialSum w a b‖ +
          ‖∑ n ∈ Finset.Ico a (b - 1),
            (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ :=
      norm_sub_le _ _
    _ ≤ ‖f (b - 1)‖ * B +
        ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ * B := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hpartial b hab le_rfl) (norm_nonneg _)
      · calc
          ‖∑ n ∈ Finset.Ico a (b - 1),
              (f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ ≤
              ∑ n ∈ Finset.Ico a (b - 1),
                ‖(f (n + 1) - f n) • intervalPartialSum w a (n + 1)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ico a (b - 1),
                ‖f (n + 1) - f n‖ * B := by
            apply Finset.sum_le_sum
            intro n hn
            rw [norm_smul]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply hpartial (n + 1)
            · exact Nat.lt_succ_of_le (Finset.mem_Ico.mp hn).1
            · have hnTop := (Finset.mem_Ico.mp hn).2
              omega

/-- For a nonnegative monotone coefficient, Abel summation costs at most
twice its terminal value. -/
theorem norm_sum_Ico_smul_le_two_mul
    (f : ℕ → ℝ) (w : ℕ → ℂ) {a b : ℕ} {B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hf : Monotone f)
    (hfa : 0 ≤ f a)
    (hpartial : ∀ k, a < k → k ≤ b → ‖intervalPartialSum w a k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤ 2 * f b * B := by
  have hbPred : a ≤ b - 1 := by omega
  have hfbPred : 0 ≤ f (b - 1) := hfa.trans (hf hbPred)
  have hdiff (n : ℕ) : 0 ≤ f (n + 1) - f n :=
    sub_nonneg.mpr (hf (by omega))
  have hbase := norm_sum_Ico_smul_le_endpoint_add_variation
    f w hab hpartial
  rw [abs_of_nonneg hfbPred] at hbase
  simp_rw [abs_of_nonneg (hdiff _)] at hbase
  rw [← Finset.sum_mul, sum_Ico_forwardDifference f hbPred] at hbase
  have hfbPred_le : f (b - 1) ≤ f b := hf (by omega)
  calc
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤
        f (b - 1) * B + (f (b - 1) - f a) * B := hbase
    _ ≤ 2 * f b * B := by nlinarith

/-- For a nonnegative antitone coefficient on the summation interval, Abel
summation costs at most its value at the left endpoint. -/
theorem norm_sum_Ico_smul_le_left_of_antitone
    (f : ℕ → ℝ) (w : ℕ → ℂ) {a b : ℕ} {B : ℝ}
    (hab : a < b)
    (hfNonneg : ∀ n, a ≤ n → n ≤ b → 0 ≤ f n)
    (hfAnti : ∀ m n, a ≤ m → m ≤ n → n ≤ b → f n ≤ f m)
    (hpartial : ∀ k, a < k → k ≤ b → ‖intervalPartialSum w a k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤ f a * B := by
  have hbPred : a ≤ b - 1 := by omega
  have hbPredTop : b - 1 ≤ b := Nat.sub_le b 1
  have hfbPred : 0 ≤ f (b - 1) := hfNonneg (b - 1) hbPred hbPredTop
  have hdiff (n : ℕ) (hn : n ∈ Finset.Ico a (b - 1)) :
      f (n + 1) - f n ≤ 0 := by
    apply sub_nonpos.mpr
    apply hfAnti n (n + 1) (Finset.mem_Ico.mp hn).1 (by omega)
    have hnTop := (Finset.mem_Ico.mp hn).2
    omega
  have hvariation :
      ∑ n ∈ Finset.Ico a (b - 1), |f (n + 1) - f n| * B =
        (f a - f (b - 1)) * B := by
    calc
      ∑ n ∈ Finset.Ico a (b - 1), |f (n + 1) - f n| * B =
          ∑ n ∈ Finset.Ico a (b - 1), (f n - f (n + 1)) * B := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [abs_of_nonpos (hdiff n hn)]
        ring
      _ = (∑ n ∈ Finset.Ico a (b - 1), (f n - f (n + 1))) * B := by
        rw [Finset.sum_mul]
      _ = (f a - f (b - 1)) * B := by
        rw [sum_Ico_backwardDifference f hbPred]
  have hbase := norm_sum_Ico_smul_le_endpoint_add_variation
    f w hab hpartial
  rw [abs_of_nonneg hfbPred, hvariation] at hbase
  calc
    ‖∑ n ∈ Finset.Ico a b, f n • w n‖ ≤
        f (b - 1) * B + (f a - f (b - 1)) * B := hbase
    _ = f a * B := by ring

/-- Source-facing logarithmic specialization: an unweighted bound for every
initial subinterval gives the logarithmically weighted sum with only the
explicit factor `2 log b`. -/
theorem norm_sum_Ico_log_smul_le
    (w : ℕ → ℂ) {a b : ℕ} {B : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b → ‖intervalPartialSum w a k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, Real.log n • w n‖ ≤
      2 * Real.log b * B := by
  apply norm_sum_Ico_smul_le_two_mul (fun n => Real.log n) w hab hB
  · intro m n hmn
    by_cases hm : m = 0
    · subst m
      by_cases hn : n = 0
      · simp [hn]
      · have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
        simpa using Real.log_nonneg hnOneR
    · have hmPos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hnPos : (0 : ℝ) < n := hmPos.trans_le hmnR
      exact Real.strictMonoOn_log.monotoneOn hmPos hnPos hmnR
  · have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    exact Real.log_nonneg haR
  · exact hpartial

/-- Unweighted prime reciprocal-phase sum on a half-open natural interval.
Writing it as an indicator-weighted interval sum makes all of its initial
subintervals directly available to finite Abel summation. -/
def primeReciprocalPhaseSum
    (a b : ℕ) (N M : ℝ) (j : ℕ) : ℂ :=
  intervalPartialSum
    (fun n => if n.Prime then
      standardAdditiveCharacter (reciprocalPhase N M j n) else 0) a b

/-- The indicator definition is exactly the literal sum over primes. -/
theorem primeReciprocalPhaseSum_eq_filter
    (a b : ℕ) (N M : ℝ) (j : ℕ) :
    primeReciprocalPhaseSum a b N M j =
      ∑ n ∈ (Finset.Ico a b).filter Nat.Prime,
        standardAdditiveCharacter (reciprocalPhase N M j n) := by
  classical
  unfold primeReciprocalPhaseSum intervalPartialSum
  rw [← Finset.sum_filter]

/-- Prime-sum form of the source's absorption of the `j = 1` case into the
`j = 2, M = 0` case. -/
theorem primeReciprocalPhaseSum_one_eq_absorb
    (a b : ℕ) (N M : ℝ) :
    primeReciprocalPhaseSum a b N M 1 =
      primeReciprocalPhaseSum a b (N + M) 0 2 := by
  unfold primeReciprocalPhaseSum intervalPartialSum
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hnPrime : n.Prime
  · simp only [hnPrime, if_true]
    rw [reciprocalPhase_one_eq_absorb]
  · simp [hnPrime]

/-- The existing prime-logarithm phase sum on an interval is the
logarithmically weighted form of `primeReciprocalPhaseSum`. -/
theorem primeLogReciprocalPhaseSum_Ico_eq_log_smul
    (a b : ℕ) (N M : ℝ) (j : ℕ) :
    primeLogReciprocalPhaseSum (Finset.Ico a b) N M j =
      ∑ n ∈ Finset.Ico a b, Real.log n •
        (if n.Prime then
          standardAdditiveCharacter (reciprocalPhase N M j n) else 0) := by
  classical
  unfold primeLogReciprocalPhaseSum
  symm
  calc
    ∑ n ∈ Finset.Ico a b, Real.log n •
        (if n.Prime then
          standardAdditiveCharacter (reciprocalPhase N M j n) else 0) =
      ∑ n ∈ Finset.Ico a b, if n.Prime then
        Real.log n • standardAdditiveCharacter (reciprocalPhase N M j n) else 0 := by
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hnPrime : n.Prime <;> simp [hnPrime]
    _ = ∑ n ∈ (Finset.Ico a b).filter Nat.Prime,
        Real.log n • standardAdditiveCharacter (reciprocalPhase N M j n) := by
      rw [← Finset.sum_filter]
    _ = ∑ n ∈ (Finset.Ico a b).filter Nat.Prime,
        (Real.log n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      simp [real_smul]

/-- Exact source-facing reduction from uniform unweighted prime-phase bounds
on all initial subintervals to the logarithmically weighted prime sum. -/
theorem norm_primeLogReciprocalPhaseSum_Ico_le
    {a b : ℕ} (N M : ℝ) (j : ℕ) {B : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖primeReciprocalPhaseSum a k N M j‖ ≤ B) :
    ‖primeLogReciprocalPhaseSum (Finset.Ico a b) N M j‖ ≤
      2 * Real.log b * B := by
  rw [primeLogReciprocalPhaseSum_Ico_eq_log_smul]
  apply norm_sum_Ico_log_smul_le
    (w := fun n => if n.Prime then
      standardAdditiveCharacter (reciprocalPhase N M j n) else 0)
    ha hab hB
  intro k hak hkb
  simpa [primeReciprocalPhaseSum] using hpartial k hak hkb

/-- The reverse Abel-summation passage used in Proposition 1.12: uniform
bounds for logarithmically weighted prime sums on all initial subintervals
control the unweighted prime sum, with the explicit factor `1 / log a`. -/
theorem norm_primeReciprocalPhaseSum_Ico_le
    {a b : ℕ} (N M : ℝ) (j : ℕ) {B : ℝ}
    (ha : 2 ≤ a) (hab : a < b)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖primeLogReciprocalPhaseSum (Finset.Ico a k) N M j‖ ≤ B) :
    ‖primeReciprocalPhaseSum a b N M j‖ ≤
      (Real.log a)⁻¹ * B := by
  let w : ℕ → ℂ := fun n => Real.log n •
    (if n.Prime then standardAdditiveCharacter (reciprocalPhase N M j n) else 0)
  let f : ℕ → ℝ := fun n => (Real.log n)⁻¹
  have hgeneric := norm_sum_Ico_smul_le_left_of_antitone f w hab
    (fun n han _hnb => by
      dsimp only [f]
      have hnOne : 1 ≤ n := by omega
      have hnOneR : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
      exact inv_nonneg.mpr (Real.log_nonneg hnOneR))
    (fun m n ham hmn _hnb => by
      dsimp only [f]
      have hmTwo : 2 ≤ m := ha.trans ham
      have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hnPos : (0 : ℝ) < n := hmPos.trans_le hmnR
      have hmOneR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      have hlogm : 0 < Real.log m := Real.log_pos hmOneR
      have hlogle : Real.log m ≤ Real.log n :=
        Real.strictMonoOn_log.monotoneOn hmPos hnPos hmnR
      exact inv_anti₀ hlogm hlogle)
    (fun k hak hkb => by
      change ‖∑ n ∈ Finset.Ico a k, Real.log n •
        (if n.Prime then
          standardAdditiveCharacter (reciprocalPhase N M j n) else 0)‖ ≤ B
      rw [← primeLogReciprocalPhaseSum_Ico_eq_log_smul]
      exact hpartial k hak hkb)
  have hsum :
      primeReciprocalPhaseSum a b N M j =
        ∑ n ∈ Finset.Ico a b, f n • w n := by
    unfold primeReciprocalPhaseSum intervalPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnLower : a ≤ n := (Finset.mem_Ico.mp hn).1
    have hnTwo : 2 ≤ n := ha.trans hnLower
    have hnOneR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hnOneR)
    by_cases hnPrime : n.Prime
    · dsimp only [f, w]
      simp only [hnPrime, if_true, smul_smul]
      rw [inv_mul_cancel₀ hlog, one_smul]
    · dsimp only [f, w]
      simp [hnPrime]
  rw [hsum]
  simpa [f] using hgeneric

end

end Tao2026
