import DongWangWangZhang2026.MeanValueSmoothing

/-!
# Arithmetic smoothing for the actual summatory dilation

The second cutoff's floor-jump error is charged only while that cutoff is
active. This preserves uniformity in the dilation factor.
-/

namespace DongWangWangZhang2026

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The actual difference corresponding to two normalized partial sums. -/
def zetaSumDilation (t w x : ℝ) : ℂ := zetaSum x t - (w : ℂ) * zetaSum (x / w) t

/-- The corresponding difference of the actual logarithmic coefficients. -/
def logZetaSumDilation (t w x : ℝ) : ℂ :=
  logZetaSum x t - (w : ℂ) * logZetaSum (x / w) t

theorem zetaSumDilation_eq_zero_of_lt_one (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : x < 1) : zetaSumDilation t w x = 0 := by
  have hw0 : 0 < w := by linarith
  rw [zetaSumDilation, zetaSum_eq_zero_of_lt_one hx,
    zetaSum_eq_zero_of_lt_one ((div_lt_one hw0).mpr (hx.trans_le hw))]
  simp

theorem measurable_zetaSumDilation (t w : ℝ) : Measurable (zetaSumDilation t w) :=
  (measurable_zetaSum t).sub
    (measurable_const.mul ((measurable_zetaSum t).comp (measurable_id.div_const w)))

theorem norm_zetaSumDilation_le (t : ℝ) {w x : ℝ} (hw : 0 < w) (hx : 0 ≤ x) :
    ‖zetaSumDilation t w x‖ ≤ 2 * x := by
  have h := norm_sub_le (zetaSum x t) ((w : ℂ) * zetaSum (x / w) t)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le] at h
  calc
    _ ≤ ‖zetaSum x t‖ + w * ‖zetaSum (x / w) t‖ := h
    _ ≤ x + w * (x / w) := add_le_add (norm_zetaSum_le hx t)
      (mul_le_mul_of_nonneg_left (norm_zetaSum_le (div_nonneg hx hw.le) t) hw.le)
    _ = _ := by field_simp; ring

theorem norm_zetaSum_sub_le_of_mem_interval (t : ℝ) {a b u v : ℝ}
    (ha : 0 ≤ a) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    ‖zetaSum u t - zetaSum v t‖ ≤ b - a + 1 := by
  rcases le_total v u with hvu | huv
  · exact (norm_zetaSum_sub_le t (ha.trans hv.1) hvu).trans (by linarith [hu.2, hv.1])
  · rw [norm_sub_rev]
    exact (norm_zetaSum_sub_le t (ha.trans hu.1) huv).trans (by linarith [hv.2, hu.1])

/-- The second floor error vanishes once the rescaled cutoff is below one
throughout the cell. It must not be charged on every cell up to `x`. -/
theorem norm_zetaSumDilation_reciprocal_sub_le (t : ℝ) {x w a b u v : ℝ}
    (hx : 0 ≤ x) (hw : 1 ≤ w) (ha : 0 < a) (hab : a ≤ b)
    (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    ‖zetaSumDilation t w (x / u) - zetaSumDilation t w (x / v)‖ ≤
      (x / a - x / b + 1) +
        if a ≤ x / w then w * ((x / w) / a - (x / w) / b + 1) else 0 := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 ≤ x / w := div_nonneg hx hw0.le
  have hrec (z : ℝ) (hz : 0 ≤ z) (s : ℝ) (hs : s ∈ Set.Icc a b) :
      z / s ∈ Set.Icc (z / b) (z / a) :=
    ⟨div_le_div_of_nonneg_left hz (ha.trans_le hs.1) hs.2,
      div_le_div_of_nonneg_left hz ha hs.1⟩
  have hfirst := norm_zetaSum_sub_le_of_mem_interval t
    (div_nonneg hx (ha.le.trans hab)) (hrec x hx u hu) (hrec x hx v hv)
  have hsecond : w * ‖zetaSum ((x / w) / u) t - zetaSum ((x / w) / v) t‖ ≤
      if a ≤ x / w then w * ((x / w) / a - (x / w) / b + 1) else 0 := by
    by_cases hactive : a ≤ x / w
    · rw [if_pos hactive]
      exact mul_le_mul_of_nonneg_left (norm_zetaSum_sub_le_of_mem_interval t
        (div_nonneg hy0 (ha.le.trans hab)) (hrec (x / w) hy0 u hu)
          (hrec (x / w) hy0 v hv)) hw0.le
    · rw [if_neg hactive,
        zetaSum_eq_zero_of_lt_one ((div_lt_one (ha.trans_le hu.1)).mpr
          ((lt_of_not_ge hactive).trans_le hu.1)),
        zetaSum_eq_zero_of_lt_one ((div_lt_one (ha.trans_le hv.1)).mpr
          ((lt_of_not_ge hactive).trans_le hv.1))]
      simp
  have hid : zetaSumDilation t w (x / u) - zetaSumDilation t w (x / v) =
      (zetaSum (x / u) t - zetaSum (x / v) t) -
        (w : ℂ) * (zetaSum ((x / w) / u) t - zetaSum ((x / w) / v) t) := by
    simp only [zetaSumDilation, div_right_comm x u w, div_right_comm x v w]
    ring
  rw [hid]
  have hn := norm_sub_le (zetaSum (x / u) t - zetaSum (x / v) t)
    ((w : ℂ) * (zetaSum ((x / w) / u) t - zetaSum ((x / w) / v) t))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0.le] at hn
  exact hn.trans (add_le_add hfirst hsecond)

/-- Dilation commutes with the actual Mangoldt convolution. The shorter
cutoff is extended only through terms whose summatory factor is zero. -/
theorem logZetaSumDilation_eq_mangoldt_convolution (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 0 ≤ x) :
    logZetaSumDilation t w x = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSumDilation t w (x / d) := by
  classical
  have hw0 : 0 < w := by linarith
  have hy0 : 0 ≤ x / w := div_nonneg hx hw0.le
  have hcut :
      (∑ d ∈ Finset.Icc 1 ⌊x / w⌋₊,
        (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSum ((x / w) / d) t) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSum ((x / w) / d) t := by
    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (div_le_self hx hw)))
    intro d hd hdnot
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdcut : ⌊x / w⌋₊ < d := by
      simp only [Finset.mem_Icc, not_and] at hdnot
      exact lt_of_not_ge (hdnot hd1)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
    rw [zetaSum_eq_zero_of_lt_one ((div_lt_one hdpos).mpr ((Nat.floor_lt hy0).mp hdcut)), mul_zero]
  rw [logZetaSumDilation, logZetaSum_eq_mangoldt_convolution,
    logZetaSum_eq_mangoldt_convolution, hcut, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [zetaSumDilation, div_right_comm x (d : ℝ) w]
  ring

theorem norm_logZetaSumDilation_le_mangoldt_sum (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 0 ≤ x) :
    ‖logZetaSumDilation t w x‖ ≤
      ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
        ‖zetaSumDilation t w (x / n)‖ := by
  rw [logZetaSumDilation_eq_mangoldt_convolution t hw hx]
  have hnorm : (∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖(ArithmeticFunction.vonMangoldt d : ℂ) * zetaTerm t d * zetaSumDilation t w (x / d)‖) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt d *
        ‖zetaSumDilation t w (x / d)‖ := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [norm_mul, norm_mul, norm_zetaTerm t (Finset.mem_Icc.mp hd).1, mul_one,
      Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply (norm_sum_le _ _).trans_eq
  rw [hnorm]
  symm
  apply Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩)
  intro n hn hn'
  have hn1 : n = 1 := by
    have hm := Finset.mem_Icc.mp hn
    simp only [Finset.mem_Ioc, not_and] at hn'
    omega
  simp [hn1]

theorem norm_log_mul_zetaSum_sub_logZetaSum_le_nonneg (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖(Real.log x : ℂ) * zetaSum x t - logZetaSum x t‖ ≤ x := by
  by_cases hx1 : 1 ≤ x
  · exact norm_log_mul_zetaSum_sub_logZetaSum_le t hx1
  · rw [zetaSum_eq_zero_of_lt_one (lt_of_not_ge hx1),
      logZetaSum_eq_zero_of_lt_one (lt_of_not_ge hx1)]
    simpa using hx

/-- Removing the logarithmic weight from the actual difference costs only
`x (2+log w)`, uniformly in the height and including the inactive cutoff. -/
theorem norm_log_mul_zetaSumDilation_sub_logDilation_le (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 0 < x) :
    ‖(Real.log x : ℂ) * zetaSumDilation t w x - logZetaSumDilation t w x‖ ≤
      x * (2 + Real.log w) := by
  have hw0 : 0 < w := by linarith
  have hy0 : 0 ≤ x / w := div_nonneg hx.le hw0.le
  have hlw : 0 ≤ Real.log w := Real.log_nonneg hw
  let P := (Real.log x : ℂ) * zetaSum x t - logZetaSum x t
  let Q := (Real.log (x / w) : ℂ) * zetaSum (x / w) t - logZetaSum (x / w) t
  have hP : ‖P‖ ≤ x := norm_log_mul_zetaSum_sub_logZetaSum_le_nonneg t hx.le
  have hQ : ‖Q‖ ≤ x / w := norm_log_mul_zetaSum_sub_logZetaSum_le_nonneg t hy0
  have hid : (Real.log x : ℂ) * zetaSumDilation t w x - logZetaSumDilation t w x =
      (P - (w : ℂ) * Q) - ((w * Real.log w : ℝ) : ℂ) * zetaSum (x / w) t := by
    dsimp only [P, Q, zetaSumDilation, logZetaSumDilation]
    rw [Real.log_div hx.ne' hw0.ne']
    push_cast
    ring
  have hQw : ‖(w : ℂ) * Q‖ ≤ w * (x / w) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0.le]
    exact mul_le_mul_of_nonneg_left hQ hw0.le
  have hS : ‖((w * Real.log w : ℝ) : ℂ) * zetaSum (x / w) t‖ ≤
      (w * Real.log w) * (x / w) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hw0.le hlw)]
    exact mul_le_mul_of_nonneg_left (norm_zetaSum_le hy0 t) (mul_nonneg hw0.le hlw)
  rw [hid]
  calc
    _ ≤ ‖P - (w : ℂ) * Q‖ + ‖((w * Real.log w : ℝ) : ℂ) * zetaSum (x / w) t‖ :=
      norm_sub_le _ _
    _ ≤ (‖P‖ + ‖(w : ℂ) * Q‖) + ‖((w * Real.log w : ℝ) : ℂ) * zetaSum (x / w) t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (x + w * (x / w)) + (w * Real.log w) * (x / w) := add_le_add (add_le_add hP hQw) hS
    _ = _ := by field_simp; ring

theorem intervalIntegrable_zetaSumDilation_reciprocal_norm (t : ℝ) {x w a b : ℝ}
    (hx : 0 ≤ x) (hw : 0 < w) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ‖zetaSumDilation t w (x / u)‖) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply Measure.integrableOn_of_bounded (by simp)
    (((measurable_zetaSumDilation t w).comp
      (measurable_const.div measurable_id)).norm.aestronglyMeasurable) (M := 2 * x / a)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [norm_norm]
  calc
    _ ≤ 2 * (x / u) := norm_zetaSumDilation_le t hw (div_nonneg hx (ha.le.trans hu.1))
    _ ≤ 2 * (x / a) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hx ha hu.1) (by norm_num)
    _ = _ := by ring

/-- Cell averaging retains the difference inside the integral. -/
theorem zetaSumDilation_reciprocal_le_cell_average (t : ℝ) {x w a b v : ℝ}
    (hx : 0 ≤ x) (hw : 1 ≤ w) (ha : 0 < a) (hab : a < b) (hv : v ∈ Set.Icc a b) :
    (b - a) * ‖zetaSumDilation t w (x / v)‖ ≤
      (∫ u : ℝ in a..b, ‖zetaSumDilation t w (x / u)‖) +
        (b - a) * ((x / a - x / b + 1) +
          if a ≤ x / w then w * ((x / w) / a - (x / w) / b + 1) else 0) := by
  have hw0 : 0 < w := by linarith
  have hfi := intervalIntegrable_zetaSumDilation_reciprocal_norm t hx hw0 ha hab.le
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc a b) :
      ‖zetaSumDilation t w (x / v)‖ ≤ ‖zetaSumDilation t w (x / u)‖ +
        ((x / a - x / b + 1) +
          if a ≤ x / w then w * ((x / w) / a - (x / w) / b + 1) else 0) := by
    have hvar := norm_zetaSumDilation_reciprocal_sub_le t hx hw ha hab.le hv hu
    have hn := norm_sub_norm_le (zetaSumDilation t w (x / v)) (zetaSumDilation t w (x / u))
    linarith
  have h := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (hfi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul] using h

/-- The proved sieve mass controls the difference on a quartic cell, with
the second cutoff's variation charged only on active cells. -/
theorem sum_mangoldt_zetaSumDilation_quarticCell_le (t x w : ℝ) (k : ℕ)
    (hx : 0 ≤ x) (hw : 1 ≤ w) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖) ≤
      2048 * (∫ u : ℝ in (k : ℝ) ^ 4..((k : ℝ) + 1) ^ 4,
        ‖zetaSumDilation t w (x / u)‖) +
          2048 * (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
            ((x / (k : ℝ) ^ 4 - x / ((k : ℝ) + 1) ^ 4 + 1) +
              if (k : ℝ) ^ 4 ≤ x / w then
                w * ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1) else 0) := by
  let a : ℝ := (k : ℝ) ^ 4
  let b : ℝ := ((k : ℝ) + 1) ^ 4
  let J := ∫ u : ℝ in a..b, ‖zetaSumDilation t w (x / u)‖
  let E := (x / a - x / b + 1) +
    if a ≤ x / w then w * ((x / w) / a - (x / w) / b + 1) else 0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast (Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by decide : 4 ≠ 0))
  have hlen : (k : ℝ) ^ 3 ≤ b - a := by dsimp [a, b]; nlinarith
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => norm_nonneg _)
  have hw0 : 0 ≤ w := by linarith
  have hE : 0 ≤ E := by
    have hfirst : 0 ≤ x / a - x / b + 1 := by
      linarith [div_le_div_of_nonneg_left hx ha hab.le]
    have hsecond : 0 ≤ (x / w) / a - (x / w) / b + 1 := by
      linarith [div_le_div_of_nonneg_left (div_nonneg hx hw0) ha hab.le]
    dsimp only [E]
    split_ifs <;> positivity
  have hmass := (sum_mangoldt_quarticCell_le_uniform k hk).trans
    (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 2048))
  have hsum := Finset.sum_le_sum (s := Finset.Ioc (k ^ 4) ((k + 1) ^ 4))
    (fun n hn => mul_le_mul_of_nonneg_left
      (zetaSumDilation_reciprocal_le_cell_average t hx hw ha hab
        (show (n : ℝ) ∈ Set.Icc a b from by
          have hmem := Finset.mem_Ioc.mp hn
          constructor
          · dsimp [a]; exact_mod_cast hmem.1.le
          · dsimp [b]; exact_mod_cast hmem.2)) (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
  change (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ((b - a) * ‖zetaSumDilation t w (x / n)‖)) ≤
    ∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4), ArithmeticFunction.vonMangoldt n *
      (J + (b - a) * E) at hsum
  simp_rw [← mul_assoc, mul_comm (ArithmeticFunction.vonMangoldt _) (b - a), mul_assoc] at hsum
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hmass (show 0 ≤ J + (b - a) * E by positivity)
  have hfinal : (b - a) * (∑ n ∈ Finset.Ioc (k ^ 4) ((k + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖) ≤
      (b - a) * (2048 * J + 2048 * (b - a) * E) := by
    calc
      _ ≤ _ := hsum.trans hm
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp hfinal

theorem sum_quarticCell_variation_cost_le (x : ℝ) (K : ℕ) (hx : 0 ≤ x) :
    (∑ k ∈ Finset.Icc 1 K, (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
      (x / (k : ℝ) ^ 4 - x / ((k : ℝ) + 1) ^ 4 + 1)) ≤
        450 * x + 15 * (K : ℝ) ^ 4 := by
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 K) (fun k hk =>
    quarticCell_variation_cost_le x k hx (by exact_mod_cast (Finset.mem_Icc.mp hk).1))
  have hinv : (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have hset : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_Icc]
      omega
    simpa only [hset, Nat.cast_zero, zero_add, div_one] using
      (sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1))
  have hcubes : (∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ 3) ≤ (K : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ _ ∈ Finset.Icc 1 K, (K : ℝ) ^ 3 := Finset.sum_le_sum (fun k hk =>
        pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (Finset.mem_Icc.mp hk).2) 3)
      _ = _ := by simp; ring
  apply hsum.trans
  simp_rw [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hinv (show 0 ≤ 225 * x by positivity)]

/-- Only cells below the rescaled cutoff contribute its floor error. The
total is linear in the original cutoff, independently of the dilation. -/
theorem sum_active_quarticCell_variation_cost_le (x w : ℝ) (K : ℕ)
    (hx : 0 ≤ x) (hw : 1 ≤ w) :
    (∑ k ∈ Finset.Icc 1 K, if (k : ℝ) ^ 4 ≤ x / w then
      w * ((((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
        ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1)) else 0) ≤
      465 * x := by
  have hw0 : 0 < w := by linarith
  have hy : 0 ≤ x / w := div_nonneg hx hw0.le
  by_cases hy1 : 1 ≤ x / w
  · obtain ⟨J, _, hJ, hcover⟩ := exists_quarticCell_cover hy1
    let V (k : ℕ) : ℝ := (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
      ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1)
    have hV (k : ℕ) (hk : 1 ≤ k) : 0 ≤ V k := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hpow : (k : ℝ) ^ 4 ≤ ((k : ℝ) + 1) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have hdiv := div_le_div_of_nonneg_left hy (by positivity : 0 < (k : ℝ) ^ 4) hpow
      dsimp only [V]
      exact mul_nonneg (sub_nonneg.mpr hpow) (by linarith)
    have hsub : (Finset.Icc 1 K).filter (fun k : ℕ => (k : ℝ) ^ 4 ≤ x / w) ⊆ Finset.Icc 1 J := by
      intro k hk
      obtain ⟨hk, hactive⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, ?_⟩
      by_contra hnot
      have hkj : J + 1 ≤ k := by omega
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ J + 1)
        (show (J : ℝ) + 1 ≤ k by exact_mod_cast hkj) 4
      linarith
    have hs : (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => (k : ℝ) ^ 4 ≤ x / w), w * V k) ≤
        ∑ k ∈ Finset.Icc 1 J, w * V k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk _
      exact mul_nonneg hw0.le (hV k (Finset.mem_Icc.mp hk).1)
    rw [Finset.sum_filter] at hs
    change (∑ k ∈ Finset.Icc 1 K, if (k : ℝ) ^ 4 ≤ x / w then w * V k else 0) ≤ _
    apply hs.trans
    rw [← Finset.mul_sum]
    have hcost := mul_le_mul_of_nonneg_left (sum_quarticCell_variation_cost_le (x / w) J hy) hw0.le
    have hJw := mul_le_mul_of_nonneg_left hJ hw0.le
    have hcancel : w * (x / w) = x := mul_div_cancel₀ x hw0.ne'
    dsimp only [V]
    nlinarith
  · have hzero : (∑ k ∈ Finset.Icc 1 K, if (k : ℝ) ^ 4 ≤ x / w then
        w * ((((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hp : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hkR
      rw [if_neg (by linarith)]
    rw [hzero]
    positivity

theorem sum_quarticCell_dilation_integrals (t x w : ℝ) (K : ℕ)
    (hx : 0 ≤ x) (hw : 0 < w) :
    (∑ k ∈ Finset.Icc 1 K,
      ∫ u : ℝ in (k : ℝ) ^ 4..((k : ℝ) + 1) ^ 4, ‖zetaSumDilation t w (x / u)‖) =
      ∫ u : ℝ in 1..((K : ℝ) + 1) ^ 4, ‖zetaSumDilation t w (x / u)‖ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact intervalIntegrable_zetaSumDilation_reciprocal_norm t hx hw (by norm_num)
        (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) K] : (1 : ℝ) ≤ K + 1))
    · exact intervalIntegrable_zetaSumDilation_reciprocal_norm t hx hw (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 4)

/-- Sieve smoothing for the actual difference, with a dilation-independent
arithmetic error. -/
theorem sum_mangoldt_zetaSumDilation_quarticPrefix_le (t x w : ℝ) (K : ℕ)
    (hx : 0 ≤ x) (hw : 1 ≤ w) :
    (∑ n ∈ Finset.Ioc 1 ((K + 1) ^ 4),
      ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖) ≤
      2048 * (∫ u : ℝ in 1..((K : ℝ) + 1) ^ 4, ‖zetaSumDilation t w (x / u)‖) +
        2048 * (915 * x + 15 * (K : ℝ) ^ 4) := by
  have hw0 : 0 < w := by linarith
  rw [← sum_quarticCells]
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 K) (fun k hk =>
    (sum_mangoldt_zetaSumDilation_quarticCell_le t x w k hx hw (Finset.mem_Icc.mp hk).1).trans_eq
      (show _ = 2048 * (∫ u : ℝ in (k : ℝ) ^ 4..((k : ℝ) + 1) ^ 4,
          ‖zetaSumDilation t w (x / u)‖) +
        2048 * ((((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          (x / (k : ℝ) ^ 4 - x / ((k : ℝ) + 1) ^ 4 + 1)) +
        2048 * (if (k : ℝ) ^ 4 ≤ x / w then
          w * ((((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
            ((x / w) / (k : ℝ) ^ 4 - (x / w) / ((k : ℝ) + 1) ^ 4 + 1)) else 0) from by
        split_ifs <;> ring))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_quarticCell_dilation_integrals t x w K hx hw0] at hsum
  have hfirst := sum_quarticCell_variation_cost_le x K hx
  have hsecond := sum_active_quarticCell_variation_cost_le x w K hx hw
  linarith

theorem integral_zetaSumDilation_reciprocal_eq_of_cutoff (t : ℝ) {w x B : ℝ}
    (hw : 1 ≤ w) (hx : 1 ≤ x) (hB : x ≤ B) :
    (∫ u : ℝ in 1..B, ‖zetaSumDilation t w (x / u)‖) =
      ∫ u : ℝ in 1..x, ‖zetaSumDilation t w (x / u)‖ := by
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := by linarith
  have htail : (∫ u : ℝ in x..B, ‖zetaSumDilation t w (x / u)‖) = 0 := by
    rw [intervalIntegral.integral_of_le hB]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [zetaSumDilation_eq_zero_of_lt_one t hw ((div_lt_one (hx0.trans hu.1)).mpr hu.1), norm_zero]
    rfl
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_zetaSumDilation_reciprocal_norm t hx0.le hw0 (by norm_num) hx)
    (intervalIntegrable_zetaSumDilation_reciprocal_norm t hx0.le hw0 hx0 hB)
  rw [htail, add_zero] at h
  exact h.symm

theorem sum_mangoldt_zetaSumDilation_le_integral (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖) ≤
      2048 * (∫ u : ℝ in 1..x, ‖zetaSumDilation t w (x / u)‖) + 1904640 * x := by
  obtain ⟨K, _, hK, hcover⟩ := exists_quarticCell_cover hx
  have hN : ⌊x⌋₊ ≤ (K + 1) ^ 4 := by
    apply Nat.le_of_lt
    apply (Nat.floor_lt (zero_le_one.trans hx)).mpr
    exact_mod_cast hcover
  have hsub : (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖) ≤
      ∑ n ∈ Finset.Ioc 1 ((K + 1) ^ 4),
        ArithmeticFunction.vonMangoldt n * ‖zetaSumDilation t w (x / n)‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hN)
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (norm_nonneg _)
  have h := hsub.trans (sum_mangoldt_zetaSumDilation_quarticPrefix_le t x w K
    (zero_le_one.trans hx) hw)
  rw [integral_zetaSumDilation_reciprocal_eq_of_cutoff t hw hx hcover.le] at h
  linarith

theorem norm_zetaSumDilation_mul_log_le_reciprocal_integral (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 1 ≤ x) :
    ‖zetaSumDilation t w x‖ * Real.log x ≤
      2048 * (∫ u : ℝ in 1..x, ‖zetaSumDilation t w (x / u)‖) +
        x * (1904642 + Real.log w) := by
  have herror := norm_log_mul_zetaSumDilation_sub_logDilation_le t hw (by linarith : 0 < x)
  have hnorm := norm_sub_norm_le ((Real.log x : ℂ) * zetaSumDilation t w x)
    (logZetaSumDilation t w x)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx)] at hnorm
  have hsum := (norm_logZetaSumDilation_le_mangoldt_sum t hw (zero_le_one.trans hx)).trans
    (sum_mangoldt_zetaSumDilation_le_integral t hw hx)
  nlinarith

theorem integral_zetaSumDilation_reciprocal_eq_exp (t w : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ u : ℝ in 1..x, ‖zetaSumDilation t w (x / u)‖) =
      x * ∫ v : ℝ in 0..Real.log x, Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖ := by
  have hx0 : 0 < x := by linarith
  have hf : ContinuousOn (fun v : ℝ => x * Real.exp (-v)) (Set.uIcc 0 (Real.log x)) :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).continuousOn
  have hd (v : ℝ) : HasDerivAt (fun v : ℝ => x * Real.exp (-v)) (-x * Real.exp (-v)) v := by
    convert ((Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_neg v)).const_mul x using 1
    ring
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun u : ℝ => ‖zetaSumDilation t w (x / u)‖) hf (fun v _ => hd v)
    (fun v _ => by have he := Real.exp_pos (-v); nlinarith)
  have htop : x * Real.exp (-Real.log x) = 1 := by rw [Real.exp_neg, Real.exp_log hx0]; field_simp
  simp only [neg_zero, Real.exp_zero, mul_one, htop, Function.comp_def] at h
  have hfun (v : ℝ) : ‖zetaSumDilation t w (x / (x * Real.exp (-v)))‖ * (-x * Real.exp (-v)) =
      -(x * (Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖)) := by
    rw [Real.exp_neg, div_mul_cancel_left₀ hx0.ne', inv_inv]
    ring
  simp_rw [hfun] at h
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_symm 1 x] at h
  linarith

theorem intervalIntegrable_normalized_zetaSumDilation_exp (t a b : ℝ) {w : ℝ} (hw : 0 < w) :
    IntervalIntegrable (fun v : ℝ => Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖)
      volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (by simp)
    (((Real.measurable_exp.comp measurable_neg).mul
      ((measurable_zetaSumDilation t w).comp Real.measurable_exp).norm).aestronglyMeasurable) (M := 2)
  filter_upwards with v
  change ‖Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖‖ ≤ 2
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  calc
    _ ≤ Real.exp (-v) * (2 * Real.exp v) := mul_le_mul_of_nonneg_left
      (norm_zetaSumDilation_le t hw (Real.exp_pos v).le) (Real.exp_pos _).le
    _ = 2 := by rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← Real.exp_add]; simp

/-- Uniform pointwise smoothing for the actual two-cutoff difference. The
only dilation loss is logarithmic; no estimate of separate sums replaces it. -/
theorem norm_normalized_zetaSumDilation_le_log_average (t : ℝ) {w x : ℝ}
    (hw : 1 ≤ w) (hx : 1 < x) :
    ‖zetaSumDilation t w x‖ / x ≤
      2048 / Real.log x *
        (∫ v : ℝ in 0..Real.log x, Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖) +
          (1904642 + Real.log w) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  have h := norm_zetaSumDilation_mul_log_le_reciprocal_integral t hw hx.le
  rw [integral_zetaSumDilation_reciprocal_eq_exp t w hx.le] at h
  calc
    _ ≤ (2048 * (∫ v : ℝ in 0..Real.log x,
        Real.exp (-v) * ‖zetaSumDilation t w (Real.exp v)‖) +
          (1904642 + Real.log w)) / Real.log x :=
      (div_le_div_iff₀ hx0 hlog).mpr (by nlinarith)
    _ = _ := by ring

theorem zetaSumDilation_exp (t b u : ℝ) :
    zetaSumDilation t (Real.exp b) (Real.exp u) =
      zetaSum (Real.exp u) t - (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t := by
  rw [zetaSumDilation, Real.exp_sub]

theorem logZetaSumDilation_exp (t b u : ℝ) :
    logZetaSumDilation t (Real.exp b) (Real.exp u) =
      logZetaSum (Real.exp u) t - (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t := by
  rw [logZetaSumDilation, Real.exp_sub]

/-- The smoothing consumer has exactly the difference used in the proved
Laplace and Parseval formulas. -/
theorem norm_exp_dilation_le_log_average (t : ℝ) {b Y : ℝ} (hb : 0 ≤ b) (hY : 0 < Y) :
    Real.exp (-Y) * ‖zetaSum (Real.exp Y) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) t‖ ≤
      2048 / Y * (∫ u : ℝ in 0..Y, Real.exp (-u) *
        ‖zetaSum (Real.exp u) t - (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t‖) +
          (1904642 + b) / Y := by
  have h := norm_normalized_zetaSumDilation_le_log_average t (Real.one_le_exp hb)
    (Real.one_lt_exp_iff.mpr hY)
  simp only [Real.log_exp, zetaSumDilation_exp] at h
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using h

end
end DongWangWangZhang2026
