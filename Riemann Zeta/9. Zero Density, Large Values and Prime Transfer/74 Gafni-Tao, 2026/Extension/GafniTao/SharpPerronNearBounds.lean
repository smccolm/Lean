import GafniTao.SharpPerronHarmonic

/-!
# Near-diagonal Perron summands

This file controls a summand in the genuine resonant range `y/2 < n < 2y`.
The constant is explicit and depends only on `log 2`; no unspecified bounded
weight is introduced.
-/

namespace GafniTao

/-- Uniform power bound for ratios in `(0,2]` on the optimized line. -/
noncomputable def sharpPerronRatioBound : ℝ :=
  2 ^ (1 + 1 / Real.log 2)

theorem one_le_sharpPerronRatioBound : 1 ≤ sharpPerronRatioBound := by
  unfold sharpPerronRatioBound
  apply Real.one_le_rpow (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 < 1 / Real.log 2 := one_div_pos.mpr hlog
  linarith

theorem rpow_sharpPerronAbscissa_le_ratioBound
    {y q : ℝ} (hy : 2 ≤ y) (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    q ^ sharpPerronAbscissa y ≤ sharpPerronRatioBound := by
  by_cases hq : q ≤ 1
  · exact (Real.rpow_le_one hq0 hq
      (sharpPerronAbscissa_pos (by linarith)).le).trans
        one_le_sharpPerronRatioBound
  · have hq1 : 1 ≤ q := le_of_not_ge hq
    calc
      q ^ sharpPerronAbscissa y ≤
          2 ^ sharpPerronAbscissa y := by
            exact Real.rpow_le_rpow hq0 hq2
              (sharpPerronAbscissa_pos (by linarith)).le
      _ ≤ 2 ^ (1 + 1 / Real.log 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (sharpPerronAbscissa_le_logTwoConstant hy)
      _ = sharpPerronRatioBound := rfl

/-- Pointwise resonant-range estimate with the literal reciprocal-distance
kernel retained. -/
theorem norm_vonMangoldt_halfPoint_cutoffError_le_near
    {T x : ℝ} {n : ℕ}
    (hy : 2 ≤ sharpPerronHalfPoint x) (hT : 0 < T)
    (hn : 1 ≤ n)
    (hnLower : sharpPerronHalfPoint x / 2 < (n : ℝ))
    (hnUpper : (n : ℝ) < 2 * sharpPerronHalfPoint x) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel (sharpPerronAbscissa (sharpPerronHalfPoint x)) T
            (sharpPerronHalfPoint x) n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff (sharpPerronHalfPoint x) n‖ ≤
      (sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) *
          (2 * sharpPerronHalfPoint x) / (Real.pi * T)) *
        (1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by
  let y := sharpPerronHalfPoint x
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hratio0 : 0 ≤ y / (n : ℝ) := (div_pos hy0 hn0).le
  have hratio2 : y / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hn0]
    linarith
  have hpow :
      (y / (n : ℝ)) ^ sharpPerronAbscissa y ≤
        sharpPerronRatioBound :=
    rpow_sharpPerronAbscissa_le_ratioBound hy hratio0 hratio2
  have hLambda : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * y) := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    exact Real.log_le_log hn0 hnUpper.le
  have hmax : max y (n : ℝ) ≤ 2 * y := by
    exact max_le (by linarith) hnUpper.le
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hdist : 0 < |y - (n : ℝ)| := abs_pos.mpr (by
    intro heq
    have hhalf := half_le_abs_sharpPerronHalfPoint_sub_natCast x n
    change sharpPerronHalfPoint x - (n : ℝ) = 0 at heq
    rw [heq, abs_zero] at hhalf
    norm_num at hhalf)
  refine (norm_vonMangoldt_halfPoint_cutoffError_le_additive
    (sharpPerronAbscissa_pos (by linarith)) hT hn).trans ?_
  dsimp only [y] at hpow hLambda hmax ⊢
  have hLambda0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hlog0 : 0 ≤ Real.log (2 * sharpPerronHalfPoint x) := by
    exact Real.log_nonneg (by linarith)
  have hratioPow0 : 0 ≤
      (sharpPerronHalfPoint x / (n : ℝ)) ^
        sharpPerronAbscissa (sharpPerronHalfPoint x) :=
    Real.rpow_nonneg hratio0 _
  have hR0 : 0 ≤ sharpPerronRatioBound :=
    one_le_sharpPerronRatioBound.trans' (by norm_num)
  have hnum :
      ArithmeticFunction.vonMangoldt n *
          (sharpPerronHalfPoint x / (n : ℝ)) ^
            sharpPerronAbscissa (sharpPerronHalfPoint x) ≤
        sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) := by
    calc
      ArithmeticFunction.vonMangoldt n *
          (sharpPerronHalfPoint x / (n : ℝ)) ^
            sharpPerronAbscissa (sharpPerronHalfPoint x) ≤
        Real.log (2 * sharpPerronHalfPoint x) *
          sharpPerronRatioBound :=
            mul_le_mul hLambda hpow hratioPow0 hlog0
      _ = sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) := by ring
  have hfirst :
      ArithmeticFunction.vonMangoldt n *
            (sharpPerronHalfPoint x / (n : ℝ)) ^
              sharpPerronAbscissa (sharpPerronHalfPoint x) /
          (Real.pi * T) ≤
        sharpPerronRatioBound *
            Real.log (2 * sharpPerronHalfPoint x) /
          (Real.pi * T) :=
    div_le_div_of_nonneg_right hnum hpiT.le
  have hsecond :
      max (sharpPerronHalfPoint x) (n : ℝ) /
          |sharpPerronHalfPoint x - (n : ℝ)| ≤
        (2 * sharpPerronHalfPoint x) /
          |sharpPerronHalfPoint x - (n : ℝ)| :=
    div_le_div_of_nonneg_right hmax hdist.le
  calc
    (ArithmeticFunction.vonMangoldt n *
          (sharpPerronHalfPoint x / (n : ℝ)) ^
            sharpPerronAbscissa (sharpPerronHalfPoint x) /
          (Real.pi * T)) *
        (max (sharpPerronHalfPoint x) (n : ℝ) /
          |sharpPerronHalfPoint x - (n : ℝ)|) ≤
      (sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) /
          (Real.pi * T)) *
        ((2 * sharpPerronHalfPoint x) /
          |sharpPerronHalfPoint x - (n : ℝ)|) := by
            exact mul_le_mul hfirst hsecond
              (div_nonneg (hy0.le.trans (le_max_left _ _)) hdist.le)
              (div_nonneg (mul_nonneg hR0 hlog0) hpiT.le)
    _ = (sharpPerronRatioBound *
          Real.log (2 * sharpPerronHalfPoint x) *
          (2 * sharpPerronHalfPoint x) / (Real.pi * T)) *
        (1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by ring

end GafniTao
