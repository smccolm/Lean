import GafniTao.SharpPerronLogDistance

/-!
# Additive-distance form of the Perron term bounds

The logarithmic denominator is converted without approximation.  At the
half-integral evaluation point the resulting denominator is uniformly at
least one half.
-/

namespace GafniTao

theorem norm_vonMangoldt_cutoffError_le_additive_of_natCast_lt
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : (n : ℝ) < x) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
        (Real.pi * T)) * (x / (x - (n : ℝ))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hInv := one_div_log_div_le_div_sub_of_pos_of_lt hnpos hnx
  have hfactor : 0 ≤
      ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
        (Real.pi * T) := by
    exact div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (div_pos hx hnpos).le c))
      (mul_nonneg Real.pi_pos.le hT.le)
  refine (norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_of_natCast_lt
    hc hT hx hn hnx).trans ?_
  calc
    ArithmeticFunction.vonMangoldt n *
          ((x / (n : ℝ)) ^ c /
            (Real.pi * T * Real.log (x / (n : ℝ)))) =
        (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
          (Real.pi * T)) * (1 / Real.log (x / (n : ℝ))) := by ring
    _ ≤ (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
          (Real.pi * T)) * (x / (x - (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hInv hfactor

theorem norm_vonMangoldt_cutoffError_le_additive_of_lt_natCast
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hxn : x < (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
        (Real.pi * T)) * ((n : ℝ) / ((n : ℝ) - x)) := by
  have hnpos : 0 < (n : ℝ) := hx.trans hxn
  have hInv := one_div_neg_log_div_le_div_sub_of_pos_of_lt hx hxn
  have hfactor : 0 ≤
      ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
        (Real.pi * T) := by
    exact div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (div_pos hx hnpos).le c))
      (mul_nonneg Real.pi_pos.le hT.le)
  refine (norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_of_lt_natCast
    hc hT hx hn hxn).trans ?_
  calc
    ArithmeticFunction.vonMangoldt n *
          ((x / (n : ℝ)) ^ c /
            (Real.pi * T * (-Real.log (x / (n : ℝ))))) =
        (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
          (Real.pi * T)) * (1 / (-Real.log (x / (n : ℝ)))) := by ring
    _ ≤ (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
          (Real.pi * T)) * ((n : ℝ) / ((n : ℝ) - x)) :=
      mul_le_mul_of_nonneg_left hInv hfactor

/-- Unified additive-distance bound at the half-integral evaluation point. -/
theorem norm_vonMangoldt_halfPoint_cutoffError_le_additive
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hn : 1 ≤ n) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel c T (sharpPerronHalfPoint x) n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff (sharpPerronHalfPoint x) n‖ ≤
      (ArithmeticFunction.vonMangoldt n *
          (sharpPerronHalfPoint x / (n : ℝ)) ^ c /
            (Real.pi * T)) *
        (max (sharpPerronHalfPoint x) (n : ℝ) /
          |sharpPerronHalfPoint x - (n : ℝ)|) := by
  have hy : 0 < sharpPerronHalfPoint x := sharpPerronHalfPoint_pos x
  have hne : sharpPerronHalfPoint x ≠ (n : ℝ) := by
    intro heq
    have hdist := half_le_abs_sharpPerronHalfPoint_sub_natCast x n
    rw [heq, sub_self, abs_zero] at hdist
    norm_num at hdist
  rcases lt_or_gt_of_ne hne with hyn | hny
  · rw [max_eq_right hyn.le, abs_of_nonpos (sub_nonpos.mpr hyn.le)]
    simpa only [neg_sub] using
      norm_vonMangoldt_cutoffError_le_additive_of_lt_natCast
        hc hT hy hn hyn
  · rw [max_eq_left hny.le, abs_of_nonneg (sub_nonneg.mpr hny.le)]
    exact norm_vonMangoldt_cutoffError_le_additive_of_natCast_lt
      hc hT hy hn hny

end GafniTao
