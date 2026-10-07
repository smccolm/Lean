import Dubon2026.RankinRieszDualIdentity
import Dubon2026.RankinDualShiftedOptimization

/-! # Actual full-level Riesz error differences with the exact three-fifths bound -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual Riesz error second difference consists precisely of the quadratic residue difference and the genuine dual-series difference. -/
theorem rankinConvolutionRieszError_difference_dual {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {y h : ℝ} (hy : 0 < y) (hh : 0 ≤ h) :
    (rieszSecondDifference (rankinConvolutionRieszError f) y h : ℂ) =
      -rankinConvolutionEntireNumerator f 0 * (h : ℂ) ^ 2 +
      ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
        (rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + 2 * h) -
          2 * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + h) +
          rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) y) := by
  rw [rieszSecondDifference]
  push_cast
  rw [rankinConvolutionRieszError_eq_dual f hk (by linarith : 0 < y + 2 * h),
    rankinConvolutionRieszError_eq_dual f hk (by linarith : 0 < y + h),
    rankinConvolutionRieszError_eq_dual f hk hy]
  push_cast
  ring

/-- The actual normalized Riesz error difference is bounded by the genuine zero-pole value and normalized dual difference. -/
theorem rankinConvolutionRieszError_difference_bound {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |rieszSecondDifference (rankinConvolutionRieszError f) y h| / h ^ 2 ≤
      ‖rankinConvolutionEntireNumerator f 0‖ + (4 * Real.pi ^ 2)⁻¹ *
        (‖rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + 2 * h) -
          2 * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + h) +
          rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) y‖ / h ^ 2) := by
  have he := rankinConvolutionRieszError_difference_dual f hk hy hh.le
  have hn : |rieszSecondDifference (rankinConvolutionRieszError f) y h| ≤
      ‖rankinConvolutionEntireNumerator f 0‖ * h ^ 2 + (4 * Real.pi ^ 2)⁻¹ *
        ‖rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + 2 * h) -
          2 * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) (y + h) +
          rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) y‖ := by
    calc
      _ = ‖(rieszSecondDifference (rankinConvolutionRieszError f) y h : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by
        rw [he]
        convert norm_add_le _ _ using 1
        simp only [norm_mul, norm_neg, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hh, abs_of_pos Real.pi_pos]
        norm_num
  apply (div_le_div_of_nonneg_right hn (sq_nonneg h)).trans_eq
  field_simp [hh.ne']

/-- The true full-level Riesz error has uniformly bounded normalized second differences at both unsmoothing base points. -/
theorem exists_rankinConvolutionRieszError_three_fifths_bound {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      |rieszSecondDifference (rankinConvolutionRieszError f) y (x ^ (3 / 5 : ℝ))| /
        (x ^ (3 / 5 : ℝ)) ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_rankinGammaDualSeries_shifted_three_fifths_bound f hk
    (show 0 < (4 * Real.pi ^ 2) ^ 2 by positivity)
  refine ⟨‖rankinConvolutionEntireNumerator f 0‖ + (4 * Real.pi ^ 2)⁻¹ * C, by positivity, ?_⟩
  intro x y hx hy hyx hhy
  have hx0 : 0 < x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 (3 / 5 : ℝ)
  have hd := rankinConvolutionRieszError_difference_bound f hk hy hh
  have hg := mul_le_mul_of_nonneg_left (hb x y hx hy hyx hhy)
    (show 0 ≤ (4 * Real.pi ^ 2)⁻¹ by positivity)
  have hz : ‖rankinConvolutionEntireNumerator f 0‖ ≤
      ‖rankinConvolutionEntireNumerator f 0‖ * x ^ (3 / 5 : ℝ) :=
    le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hx (by norm_num))
  exact hd.trans ((add_le_add hz hg).trans_eq (by ring))

end
end Dubon2026
