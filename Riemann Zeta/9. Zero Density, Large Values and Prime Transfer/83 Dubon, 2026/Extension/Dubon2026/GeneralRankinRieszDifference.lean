import Dubon2026.GeneralRankinDualDifference

/-! # The exact general-level Riesz error difference estimate -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The literal general-level Riesz error difference is its quadratic pole contribution plus the genuine finite dual difference. -/
theorem general_rankinConvolutionRieszError_difference_dual {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {y h : ℝ} (hy : 0 < y) (hh : 0 ≤ h) :
    (rieszSecondDifference (rankinConvolutionRieszError f) y h : ℂ) =
      -rankinConvolutionEntireNumerator f 0 * (h : ℂ) ^ 2 +
        (generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
          generalRankinGammaDualSeries f y) := by
  rw [rieszSecondDifference]
  push_cast
  rw [general_rankinConvolutionRieszError_eq_dual f hk (by linarith : 0 < y + 2 * h),
    general_rankinConvolutionRieszError_eq_dual f hk (by linarith : 0 < y + h),
    general_rankinConvolutionRieszError_eq_dual f hk hy]
  push_cast
  ring

/-- Normalizing the actual error difference retains the true zero-pole value and finite dual-series bound. -/
theorem general_rankinConvolutionRieszError_difference_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |rieszSecondDifference (rankinConvolutionRieszError f) y h| / h ^ 2 ≤
      ‖rankinConvolutionEntireNumerator f 0‖ +
        ‖generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
          generalRankinGammaDualSeries f y‖ / h ^ 2 := by
  have he := general_rankinConvolutionRieszError_difference_dual f hk hy hh.le
  have hn : |rieszSecondDifference (rankinConvolutionRieszError f) y h| ≤
      ‖rankinConvolutionEntireNumerator f 0‖ * h ^ 2 +
        ‖generalRankinGammaDualSeries f (y + 2 * h) - 2 * generalRankinGammaDualSeries f (y + h) +
          generalRankinGammaDualSeries f y‖ := by
    calc
      _ = ‖(rieszSecondDifference (rankinConvolutionRieszError f) y h : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by
        rw [he]
        convert norm_add_le _ _ using 1
        simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply (div_le_div_of_nonneg_right hn (sq_nonneg h)).trans_eq
  field_simp [hh.ne']

/-- The original general-level Riesz error has the exact three-fifths normalized difference bound at both unsmoothing base points. -/
theorem exists_general_rankinConvolutionRieszError_three_fifths_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      |rieszSecondDifference (rankinConvolutionRieszError f) y (x ^ (3 / 5 : ℝ))| /
        (x ^ (3 / 5 : ℝ)) ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_generalRankinGammaDualSeries_shifted_three_fifths_bound f hk
  refine ⟨‖rankinConvolutionEntireNumerator f 0‖ + C, by positivity, ?_⟩
  intro x y hx hy hyx hhy
  have hx0 : 0 < x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 (3 / 5 : ℝ)
  have hd := general_rankinConvolutionRieszError_difference_bound f hk hy hh
  have hg := hb x y hx hy hyx hhy
  have hz : ‖rankinConvolutionEntireNumerator f 0‖ ≤
      ‖rankinConvolutionEntireNumerator f 0‖ * x ^ (3 / 5 : ℝ) :=
    le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hx (by norm_num))
  exact hd.trans ((add_le_add hz hg).trans_eq (by ring))

end
end Dubon2026
