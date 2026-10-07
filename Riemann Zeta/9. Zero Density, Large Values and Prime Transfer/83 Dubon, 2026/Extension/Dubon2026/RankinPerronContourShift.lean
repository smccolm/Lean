import Dubon2026.RankinPerronCutoffs

/-! # The genuine Rankin Perron contour shift including both exact residues -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The exact normalization of an arbitrary rectangle integral in terms of its actual symmetric vertical cutoffs. -/
theorem rectangleIntegral'_symmetric_vertical_formula (F : ℂ → ℂ) (a b T : ℝ) :
    RectangleIntegral' F ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
      ((1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, F ((b : ℂ) + t * I)) -
      ((1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, F ((a : ℂ) + t * I)) -
      (1 / (2 * Real.pi) : ℝ) • (I * (HIntegral F a b (-T) - HIntegral F a b T)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [RectangleIntegral', RectangleIntegral, VIntegral, smul_eq_mul, Complex.real_smul,
    sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, zero_sub, add_zero, zero_add]
  push_cast
  field_simp [hp, I_ne_zero]
  ring_nf
  simp [I_sq, sub_eq_add_neg]

/-- The actual finite Rankin Perron shift retains both residues and both oriented horizontal edges. -/
theorem rankinPerronVerticalCutoff_shift {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {x T : ℝ} (hx : 0 < x) (hT : 0 < T) :
    rankinPerronVerticalCutoff f x (9 / 8) T - rankinPerronVerticalCutoff f x (-1 / 8) T =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 +
      (1 / (2 * Real.pi) : ℝ) • (I *
        (HIntegral (rankinPerronContinuation f x) (-1 / 8) (9 / 8) (-T) -
          HIntegral (rankinPerronContinuation f x) (-1 / 8) (9 / 8) T)) := by
  have hh := rankinPerron_rectangle_residues f hk hx hT
  have he := rectangleIntegral'_symmetric_vertical_formula (rankinPerronContinuation f x) (-1 / 8) (9 / 8) T
  norm_num only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, neg_div] at he hh ⊢
  rw [he] at hh
  simp only [rankinPerronVerticalCutoff, gammaVerticalPoint, ofReal_div, ofReal_neg,
    ofReal_ofNat, ofReal_one]
  linear_combination hh

/-- The actual left Perron contour converges to the original Riesz sum minus its exact two-pole contribution. -/
theorem tendsto_rankinPerronVerticalCutoff_left {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    Tendsto (rankinPerronVerticalCutoff f x (-1 / 8)) atTop
      (𝓝 ((rankinConvolutionRiesz f x : ℂ) -
        ((rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
          rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2))) := by
  have hright := tendsto_rankinPerronVerticalCutoff_right f (by omega : 0 ≤ k) hx
    (by norm_num : (1 : ℝ) < 9 / 8)
  obtain ⟨hupper, hlower⟩ := tendsto_rankinPerron_horizontal_zero f hk hx
  have hedge := ((hlower.sub hupper).const_mul I).const_smul (1 / (2 * Real.pi) : ℝ)
  simp only [sub_self, mul_zero, smul_zero] at hedge
  have ht := (hright.sub_const ((rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
      rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2)).sub hedge
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have he := rankinPerronVerticalCutoff_shift f (by omega : 0 < k) hx hT
  linear_combination he

end
end Dubon2026
