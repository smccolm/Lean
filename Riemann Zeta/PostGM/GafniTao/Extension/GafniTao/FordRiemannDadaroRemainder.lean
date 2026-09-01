import GafniTao.FordRiemannDadaroPhaseBounds

/-!
# Quantitative remainder for Ford's ordinary-zeta truncation

The cutoff `floor t + 1/2` may lie below `t`, so the comparison with
`t ^ (-sigma)` carries an explicit factor at most two.  This file records
that loss rather than importing the sharper bound for the distinct Hurwitz
cutoff.
-/

open Complex

namespace GafniTao

noncomputable section

theorem fordRiemannDadaroCutoff_negPower_le_two_mul
    {sigma t : ℝ} (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ t) :
    fordRiemannDadaroCutoff t ^ (-sigma) ≤ 2 * t ^ (-sigma) := by
  have htPos : 0 < t := by linarith
  have hcutPos : 0 < fordRiemannDadaroCutoff t :=
    fordRiemannDadaroCutoff_pos t
  have hcutLower : t / 2 ≤ fordRiemannDadaroCutoff t := by
    linarith [t_sub_half_lt_fordRiemannDadaroCutoff t]
  have hhalfPos : 0 < t / 2 := by positivity
  have hpow : (t / 2) ^ sigma ≤ fordRiemannDadaroCutoff t ^ sigma :=
    Real.rpow_le_rpow hhalfPos.le hcutLower hsigmaLower
  have hinv :
      (fordRiemannDadaroCutoff t ^ sigma)⁻¹ ≤ ((t / 2) ^ sigma)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hhalfPos sigma) hpow
  have htwo : (2 : ℝ) ^ sigma ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      hsigmaUpper
  rw [← Real.rpow_neg hcutPos.le, ← Real.rpow_neg hhalfPos.le] at hinv
  calc
    fordRiemannDadaroCutoff t ^ (-sigma) ≤ (t / 2) ^ (-sigma) := hinv
    _ = (2 : ℝ) ^ sigma * t ^ (-sigma) := by
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [show -(sigma) = -sigma by rfl]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
      rw [div_eq_mul_inv]
      rw [inv_inv]
      ring
    _ ≤ 2 * t ^ (-sigma) := by
      gcongr

set_option maxHeartbeats 800000 in
theorem norm_riemannZeta_sub_fordPartialSum_le_thirty
    {sigma t : ℝ} (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) -
        (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
          (n : ℂ) ^ (-fordComplexHeight sigma t))‖ ≤
      30 * t ^ (-sigma) := by
  have htPos : 0 < t := by linarith
  have hcutPos : 0 < fordRiemannDadaroCutoff t :=
    fordRiemannDadaroCutoff_pos t
  have hcutOne : 1 ≤ fordRiemannDadaroCutoff t := by
    linarith [t_sub_half_lt_fordRiemannDadaroCutoff t]
  obtain ⟨E, hEq, hE⟩ :=
    riemannZeta_eq_fordPartialSum_sub_terms hsigmaLower ht
  let psum : ℂ :=
    ∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
      (n : ℂ) ^ (-fordComplexHeight sigma t)
  let main : ℂ :=
    ((fordRiemannDadaroCutoff t : ℂ) ^ (1 - fordComplexHeight sigma t)) /
      (1 - fordComplexHeight sigma t)
  let boundary : ℂ :=
    RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff
        (fordComplexHeight sigma t) (fordRiemannDadaroCutoff t) *
      ((fordRiemannDadaroCutoff t : ℂ) ^ (-fordComplexHeight sigma t))
  have hDiff :
      riemannZeta (fordComplexHeight sigma t) - psum = -main - boundary + E := by
    dsimp only [psum, main, boundary]
    linear_combination hEq
  have hDen :
      t ≤ ‖(1 : ℂ) - fordComplexHeight sigma t‖ := by
    calc
      t = |((1 : ℂ) - fordComplexHeight sigma t).im| := by
        simp [fordComplexHeight, abs_of_pos htPos]
      _ ≤ ‖(1 : ℂ) - fordComplexHeight sigma t‖ := abs_im_le_norm _
  have hDenPos : 0 < ‖(1 : ℂ) - fordComplexHeight sigma t‖ :=
    htPos.trans_le hDen
  have hcutUpper := fordRiemannDadaroCutoff_le_add_half htPos.le
  have hratio :
      fordRiemannDadaroCutoff t /
          ‖(1 : ℂ) - fordComplexHeight sigma t‖ ≤ 3 / 2 := by
    rw [div_le_iff₀ hDenPos]
    nlinarith
  have hPowSplit :
      fordRiemannDadaroCutoff t ^ (1 - sigma) =
        fordRiemannDadaroCutoff t * fordRiemannDadaroCutoff t ^ (-sigma) := by
    rw [show 1 - sigma = 1 + (-sigma) by ring,
      Real.rpow_add hcutPos, Real.rpow_one]
  have hMain : ‖main‖ ≤
      (3 / 2 : ℝ) * fordRiemannDadaroCutoff t ^ (-sigma) := by
    dsimp only [main]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hcutPos]
    simp only [one_re, sub_re]
    rw [show (fordComplexHeight sigma t).re = sigma by simp [fordComplexHeight],
      hPowSplit]
    calc
      fordRiemannDadaroCutoff t * fordRiemannDadaroCutoff t ^ (-sigma) /
          ‖(1 : ℂ) - fordComplexHeight sigma t‖ =
          (fordRiemannDadaroCutoff t /
            ‖(1 : ℂ) - fordComplexHeight sigma t‖) *
              fordRiemannDadaroCutoff t ^ (-sigma) := by ring
      _ ≤ (3 / 2 : ℝ) * fordRiemannDadaroCutoff t ^ (-sigma) :=
        mul_le_mul_of_nonneg_right hratio
          (Real.rpow_nonneg hcutPos.le _)
  have hBoundary : ‖boundary‖ ≤
      4 * fordRiemannDadaroCutoff t ^ (-sigma) := by
    dsimp only [boundary]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hcutPos]
    simp only [neg_re]
    rw [show (fordComplexHeight sigma t).re = sigma by simp [fordComplexHeight]]
    exact mul_le_mul_of_nonneg_right
      (fordRiemannDadaroBoundaryCoeff_le_four ht)
      (Real.rpow_nonneg hcutPos.le _)
  have hError : ‖E‖ ≤ 9 * fordRiemannDadaroCutoff t ^ (-sigma) := by
    calc
      ‖E‖ ≤
          RiemannZeta.GuthMaynard.sharpZetaErrorCoeff
              (fordComplexHeight sigma t) (fordRiemannDadaroCutoff t) /
            fordRiemannDadaroCutoff t ^ (sigma + 1) := hE
      _ ≤ 9 / fordRiemannDadaroCutoff t ^ (sigma + 1) := by
        gcongr
        exact fordRiemannDadaroErrorCoeff_le_nine hsigmaLower hsigmaUpper ht
      _ = 9 * fordRiemannDadaroCutoff t ^ (-(sigma + 1)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hcutPos.le]
      _ ≤ 9 * fordRiemannDadaroCutoff t ^ (-sigma) := by
        gcongr
        linarith
  rw [hDiff]
  calc
    ‖-main - boundary + E‖ ≤ ‖main‖ + ‖boundary‖ + ‖E‖ := by
      calc
        _ ≤ ‖-main - boundary‖ + ‖E‖ := norm_add_le _ _
        _ ≤ (‖-main‖ + ‖boundary‖) + ‖E‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = ‖main‖ + ‖boundary‖ + ‖E‖ := by rw [norm_neg]
    _ ≤ (3 / 2 : ℝ) * fordRiemannDadaroCutoff t ^ (-sigma) +
          4 * fordRiemannDadaroCutoff t ^ (-sigma) +
          9 * fordRiemannDadaroCutoff t ^ (-sigma) := by gcongr
    _ = (29 / 2 : ℝ) * fordRiemannDadaroCutoff t ^ (-sigma) := by ring
    _ ≤ (29 / 2 : ℝ) * (2 * t ^ (-sigma)) := by
      gcongr
      exact fordRiemannDadaroCutoff_negPower_le_two_mul
        hsigmaLower hsigmaUpper ht
    _ ≤ 30 * t ^ (-sigma) := by
      have hp := Real.rpow_nonneg htPos.le (-sigma)
      nlinarith

#print axioms fordRiemannDadaroCutoff_negPower_le_two_mul
#print axioms norm_riemannZeta_sub_fordPartialSum_le_thirty

end

end GafniTao
