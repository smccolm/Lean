import GafniTao.FordDadaroPhaseBounds

/-!
# Quantitative Dadaro remainder at Ford's endpoint

The exact formula is converted to a single `15 * t^(-sigma)` norm bound.
The subsequent large-height module will absorb this into Ford's `10^-80`
constant.
-/

open Complex

namespace GafniTao

noncomputable section

set_option maxHeartbeats 800000 in
theorem norm_riemannZeta_sub_fordFiniteApproximation_le_fifteen
    {sigma t : ℝ} (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ t) :
    ‖riemannZeta (fordComplexHeight sigma t) -
        fordHurwitzFiniteApproximation sigma 1 t‖ ≤
      15 * t ^ (-sigma) := by
  have htPos : 0 < t := by linarith
  have htOne : 1 ≤ t := by linarith
  have hcutPos : 0 < fordDadaroCutoff t := fordDadaroCutoff_pos t
  have hcutOne : 1 ≤ fordDadaroCutoff t := by
    linarith [lt_fordDadaroCutoff t]
  obtain ⟨E, hEq, hE⟩ :=
    riemannZeta_eq_fordFiniteApproximation_sub_terms hsigmaLower ht
  let main : ℂ :=
    ((fordDadaroCutoff t : ℂ) ^ (1 - fordComplexHeight sigma t)) /
      (1 - fordComplexHeight sigma t)
  let boundary : ℂ :=
    RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff
        (fordComplexHeight sigma t) (fordDadaroCutoff t) *
      ((fordDadaroCutoff t : ℂ) ^ (-fordComplexHeight sigma t))
  have hDiff :
      riemannZeta (fordComplexHeight sigma t) -
          fordHurwitzFiniteApproximation sigma 1 t = -main - boundary + E := by
    dsimp only [main, boundary]
    linear_combination hEq
  have hDen :
      t ≤ ‖(1 : ℂ) - fordComplexHeight sigma t‖ := by
    calc
      t = |((1 : ℂ) - fordComplexHeight sigma t).im| := by
        simp [fordComplexHeight, abs_of_pos htPos]
      _ ≤ ‖(1 : ℂ) - fordComplexHeight sigma t‖ := abs_im_le_norm _
  have hDenPos : 0 < ‖(1 : ℂ) - fordComplexHeight sigma t‖ :=
    htPos.trans_le hDen
  have hcutUpper := fordDadaroCutoff_le_add htPos.le
  have hratio :
      fordDadaroCutoff t /
          ‖(1 : ℂ) - fordComplexHeight sigma t‖ ≤ 3 / 2 := by
    rw [div_le_iff₀ hDenPos]
    nlinarith
  have hPowSplit :
      fordDadaroCutoff t ^ (1 - sigma) =
        fordDadaroCutoff t * fordDadaroCutoff t ^ (-sigma) := by
    rw [show 1 - sigma = 1 + (-sigma) by ring,
      Real.rpow_add hcutPos, Real.rpow_one]
  have hMain : ‖main‖ ≤
      (3 / 2 : ℝ) * fordDadaroCutoff t ^ (-sigma) := by
    dsimp only [main]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hcutPos]
    simp only [one_re, sub_re]
    rw [show (fordComplexHeight sigma t).re = sigma by simp [fordComplexHeight],
      hPowSplit]
    calc
      fordDadaroCutoff t * fordDadaroCutoff t ^ (-sigma) /
          ‖(1 : ℂ) - fordComplexHeight sigma t‖ =
          (fordDadaroCutoff t /
            ‖(1 : ℂ) - fordComplexHeight sigma t‖) *
              fordDadaroCutoff t ^ (-sigma) := by ring
      _ ≤ (3 / 2 : ℝ) * fordDadaroCutoff t ^ (-sigma) :=
        mul_le_mul_of_nonneg_right hratio
          (Real.rpow_nonneg hcutPos.le _)
  have hBoundary : ‖boundary‖ ≤
      4 * fordDadaroCutoff t ^ (-sigma) := by
    dsimp only [boundary]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hcutPos]
    simp only [neg_re]
    rw [show (fordComplexHeight sigma t).re = sigma by simp [fordComplexHeight]]
    exact mul_le_mul_of_nonneg_right
      (fordDadaroBoundaryCoeff_le_four ht)
      (Real.rpow_nonneg hcutPos.le _)
  have hError : ‖E‖ ≤ 9 * fordDadaroCutoff t ^ (-sigma) := by
    calc
      ‖E‖ ≤
          RiemannZeta.GuthMaynard.sharpZetaErrorCoeff
              (fordComplexHeight sigma t) (fordDadaroCutoff t) /
            fordDadaroCutoff t ^ (sigma + 1) := hE
      _ ≤ 9 / fordDadaroCutoff t ^ (sigma + 1) := by
        gcongr
        exact fordDadaroErrorCoeff_le_nine hsigmaLower hsigmaUpper ht
      _ = 9 * fordDadaroCutoff t ^ (-(sigma + 1)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hcutPos.le]
      _ ≤ 9 * fordDadaroCutoff t ^ (-sigma) := by
        gcongr
        linarith
  have hCutPower :
      fordDadaroCutoff t ^ (-sigma) ≤ t ^ (-sigma) := by
    rw [Real.rpow_neg hcutPos.le, Real.rpow_neg htPos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos htPos _)
      (Real.rpow_le_rpow htPos.le (le_of_lt (lt_fordDadaroCutoff t)) hsigmaLower)
  rw [hDiff]
  calc
    ‖-main - boundary + E‖ ≤ ‖main‖ + ‖boundary‖ + ‖E‖ := by
      calc
        _ ≤ ‖-main - boundary‖ + ‖E‖ := norm_add_le _ _
        _ ≤ (‖-main‖ + ‖boundary‖) + ‖E‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = ‖main‖ + ‖boundary‖ + ‖E‖ := by rw [norm_neg]
    _ ≤ (3 / 2 : ℝ) * fordDadaroCutoff t ^ (-sigma) +
          4 * fordDadaroCutoff t ^ (-sigma) +
          9 * fordDadaroCutoff t ^ (-sigma) := by gcongr
    _ = (29 / 2 : ℝ) * fordDadaroCutoff t ^ (-sigma) := by ring
    _ ≤ 15 * fordDadaroCutoff t ^ (-sigma) := by
      gcongr
      norm_num
    _ ≤ 15 * t ^ (-sigma) := by gcongr

#print axioms norm_riemannZeta_sub_fordFiniteApproximation_le_fifteen

end

end GafniTao
