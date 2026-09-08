import GafniTao.FordShiftedZeroDetectorAssembly
import GafniTao.FordZeroDetectorHorizontalBound

/-!
# Uniform horizontal-tail bound for the shifted detector
-/

open Complex Set MeasureTheory Metric Finset
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordShiftedHorizontalOffset_eq_unshifted
    (sigma y x : ℝ) :
    fordShiftedHorizontalOffset sigma y x =
      fordHorizontalOffset y (x - sigma + 1) := by
  unfold fordShiftedHorizontalOffset fordHorizontalOffset
  push_cast
  ring

theorem norm_deriv_fordCotKernel_shifted_horizontal_abs_le
    {sigma eta y x : ℝ} (heta : 0 < eta)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * |y|) :
    ‖deriv (fordCotKernel eta)
      (fordShiftedHorizontalOffset sigma y x)‖ ≤
      16 * (Real.pi / (2 * eta)) ^ 2 *
        Real.exp (-2 * ((Real.pi / (2 * eta)) * |y|)) := by
  rw [fordShiftedHorizontalOffset_eq_unshifted]
  exact norm_deriv_fordCotKernel_horizontal_abs_le heta hheight

theorem norm_fordShiftedHorizontalRemainder_le
    {sigma eta t y M : ℝ} (heta : 0 < eta) (hM : 0 ≤ M)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * |y|)
    (hL : ∀ x ∈ Set.Icc (sigma - eta) (sigma + eta),
      ‖fordHorizontalLogDeriv t y x‖ ≤ M) :
    ‖fordShiftedHorizontalRemainder sigma eta t y‖ ≤
      ((1 / (2 * Real.pi)) *
        (16 * (Real.pi / (2 * eta)) ^ 2 *
          Real.exp (-2 * ((Real.pi / (2 * eta)) * |y|))) *
        (2 * eta * M)) * (2 * eta) := by
  let D : ℝ := 16 * (Real.pi / (2 * eta)) ^ 2 *
    Real.exp (-2 * ((Real.pi / (2 * eta)) * |y|))
  let B : ℝ := (1 / (2 * Real.pi)) * D * (2 * eta * M)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
    ring
  have hpoint : ∀ x ∈ Set.Icc (sigma - eta) (sigma + eta),
      ‖fordShiftedHorizontalWeightDeriv sigma eta y x *
        fordHorizontalNormalizedLogLift t y (sigma - eta) x‖ ≤ B := by
    intro x hx
    have hlift := norm_fordHorizontalNormalizedLogLift_le
      (t := t) (y := y) (a := sigma - eta) (x := x) (M := M)
      (by linarith [hx.1])
      (fun u hu => hL u ⟨hu.1, hu.2.trans hx.2⟩)
    have hxlen : x - (sigma - eta) ≤ 2 * eta := by
      linarith [hx.2]
    have hlift' :
        ‖fordHorizontalNormalizedLogLift t y (sigma - eta) x‖ ≤
          2 * eta * M := by
      calc
        _ ≤ M * (x - (sigma - eta)) := hlift
        _ ≤ M * (2 * eta) :=
          mul_le_mul_of_nonneg_left hxlen hM
        _ = 2 * eta * M := by ring
    have hweight :
        ‖fordShiftedHorizontalWeightDeriv sigma eta y x‖ ≤
          (1 / (2 * Real.pi)) * D := by
      unfold fordShiftedHorizontalWeightDeriv
      rw [norm_mul, hscalar]
      exact mul_le_mul_of_nonneg_left
        (norm_deriv_fordCotKernel_shifted_horizontal_abs_le
          (sigma := sigma) heta hheight)
        (by positivity)
    rw [norm_mul]
    exact (mul_le_mul hweight hlift'
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp only [B])
  have hab : sigma - eta ≤ sigma + eta := by linarith
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ =>
      fordShiftedHorizontalWeightDeriv sigma eta y x *
        fordHorizontalNormalizedLogLift t y (sigma - eta) x)
    (a := sigma - eta) (b := sigma + eta) (C := B)
    (fun x hx => hpoint x (by
      have hx' := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le hab] at hx'
      exact hx'))
  have hlen : |(sigma + eta) - (sigma - eta)| = 2 * eta := by
    rw [abs_of_pos (by linarith)]
    ring
  unfold fordShiftedHorizontalRemainder
  rw [hlen] at hraw
  simpa [B, D] using hraw

end

end GafniTao
