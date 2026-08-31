import GafniTao.FordZeroDetectorAbelAssembly
import GafniTao.SharpPerronHorizontalAll

/-!
# Quantitative horizontal remainder bound

The normalized logarithm lift removes the otherwise unnecessary initial
branch constant.  Its norm is controlled solely by the selected-height
logarithmic-derivative estimate.  Combined with exponential decay of the
cotangent derivative, this gives Ford's complete finite horizontal-tail
majorant.
-/

open Complex Set MeasureTheory Metric Finset
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem norm_deriv_fordCotKernel_horizontal_abs_le
    {eta y x : ℝ} (heta : 0 < eta)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * |y|) :
    ‖deriv (fordCotKernel eta) (fordHorizontalOffset y x)‖ ≤
      16 * (Real.pi / (2 * eta)) ^ 2 *
        Real.exp (-2 * ((Real.pi / (2 * eta)) * |y|)) := by
  by_cases hy : 0 ≤ y
  · have hheightY : 1 ≤ (Real.pi / (2 * eta)) * y := by
      simpa [abs_of_nonneg hy] using hheight
    rw [abs_of_nonneg hy]
    simpa [fordHorizontalOffset] using
      (norm_deriv_fordCotKernel_horizontal_le
        (R := y) (x := x - 1) heta hheightY)
  · have hyneg : y < 0 := lt_of_not_ge hy
    have habs : |y| = -y := abs_of_neg hyneg
    have hpos : 0 < -y := neg_pos.mpr hyneg
    have hsinY := ford_horizontal_scaled_sin_ne_zero
      heta hyneg.ne (x := x)
    have hsinNeg := ford_horizontal_scaled_sin_ne_zero
      heta hpos.ne' (y := -y) (x := x)
    let c : ℝ := Real.pi / (2 * eta)
    have hc : 0 < c := by dsimp only [c]; positivity
    have hscaleY :
        ((c : ℂ) * fordHorizontalOffset y x) =
          ((c * (x - 1) : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [fordHorizontalOffset]
    have hscaleNeg :
        ((c : ℂ) * fordHorizontalOffset (-y) x) =
          ((c * (x - 1) : ℝ) : ℂ) + ((c * (-y) : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [fordHorizontalOffset]
    have hsquareY := norm_sin_add_mul_I_sq (c * (x - 1)) (c * y)
    have hsquareNeg := norm_sin_add_mul_I_sq
      (c * (x - 1)) (c * (-y))
    have hsinhSq : Real.sinh (c * (-y)) ^ 2 =
        Real.sinh (c * y) ^ 2 := by
      rw [show c * (-y) = -(c * y) by ring, Real.sinh_neg]
      ring
    have hnormSin :
        ‖Complex.sin ((c : ℂ) * fordHorizontalOffset y x)‖ =
          ‖Complex.sin ((c : ℂ) * fordHorizontalOffset (-y) x)‖ := by
      rw [hscaleY, hscaleNeg]
      nlinarith [norm_nonneg (Complex.sin
        (((c * (x - 1) : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I)),
        norm_nonneg (Complex.sin
          (((c * (x - 1) : ℝ) : ℂ) + ((c * (-y) : ℝ) : ℂ) * I))]
    have hnormDeriv :
        ‖deriv (fordCotKernel eta) (fordHorizontalOffset y x)‖ =
          ‖deriv (fordCotKernel eta) (fordHorizontalOffset (-y) x)‖ := by
      rw [(hasDerivAt_fordCotKernel hsinY).deriv,
        (hasDerivAt_fordCotKernel hsinNeg).deriv,
        norm_div, norm_div, norm_pow, norm_pow,
        hnormSin]
    have hheightNeg :
        1 ≤ (Real.pi / (2 * eta)) * (-y) := by
      rw [← habs]
      exact hheight
    rw [hnormDeriv, habs]
    simpa [fordHorizontalOffset] using
      (norm_deriv_fordCotKernel_horizontal_le
        (R := -y) (x := x - 1) heta hheightNeg)

theorem norm_fordHorizontalNormalizedLogLift_le
    {t y a x M : ℝ} (hax : a ≤ x)
    (hL : ∀ u ∈ Set.Icc a x,
      ‖fordHorizontalLogDeriv t y u‖ ≤ M) :
    ‖fordHorizontalNormalizedLogLift t y a x‖ ≤ M * (x - a) := by
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fordHorizontalLogDeriv t y) (a := a) (b := x) (C := M)
    (fun u hu => hL u (by
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le hax] at hu'
      exact hu'))
  unfold fordHorizontalNormalizedLogLift intervalLogLift
  simp only [zero_add]
  rw [abs_of_nonneg (sub_nonneg.mpr hax)] at hraw
  exact hraw

theorem norm_fordDetectorHorizontalRemainder_le
    {eta t y M : ℝ} (heta : 0 < eta) (hM : 0 ≤ M)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * |y|)
    (hL : ∀ x ∈ Set.Icc (1 - eta) (1 + eta),
      ‖fordHorizontalLogDeriv t y x‖ ≤ M) :
    ‖fordDetectorHorizontalRemainder eta t y‖ ≤
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
  have hpoint : ∀ x ∈ Set.Icc (1 - eta) (1 + eta),
      ‖fordHorizontalWeightDeriv eta y x *
        fordHorizontalNormalizedLogLift t y (1 - eta) x‖ ≤ B := by
    intro x hx
    have hlift := norm_fordHorizontalNormalizedLogLift_le
      (t := t) (y := y) (a := 1 - eta) (x := x) (M := M)
      (by linarith [hx.1]) (fun u hu => hL u ⟨hu.1, hu.2.trans hx.2⟩)
    have hxlen : x - (1 - eta) ≤ 2 * eta := by linarith [hx.2]
    have hlift' :
        ‖fordHorizontalNormalizedLogLift t y (1 - eta) x‖ ≤
          2 * eta * M := by
      calc
        _ ≤ M * (x - (1 - eta)) := hlift
        _ ≤ M * (2 * eta) :=
          mul_le_mul_of_nonneg_left hxlen hM
        _ = 2 * eta * M := by ring
    have hweight : ‖fordHorizontalWeightDeriv eta y x‖ ≤
        (1 / (2 * Real.pi)) * D := by
      unfold fordHorizontalWeightDeriv
      rw [norm_mul, hscalar]
      exact mul_le_mul_of_nonneg_left
        (norm_deriv_fordCotKernel_horizontal_abs_le heta hheight)
        (by positivity)
    rw [norm_mul]
    exact (mul_le_mul hweight hlift'
      (norm_nonneg _) (by positivity)).trans_eq (by
        dsimp only [B])
  have hab : 1 - eta ≤ 1 + eta := by linarith
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => fordHorizontalWeightDeriv eta y x *
      fordHorizontalNormalizedLogLift t y (1 - eta) x)
    (a := 1 - eta) (b := 1 + eta) (C := B)
    (fun x hx => hpoint x (by
      have hx' := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le hab] at hx'
      exact hx'))
  have hlen : |(1 + eta) - (1 - eta)| = 2 * eta := by
    rw [abs_of_pos (by linarith)]
    ring
  unfold fordDetectorHorizontalRemainder
  rw [hlen] at hraw
  simpa [B, D] using hraw

end

end GafniTao
