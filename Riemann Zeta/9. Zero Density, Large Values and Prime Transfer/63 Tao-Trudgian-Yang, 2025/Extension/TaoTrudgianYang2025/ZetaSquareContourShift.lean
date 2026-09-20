import TaoTrudgianYang2025.ZetaSquareContour

/-!
Adapted from the adjacent Gafni--Tao one-sided contour proof, using the
canonical Lean 4.30 foundation directly. This proves an exact contour step;
it is not the uniform local mean-square estimate or the twelfth moment.

# The reflected one-sided zeta-square AFE

The right contour at height `t` opens into the ordinary divisor Dirichlet
series.  The functional equation turns the left contour into the right
contour at `-t`.  This file proves that exact two-piece identity, including
the vanishing horizontal edges.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace TaoTrudgianYang2025

noncomputable section

open RiemannZeta.GuthMaynard

theorem exists_zetaSquareContourIntegrand_horizontal_bound
    (t c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, C > 0 ∧ ∀ H : ℝ, H ≥ 1 → ∀ x ∈ Set.uIcc (-c) c,
      ‖zetaSquareContourIntegrand t
          ((x : ℂ) + (H : ℂ) * I)‖ ≤
        ‖(zetaSquarePoleNormalization t)⁻¹‖ *
          Real.exp (100 * c ^ 2 - H ^ 2 +
            (2 * C + 633) *
              (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hxi⟩ :=
    exists_completedXiNumerator_order_three_halves_bound
  refine ⟨C, hC, ?_⟩
  intro H hH x hx
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have harg := one_add_norm_afeCriticalPoint_add_horizontal_le
    t c H x hc hH0 hx
  have hpow :
      (1 + ‖afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I)‖) ^
          (3 / 2 : ℝ) ≤
        (2 + |t| + c + H) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) harg (by norm_num)
  have hxiBound :
      ‖completedXiNumerator
        (afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I))‖ ≤
        Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) :=
    (hxi _).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hC.le))
  have hxabs : |x| ≤ c := by
    rw [uIcc_of_le (by linarith : -c ≤ c)] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hxsq : x ^ 2 ≤ c ^ 2 := by
    have hsquare := mul_self_le_mul_self (abs_nonneg x) hxabs
    calc
      x ^ 2 = |x| ^ 2 := by rw [sq_abs]
      _ ≤ c ^ 2 := by simpa only [pow_two] using hsquare
  have hgauss :
      ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ ≤
        Real.exp (100 * c ^ 2 - H ^ 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((((x : ℂ) + (H : ℂ) * I) ^ 2).re) =
        x ^ 2 - H ^ 2 := by
      simp [pow_two, mul_re, mul_im]
    norm_num [mul_re, hre]
    nlinarith [sq_nonneg H]
  have hwNorm : 1 ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
    have himle := Complex.abs_im_le_norm ((x : ℂ) + (H : ℂ) * I)
    have himle' : H ≤ ‖(x : ℂ) + (H : ℂ) * I‖ := by
      simpa [abs_of_nonneg hH0] using himle
    linarith
  let R : ℝ := 2 + |t| + c + H
  have hR : 1 ≤ R := by
    dsimp only [R]
    linarith [abs_nonneg t]
  have hwUpper : ‖(x : ℂ) + (H : ℂ) * I‖ ≤ R := by
    calc
      ‖(x : ℂ) + (H : ℂ) * I‖ ≤
          ‖(x : ℂ)‖ + ‖(H : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + H := by simp [Real.norm_eq_abs, abs_of_nonneg hH0]
      _ ≤ R := by
        dsimp only [R]
        linarith [hxabs, abs_nonneg t]
  have haux : ‖hughesYoungAuxiliaryZero
      ((x : ℂ) + (H : ℂ) * I)‖ ≤
      Real.exp (633 * R ^ (3 / 2 : ℝ)) :=
    norm_hughesYoungAuxiliaryZero_le_exp_three_halves hR hwUpper
  unfold zetaSquareContourIntegrand
    zetaSquareContourNumerator
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow]
  have hnum :
      ‖Complex.exp (100 * (((x : ℂ) + (H : ℂ) * I) ^ 2))‖ *
          ‖hughesYoungAuxiliaryZero ((x : ℂ) + (H : ℂ) * I)‖ *
          ‖completedXiNumerator
            (afeCriticalPoint t + ((x : ℂ) + (H : ℂ) * I))‖ ^ 2 ≤
        Real.exp (100 * c ^ 2 - H ^ 2 +
          (2 * C + 633) * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
    calc
      _ ≤ Real.exp (100 * c ^ 2 - H ^ 2) *
          Real.exp (633 * R ^ (3 / 2 : ℝ)) *
          Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) ^ 2 := by
            gcongr
      _ = _ := by
        have hsq :
            Real.exp (C * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) ^ 2 =
              Real.exp (2 * C *
                (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [hsq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [R]
        ring
  calc
    _ ≤ (Real.exp (100 * c ^ 2 - H ^ 2 +
          (2 * C + 633) * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) /
        ‖zetaSquarePoleNormalization t‖) / 1 := by
      gcongr
    _ = ‖(zetaSquarePoleNormalization t)⁻¹‖ *
        Real.exp (100 * c ^ 2 - H ^ 2 +
          (2 * C + 633) * (2 + |t| + c + H) ^ (3 / 2 : ℝ)) := by
      rw [norm_inv]
      field_simp [norm_ne_zero_iff.mpr
        (zetaSquarePoleNormalization_ne_zero t)]

theorem tendsto_hIntegral_zetaSquare_top_zero
    (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral (zetaSquareContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_zetaSquareContourIntegrand_horizontal_bound t c hc
  let A : ℝ := 2 + |t| + c
  let K : ℝ := ‖(zetaSquarePoleNormalization t)⁻¹‖
  let envelope : ℝ → ℝ := fun H =>
    K * Real.exp (100 * c ^ 2 - H ^ 2 +
      (2 * C + 633) * (A + H) ^ (3 / 2 : ℝ))
  have henv0 : Tendsto envelope atTop (𝓝 0) := by
    unfold envelope
    have hraw := tendsto_exp_const_sub_sq_add_three_halves A
      (2 * C + 633) (100 * c ^ 2)
    simpa only [mul_zero] using Tendsto.const_mul K hraw
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (zetaSquareContourIntegrand t) (-c) c H‖ ≤
        envelope H * |c - (-c)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.uIcc (-c) c := Set.uIoc_subset_uIcc hx
      simpa [envelope, A, K, add_assoc] using hbound H hH x hx')
  simpa using henv0.mul_const |c - (-c)|

theorem tendsto_hIntegral'_zetaSquare_top_zero
    (t c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ =>
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H)
      atTop (𝓝 0) := by
  unfold HIntegral'
  simpa using
    (tendsto_hIntegral_zetaSquare_top_zero t c hc).const_smul
      (1 / (2 * Real.pi * I))

theorem hIntegral_zetaSquare_bottom (t c H : ℝ) :
    HIntegral (zetaSquareContourIntegrand t) (-c) c (-H) =
      -HIntegral (zetaSquareContourIntegrand (-t)) (-c) c H := by
  let f := zetaSquareContourIntegrand t
  let g := zetaSquareContourIntegrand (-t)
  have hpoint : ∀ x : ℝ,
      f ((x : ℂ) + (-H : ℂ) * I) =
        -g (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
    intro x
    have harg : (x : ℂ) + (-H : ℂ) * I =
        -(((-x : ℝ) : ℂ) + (H : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact zetaSquareContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => g ((x : ℂ) + (H : ℂ) * I))
    (a := -c) (b := c)
  simp only [neg_neg] at hcomp
  change (∫ x in -c..c, f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
    -(∫ x in -c..c, g ((x : ℂ) + (H : ℂ) * I))
  calc
    _ = -∫ x in -c..c, g (((-x : ℝ) : ℂ) + (H : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _hx
      simpa only [ofReal_neg] using hpoint x
    _ = _ := by
      rw [hcomp]

theorem vIntegral_zetaSquare_left (t c H : ℝ) :
    VIntegral (zetaSquareContourIntegrand t) (-c) (-H) H =
      -VIntegral (zetaSquareContourIntegrand (-t)) c (-H) H := by
  let f := zetaSquareContourIntegrand t
  let g := zetaSquareContourIntegrand (-t)
  have hpoint : ∀ y : ℝ,
      f (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    intro y
    have harg : (((-c : ℝ) : ℂ) + (y : ℂ) * I) =
        -((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [harg]
    exact zetaSquareContourIntegrand_neg t _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ => g ((c : ℂ) + (y : ℂ) * I))
    (a := -H) (b := H)
  simp only [neg_neg] at hcomp
  have hraw :
    (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -∫ y in -H..H, g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      simpa only [ofReal_neg] using hpoint y
  have hraw' :
      (∫ y in -H..H, f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -(∫ y in -H..H, g ((c : ℂ) + (y : ℂ) * I)) := by
    calc
      _ = -∫ y in -H..H, g ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := hraw
      _ = _ := by rw [hcomp]
  unfold VIntegral
  rw [hraw']
  simp [g]

/-- Finite-height one-sided AFE with both reflected right contours and both
horizontal errors displayed. -/
theorem zetaSquareAFE_truncated_native
    (t : ℝ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H -
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H -
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H := by
  have hrect := zetaSquare_finiteRectangle t hc hH
  change RectangleIntegral'
      (zetaSquareContourIntegrand t)
      ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) = _ at hrect
  rw [show RectangleIntegral'
        (zetaSquareContourIntegrand t)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H -
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H -
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H by
    unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
    simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
    rw [hIntegral_zetaSquare_bottom,
      vIntegral_zetaSquare_left]
    ring] at hrect
  exact hrect.symm

/-- Infinite-height AFE: the two right contours sum to the completed zeta
square at height `t`. -/
theorem zetaSquareAFE_vertical_limit_native
    (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      VIntegral' (zetaSquareContourIntegrand t) c (-H) H +
      VIntegral' (zetaSquareContourIntegrand (-t)) c (-H) H)
      atTop (𝓝 (completedRiemannZeta (afeCriticalPoint t) ^ 2)) := by
  let F : ℂ := completedRiemannZeta (afeCriticalPoint t) ^ 2
  have ht := tendsto_hIntegral'_zetaSquare_top_zero t c hc.le
  have hmt := tendsto_hIntegral'_zetaSquare_top_zero (-t) c hc.le
  have htarget : Tendsto (fun H : ℝ => F +
      HIntegral' (zetaSquareContourIntegrand t) (-c) c H +
      HIntegral' (zetaSquareContourIntegrand (-t)) (-c) c H)
      atTop (𝓝 F) := by
    simpa using (tendsto_const_nhds.add ht).add hmt
  apply htarget.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hfinite := zetaSquareAFE_truncated_native t hc hH
  change F = _ at hfinite
  linear_combination hfinite


end

end TaoTrudgianYang2025
