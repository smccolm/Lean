import Tao2026.SmoothNumberSaddleHTContourEdgeBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted left-edge reduction for the HT contour

A uniform sup bound on the full left-edge integrand is exponentially too
coarse, because it discards the Perron denominator before integrating over
the full height.  This module retains that denominator.  The elementary
estimate

`1 / ‖a + iu‖ ≤ 2 / (a + |u|)`

turns the vertical integral into a logarithm.  Together with the two
horizontal sup bounds, this gives the source-scale scalar edge majorant that
the translated zeta logarithmic-derivative estimates must satisfy.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

private theorem norm_perronContourScalar_weighted :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I) : ℂ)‖ =
      1 / (2 * Real.pi) := by
  simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I]
  ring

/-- Exact logarithmic mass of the elementary reciprocal-distance envelope. -/
theorem integral_one_div_add_abs
    {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ u in (-T)..T, 1 / (a + |u|)) =
      2 * Real.log ((a + T) / a) := by
  let g : ℝ → ℝ := fun u => 1 / (a + |u|)
  have hg : Continuous g := by
    dsimp [g]
    apply Continuous.div continuous_const (continuous_const.add continuous_abs)
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (abs_nonneg u))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-T) 0 : IntervalIntegrable g volume (-T) 0)
    (hg.intervalIntegrable 0 T : IntervalIntegrable g volume 0 T)
  have hneg : (∫ u in (-T)..0, g u) = ∫ u in 0..T, g u := by
    calc
      (∫ u in (-T)..0, g u) = ∫ u in 0..T, g (-u) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg
            (f := g) (a := 0) (b := T)).symm
      _ = ∫ u in 0..T, g u := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp [g]
  have hpos : (∫ u in 0..T, g u) = Real.log ((a + T) / a) := by
    calc
      (∫ u in 0..T, g u) = ∫ u in 0..T, 1 / (a + u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : 0 ≤ u := by
          rw [Set.uIcc_of_le hT] at hu
          exact hu.1
        simp [g, abs_of_nonneg hu']
      _ = Real.log (a + T) - Real.log a := by
        have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) T,
            HasDerivAt (fun v : ℝ => Real.log (a + v))
              (1 / (a + u)) u := by
          intro u hu
          rw [Set.uIcc_of_le hT] at hu
          have hu0 := hu.1
          have hau : a + u ≠ 0 := by linarith
          simpa [one_div] using
            ((hasDerivAt_const u a).add (hasDerivAt_id u)).log hau
        have hcont : ContinuousOn (fun u : ℝ => 1 / (a + u))
            (Set.uIcc 0 T) := by
          apply ContinuousOn.div continuousOn_const
            (continuousOn_const.add continuousOn_id)
          intro u hu
          rw [Set.uIcc_of_le hT] at hu
          have hu0 := hu.1
          change a + u ≠ 0
          linarith
        simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
          hderiv (hcont.intervalIntegrable :
            IntervalIntegrable (fun u : ℝ => 1 / (a + u)) volume 0 T)
      _ = Real.log ((a + T) / a) := by
        rw [Real.log_div (by linarith) (ne_of_gt ha)]
  rw [← hsplit, hneg, hpos]
  ring

/-- A vertical pointwise estimate retaining the Perron denominator incurs
only a logarithmic height cost after normalized contour integration. -/
theorem norm_VIntegral'_le_of_norm_le_div_norm
    {f : ℂ → ℂ} {a T B : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hpoint : ∀ u ∈ Set.Icc (-T) T,
      ‖f ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        B / ‖(a : ℂ) + (u : ℂ) * Complex.I‖) :
    ‖VIntegral' f a (-T) T‖ ≤
      (1 / (2 * Real.pi)) *
        (4 * B * Real.log ((a + T) / a)) := by
  let g : ℝ → ℝ := fun u => 2 * B / (a + |u|)
  have hg : Continuous g := by
    dsimp [g]
    apply Continuous.div
      (continuous_const.mul continuous_const)
      (continuous_const.add continuous_abs)
    intro u
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha (abs_nonneg u))
  have hraw := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun u : ℝ => f ((a : ℂ) + (u : ℂ) * Complex.I))
    (g := g) (a := -T) (b := T) (by linarith) (by
      filter_upwards with u hu
      have huIcc : u ∈ Set.Icc (-T) T := by
        rw [Set.mem_Ioc] at hu
        exact ⟨hu.1.le, hu.2⟩
      let z : ℂ := (a : ℂ) + (u : ℂ) * Complex.I
      have hzRe : z.re = a := by simp [z]
      have hzIm : z.im = u := by simp [z]
      have hz0 : z ≠ 0 := by
        intro hz
        have hzReZero := congrArg Complex.re hz
        simp [z] at hzReZero
        linarith
      have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hsum : 0 < a + |u| :=
        add_pos_of_pos_of_nonneg ha (abs_nonneg u)
      have haNorm : a ≤ ‖z‖ := by
        have h := Complex.abs_re_le_norm z
        rwa [hzRe, abs_of_pos ha] at h
      have huNorm : |u| ≤ ‖z‖ := by
        have h := Complex.abs_im_le_norm z
        rwa [hzIm] at h
      have hgeom : a + |u| ≤ 2 * ‖z‖ := by linarith
      calc
        ‖f ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ B / ‖z‖ := by
          simpa [z] using hpoint u huIcc
        _ ≤ 2 * B / (a + |u|) := by
          rw [div_le_div_iff₀ hznorm hsum]
          nlinarith
        _ = g u := by rfl)
    (hg.intervalIntegrable (-T) T : IntervalIntegrable g volume (-T) T)
  rw [VIntegral', VIntegral]
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, one_mul,
    norm_perronContourScalar_weighted]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ u in (-T)..T,
          f ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      (1 / (2 * Real.pi)) * (∫ u in (-T)..T, g u) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (1 / (2 * Real.pi)) *
        (4 * B * Real.log ((a + T) / a)) := by
      rw [show (∫ u in (-T)..T, g u) =
          4 * B * Real.log ((a + T) / a) by
        dsimp [g]
        calc
          (∫ u in (-T)..T, 2 * B / (a + |u|)) =
              ∫ u in (-T)..T, (2 * B) * (1 / (a + |u|)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring
          _ = (2 * B) * (∫ u in (-T)..T, 1 / (a + |u|)) := by
            rw [intervalIntegral.integral_const_mul]
          _ = 4 * B * Real.log ((a + T) / a) := by
            rw [integral_one_div_add_abs ha hT]
            ring]

/-- Exact norm factorization of the translated shifted-Perron integrand at
a zero-free, non-pole point. -/
theorem norm_smoothSaddleHTShiftedZetaPerronIntegrand_eq
    {y : ℝ} {s z : ℂ} (hy : 0 < y)
    (hz0 : z ≠ 0) (hsz1 : s + z ≠ 1)
    (hzeta : riemannZeta (s + z) ≠ 0) :
    ‖smoothSaddleHTShiftedZetaPerronIntegrand y s z‖ =
      ‖deriv riemannZeta (s + z) / riemannZeta (s + z)‖ *
        y ^ z.re / ‖z‖ := by
  rw [smoothSaddleHTShiftedZetaPerronIntegrand_eq hz0 hsz1 hzeta]
  simp only [norm_mul, norm_neg, logDeriv_apply, norm_div]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  ring

/-- A pointwise logarithmic-derivative bound transfers directly to the
shifted-Perron integrand while retaining its full Perron denominator. -/
theorem norm_smoothSaddleHTShiftedZetaPerronIntegrand_le
    {y L : ℝ} {s z : ℂ} (hy : 0 < y)
    (hz0 : z ≠ 0) (hsz1 : s + z ≠ 1)
    (hzeta : riemannZeta (s + z) ≠ 0)
    (hlog : ‖deriv riemannZeta (s + z) / riemannZeta (s + z)‖ ≤ L) :
    ‖smoothSaddleHTShiftedZetaPerronIntegrand y s z‖ ≤
      L * y ^ z.re / ‖z‖ := by
  rw [norm_smoothSaddleHTShiftedZetaPerronIntegrand_eq
    hy hz0 hsz1 hzeta]
  gcongr

/-- The source-scale scalar majorant retaining the reciprocal denominator on
the left vertical edge. -/
noncomputable def smoothSaddleHTContourEdgeWeightedMajorant
    (y : ℕ) (beta ε horizontalBound verticalNumerator : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (2 * horizontalBound *
        (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
      4 * verticalNumerator *
        Real.log
          (((beta - smoothSaddleHTContourShift y ε) +
              smoothSaddleHTContourHeight y ε) /
            (beta - smoothSaddleHTContourShift y ε)))

/-- Two horizontal sup bounds and a denominator-retaining vertical bound
control the complete three-edge contribution at logarithmic vertical cost. -/
theorem norm_smoothSaddleHTContourEdgeContribution_le_weightedMajorant
    {y : ℕ} {beta ε t horizontalBound verticalNumerator : ℝ}
    (hy : 2 ≤ y)
    (hbetaShift : smoothSaddleHTContourShift y ε < beta)
    (hVertical : 0 ≤ verticalNumerator)
    (hbottom : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) -
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (htop : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) +
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (hleft : ∀ u ∈ Set.Icc
        (-smoothSaddleHTContourHeight y ε)
        (smoothSaddleHTContourHeight y ε),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            (u : ℂ) * Complex.I)‖ ≤
        verticalNumerator /
          ‖((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            (u : ℂ) * Complex.I‖) :
    ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTContourEdgeWeightedMajorant y beta ε
        horizontalBound verticalNumerator := by
  let left : ℝ := beta - smoothSaddleHTContourShift y ε
  let right : ℝ := smoothSaddleHTContourRight y beta
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let F : ℂ → ℂ := smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
    (smoothSaddleHTSourceExponent beta t)
  have hshiftPos := smoothSaddleHTContourShift_pos hy ε
  have hright := smoothSaddleHTContourRight_gt hy beta
  have hleftPos : 0 < left := by
    dsimp [left]
    linarith
  have hlr : left ≤ right := by
    dsimp [left, right]
    linarith
  have hT : 0 ≤ T := (smoothSaddleHTContourHeight_pos y ε).le
  have hbottom' : ‖HIntegral' F left right (-T)‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    simpa [F, T, sub_eq_add_neg] using
      hbottom x (by simpa [left, right] using hx)
  have htop' : ‖HIntegral' F left right T‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    exact htop x (by simpa [left, right] using hx)
  have hleft' : ‖VIntegral' F left (-T) T‖ ≤
      (1 / (2 * Real.pi)) *
        (4 * verticalNumerator * Real.log ((left + T) / left)) := by
    apply norm_VIntegral'_le_of_norm_le_div_norm
      hleftPos hT hVertical
    intro u hu
    exact hleft u (by simpa [left, T] using hu)
  unfold smoothSaddleHTContourEdgeContribution
  change ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
      VIntegral' F left (-T) T‖ ≤ _
  calc
    ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
        VIntegral' F left (-T) T‖ ≤
      ‖HIntegral' F left right (-T)‖ +
        ‖HIntegral' F left right T‖ +
          ‖VIntegral' F left (-T) T‖ := by
            simpa using (norm_add₃_le :
              ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
                  VIntegral' F left (-T) T‖ ≤
                ‖-HIntegral' F left right (-T)‖ +
                  ‖HIntegral' F left right T‖ +
                    ‖VIntegral' F left (-T) T‖)
    _ ≤ (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
        (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
          (1 / (2 * Real.pi)) *
            (4 * verticalNumerator * Real.log ((left + T) / left)) := by
              gcongr
    _ = smoothSaddleHTContourEdgeWeightedMajorant y beta ε
        horizontalBound verticalNumerator := by
      rw [show right - left =
          smoothSaddleHTContourShift y ε + 1 / Real.log y by
        simpa [left, right] using
          smoothSaddleHTContour_horizontal_length y beta ε]
      simp only [left, T, smoothSaddleHTContourEdgeWeightedMajorant]
      ring

end

end Tao2026
