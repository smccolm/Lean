import GafniTao.PintzZetaAFEKernelBound

/-!
# The dual central kernel in the single-zeta AFE

The second AFE edge is centred at `1-s`, while its normalization remains at
`s`.  This file proves the two sign/conductor bridges needed to estimate that
literal edge.  In particular, the factor `t^(1/2-r)` is derived from the
real-Gamma quotient and is not inserted as an independent hypothesis.
-/

open Complex

namespace GafniTao

noncomputable section

/-- The pole-cancelling polynomial costs at most four on the central part of
the dual edge. -/
theorem norm_pintzZetaAFE_dual_polynomial_ratio_le_four
    {r q t u : ℝ} (hrLower : 1 / 2 < r)
    (hq : 0 < q) (hqDual : q < 1 - r)
    (ht : 4 ≤ t) (hu : |u| ≤ t / 2) :
    ‖(((((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I) *
          (1 - (((1 - r - q : ℝ) : ℂ) +
            ((-t + u : ℝ) : ℂ) * I))) /
        ((((r : ℝ) : ℂ) + (t : ℂ) * I) *
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I))))‖ ≤ 4 := by
  let z : ℂ := ((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  have hzRe : 0 ≤ z.re := by simp [z]; linarith
  have hzReUpper : z.re ≤ 1 := by simp [z]; linarith
  have htPos : 0 < t := by linarith
  have himAbs : |-t + u| ≤ 3 * t / 2 := by
    calc
      |-t + u| ≤ |-t| + |u| := abs_add_le _ _
      _ ≤ t + t / 2 := by rw [abs_neg, abs_of_pos htPos]; gcongr
      _ = 3 * t / 2 := by ring
  have hzNorm : ‖z‖ ≤ 2 * t := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = z.re + |-t + u| := by rw [abs_of_nonneg hzRe]; simp [z]
      _ ≤ 1 + 3 * t / 2 := add_le_add hzReUpper himAbs
      _ ≤ 2 * t := by linarith
  have honezRe : 0 ≤ (1 - z).re := by simp; exact hzReUpper
  have honezNorm : ‖1 - z‖ ≤ 2 * t := by
    calc
      ‖1 - z‖ ≤ |(1 - z).re| + |(1 - z).im| :=
        Complex.norm_le_abs_re_add_abs_im (1 - z)
      _ ≤ 1 + 3 * t / 2 := by
        rw [abs_of_nonneg honezRe]
        have hre : (1 - z).re ≤ 1 := by simp; exact hzRe
        have him : |(1 - z).im| = |-t + u| := by
          simp only [z, sub_im, one_im, add_im, ofReal_im, ofReal_re,
            mul_im, I_im, I_re, mul_one, zero_mul, add_zero, zero_sub]
          rw [zero_add, abs_neg]
        rw [him]
        linarith
      _ ≤ 2 * t := by linarith
  have hsNorm : t ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa [s, abs_of_pos htPos] using h
  have honesNorm : t ≤ ‖1 - s‖ := by
    have h := Complex.abs_im_le_norm (1 - s)
    simpa [s, abs_of_pos htPos, abs_neg] using h
  have hsNormPos : 0 < ‖s‖ := htPos.trans_le hsNorm
  have honesNormPos : 0 < ‖1 - s‖ := htPos.trans_le honesNorm
  change ‖z * (1 - z) / (s * (1 - s))‖ ≤ 4
  rw [norm_div, norm_mul, norm_mul]
  rw [div_le_iff₀ (mul_pos hsNormPos honesNormPos)]
  calc
    ‖z‖ * ‖1 - z‖ ≤ (2 * t) * (2 * t) :=
      mul_le_mul hzNorm honezNorm (norm_nonneg _) (by positivity)
    _ = 4 * (t * t) := by ring
    _ ≤ 4 * (‖s‖ * ‖1 - s‖) := by gcongr

/-- The displaced dual Gamma quotient is the product of a left displacement
at `1-s` and the exact unshifted functional-equation conductor. -/
theorem exists_norm_GammaR_dual_displaced_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqDual : q < 1 - r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      4 ≤ t → |u| ≤ t / 2 →
      ‖Complex.Gammaℝ
          (((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp (C + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2) +
          Real.log (t / 4 + 2) * (1 / 2 - r)) := by
  have hdualBasePos : 0 < 1 - r := by linarith
  obtain ⟨Cshift, hCshift, hshift⟩ :=
    exists_norm_GammaR_left_vertical_ratio_le
      hq hqDual (by linarith : 1 - r ≤ 1)
  obtain ⟨Cdual, hCdual, hdual⟩ :=
    exists_norm_GammaR_dual_ratio_le hrLower hrUpper
  let C : ℝ := Cshift + Cdual
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u ht hu
  let A : ℂ := Complex.Gammaℝ
    (((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)
  let B : ℂ := Complex.Gammaℝ
    (((1 - r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
  let D : ℂ := Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)
  have hB : B ≠ 0 := by
    dsimp only [B]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hD : D ≠ 0 := by
    dsimp only [D]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hfactor : A / D = (A / B) * (B / D) := by
    field_simp
  have hshiftRaw := hshift t (-u) ht (by simpa [abs_neg] using hu)
  rw [norm_div] at hshiftRaw
  have hshiftSign :
      ‖A / B‖ ≤ Real.exp (Cshift + Real.pi * |u| / 4 -
        Real.log (t / 4 + 2) * (q / 2)) := by
    have hnum :
        ‖Complex.Gammaℝ
            (((1 - r - q : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ =
          ‖Complex.Gammaℝ
            (((1 - r - q : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I)‖ := by
      have h := norm_GammaR_real_neg_im_eq (1 - r - q) (t - u)
      convert h using 1
      congr 2
      push_cast
      ring
    have hden :
        ‖Complex.Gammaℝ
            (((1 - r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
          ‖Complex.Gammaℝ
            (((1 - r : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_GammaR_real_neg_im_eq (1 - r) t
    dsimp only [A, B]
    rw [norm_div, hnum, hden]
    simpa only [sub_eq_add_neg, abs_neg] using hshiftRaw
  have hdualRaw := hdual t ht
  have hmul := mul_le_mul hshiftSign hdualRaw (norm_nonneg _)
    (Real.exp_pos _).le
  rw [hfactor, norm_mul]
  calc
    ‖A / B‖ * ‖B / D‖ ≤
        Real.exp (Cshift + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2)) *
        Real.exp (Cdual + Real.log (t / 4 + 2) * (1 / 2 - r)) := by
      simpa only [A, B, D] using hmul
    _ = Real.exp (C + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2) +
          Real.log (t / 4 + 2) * (1 / 2 - r)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [C]
      ring

/-- Literal central-line majorant for one coefficient on the dual AFE edge.
The last exponential is the functional-equation conductor and remains
separate for the square-root cancellation in the finite-head consumer. -/
theorem exists_norm_pintzZetaAFETermContourIntegrand_dual_central_le
    {r q : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1)
    (hq : 0 < q) (hqDual : q < 1 - r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ) (n : ℕ),
      4 ≤ t → |u| ≤ t / 2 → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I)) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
          (n : ℝ) ^ (-(1 - r - q)) := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_GammaR_dual_displaced_le hrLower hrUpper hq hqDual
  let C : ℝ := 4 * q⁻¹ * Real.exp (100 * q ^ 2 + Cgamma)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u n ht hu hn
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  let base : ℂ := 1 - s
  let w : ℂ := ((-q : ℝ) : ℂ) + (u : ℂ) * I
  have hpoly := norm_pintzZetaAFE_dual_polynomial_ratio_le_four
    hrLower hq hqDual ht hu
  have hgam := hgamma t u ht hu
  have hsum :
      base + w = ((1 - r - q : ℝ) : ℂ) +
        ((-t + u : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [base, s, w]
      ring
    · simp [base, s, w]
  have hdir : ‖pintzZetaDirichletTerm (base + w) n‖ =
      (n : ℝ) ^ (-(1 - r - q)) := by
    rw [norm_pintzZetaDirichletTerm_of_ne_zero hn, hsum]
    congr 1
    simp
  have hwInv := norm_inv_neg_real_add_im_le (u := u) hq
  have hgauss := norm_pintzZetaAFE_gaussian_vertical (-q) u
  rw [pintzZetaAFETermContourIntegrand_factor]
  simp only [norm_div, norm_mul]
  rw [hgauss, hdir]
  have hpoly' :
      ‖(base + w) * (1 - (base + w)) / (s * (1 - s))‖ ≤ 4 := by
    rw [hsum]
    simpa only [s] using hpoly
  have hgam' :
      ‖Complex.Gammaℝ (base + w) / Complex.Gammaℝ s‖ ≤
        Real.exp (Cgamma + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2) +
          Real.log (t / 4 + 2) * (1 / 2 - r)) := by
    rw [hsum]
    simpa only [s] using hgam
  have hExp :
      Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          Real.exp (Cgamma + Real.pi * |u| / 4 -
            Real.log (t / 4 + 2) * (q / 2) +
            Real.log (t / 4 + 2) * (1 / 2 - r)) =
        Real.exp (100 * q ^ 2 + Cgamma) *
          Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) := by
    repeat' rw [← Real.exp_add]
    congr 1
    ring
  simp only [norm_div, norm_mul] at hpoly' hgam'
  rw [div_eq_mul_inv]
  calc
    Real.exp (100 * (-q) ^ 2 - 100 * u ^ 2) *
          ((‖base + w‖ * ‖1 - (base + w)‖) /
            (‖s‖ * ‖1 - s‖)) *
          (‖Complex.Gammaℝ (base + w)‖ / ‖Complex.Gammaℝ s‖) *
          (n : ℝ) ^ (-(1 - r - q)) * ‖w‖⁻¹ ≤
        Real.exp (100 * q ^ 2 - 100 * u ^ 2) * 4 *
          Real.exp (Cgamma + Real.pi * |u| / 4 -
            Real.log (t / 4 + 2) * (q / 2) +
            Real.log (t / 4 + 2) * (1 / 2 - r)) *
          (n : ℝ) ^ (-(1 - r - q)) * q⁻¹ := by
      rw [neg_sq]
      gcongr
    _ = 4 * q⁻¹ *
          (Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
            Real.exp (Cgamma + Real.pi * |u| / 4 -
              Real.log (t / 4 + 2) * (q / 2) +
              Real.log (t / 4 + 2) * (1 / 2 - r))) *
          (n : ℝ) ^ (-(1 - r - q)) := by ring
    _ = C * Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          Real.exp (Real.log (t / 4 + 2) * (1 / 2 - r)) *
          (n : ℝ) ^ (-(1 - r - q)) := by
      rw [hExp]
      dsimp only [C]
      ring

#print axioms norm_pintzZetaAFE_dual_polynomial_ratio_le_four
#print axioms exists_norm_GammaR_dual_displaced_le
#print axioms exists_norm_pintzZetaAFETermContourIntegrand_dual_central_le

end

end GafniTao
