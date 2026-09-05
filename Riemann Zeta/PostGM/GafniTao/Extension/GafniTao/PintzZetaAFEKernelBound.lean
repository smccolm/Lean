import GafniTao.PintzGammaVerticalRatio
import GafniTao.PintzZetaAFEHybrid

/-!
# Quantitative central kernel for the single-zeta AFE

This file bounds the literal kernel already constructed in
`PintzZetaAFEHybrid`.  The polynomial normalization and the real-Gamma
quotient are kept separate so that the square-root conductor cancellation is
visible in the later finite-head estimate.
-/

open Complex
open scoped ComplexConjugate

namespace GafniTao

noncomputable section

/-- Exact Gaussian norm on a vertical contour. -/
theorem norm_pintzZetaAFE_gaussian_vertical (c u : ℝ) :
    ‖Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2))‖ =
      Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]
  ring

/-- In the central vertical range, the pole-cancelling quadratic numerator
costs at most an absolute factor four after normalization at the physical
point. -/
theorem norm_pintzZetaAFE_polynomial_ratio_le_four
    {r q t u : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1)
    (ht : 4 ≤ t) (hu : |u| ≤ t / 2) :
    ‖(((((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I) *
          (1 - (((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I))) /
        ((((r : ℝ) : ℂ) + (t : ℂ) * I) *
          (1 - (((r : ℝ) : ℂ) + (t : ℂ) * I))))‖ ≤ 4 := by
  let z : ℂ := ((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  have hzRe : 0 ≤ z.re := by simp [z]; linarith
  have hzReUpper : z.re ≤ 1 := by simp [z]; linarith
  have htPos : 0 < t := by linarith
  have htuAbs : |t + u| ≤ 3 * t / 2 := by
    calc
      |t + u| ≤ |t| + |u| := abs_add_le _ _
      _ ≤ t + t / 2 := by rw [abs_of_pos htPos]; gcongr
      _ = 3 * t / 2 := by ring
  have hzNorm : ‖z‖ ≤ 2 * t := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = z.re + |t + u| := by rw [abs_of_nonneg hzRe]; simp [z]
      _ ≤ 1 + 3 * t / 2 := add_le_add hzReUpper htuAbs
      _ ≤ 2 * t := by linarith
  have honezRe : 0 ≤ (1 - z).re := by simp; exact hzReUpper
  have honezReUpper : (1 - z).re ≤ 1 := by simp; exact hzRe
  have honezNorm : ‖1 - z‖ ≤ 2 * t := by
    calc
      ‖1 - z‖ ≤ |(1 - z).re| + |(1 - z).im| :=
        Complex.norm_le_abs_re_add_abs_im (1 - z)
      _ ≤ 1 + 3 * t / 2 := by
        rw [abs_of_nonneg honezRe]
        have him : |(1 - z).im| = |t + u| := by
          simp only [z, sub_im, one_im, add_im, ofReal_im, ofReal_re, mul_im, I_im,
            I_re, mul_one, zero_mul, add_zero, zero_sub]
          simp only [zero_add, abs_neg]
        rw [him]
        gcongr
      _ ≤ 2 * t := by linarith
  have hsNorm : t ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    simpa [s, abs_of_pos htPos] using this
  have honesNorm : t ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simpa [s, abs_of_pos htPos, abs_neg] using this
  have hsNormPos : 0 < ‖s‖ := htPos.trans_le hsNorm
  have honesNormPos : 0 < ‖1 - s‖ := htPos.trans_le honesNorm
  change ‖z * (1 - z) / (s * (1 - s))‖ ≤ 4
  rw [norm_div, norm_mul, norm_mul]
  rw [div_le_iff₀ (mul_pos hsNormPos honesNormPos)]
  calc
    ‖z‖ * ‖1 - z‖ ≤ (2 * t) * (2 * t) :=
      mul_le_mul hzNorm honezNorm (norm_nonneg _) (by positivity)
    _ = 4 * (t * t) := by ring
    _ ≤ 4 * (‖s‖ * ‖1 - s‖) := by
      gcongr

/-- Exact factorization of a displaced coefficient into the Gaussian,
quadratic ratio, real-Gamma ratio, Dirichlet coefficient, and Cauchy kernel.
-/
theorem pintzZetaAFETermContourIntegrand_factor
    (s base : ℂ) (n : ℕ) (w : ℂ) :
    pintzZetaAFETermContourIntegrand s base n w =
      Complex.exp (100 * w ^ 2) *
        (((base + w) * (1 - (base + w))) / (s * (1 - s))) *
        (Complex.Gammaℝ (base + w) / Complex.Gammaℝ s) *
        pintzZetaDirichletTerm (base + w) n / w := by
  unfold pintzZetaAFETermContourIntegrand pintzZetaAFETermNumerator
    pintzZetaAFENormalization
  dsimp only
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact norm of a positive coefficient of the ordinary zeta Dirichlet
series. -/
theorem norm_pintzZetaDirichletTerm_of_ne_zero
    {z : ℂ} {n : ℕ} (hn : n ≠ 0) :
    ‖pintzZetaDirichletTerm z n‖ = (n : ℝ) ^ (-z.re) := by
  have hzeta :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) = 1 := by
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hn]
    norm_num
  rw [pintzZetaDirichletTerm, LSeries.norm_term_eq, if_neg hn, hzeta]
  simp only [norm_one, one_div]
  rw [← Real.rpow_neg (Nat.cast_nonneg n)]

/-- The Cauchy denominator on the left line costs at most `q⁻¹`. -/
theorem norm_inv_neg_real_add_im_le
    {q u : ℝ} (hq : 0 < q) :
    ‖(((-q : ℝ) : ℂ) + (u : ℂ) * I)‖⁻¹ ≤ q⁻¹ := by
  let w : ℂ := ((-q : ℝ) : ℂ) + (u : ℂ) * I
  have hqNorm : q ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    simpa [w, abs_of_pos hq] using h
  exact inv_anti₀ hq hqNorm

/-- The real Gamma factor has the expected norm symmetry across the real
axis.  This is the exact sign bridge needed on the dual side of the AFE. -/
theorem norm_GammaR_real_neg_im_eq (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ := by
  rw [norm_GammaR_real_im, norm_GammaR_real_im]
  congr 1
  have hconj :
      (((r / 2 : ℝ) : ℂ) + (((-t) / 2 : ℝ) : ℂ) * I) =
        conj (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) := by
    simp only [map_add, map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [hconj, Complex.Gamma_conj, norm_conj]

/-- The unshifted dual Gamma quotient contributes precisely the square-root
conductor factor `t^(1/2-r)`, here kept in logarithmic exponential form. -/
theorem exists_norm_GammaR_dual_ratio_le
    {r : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t →
      ‖Complex.Gammaℝ (((1 - r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp (C + Real.log (t / 4 + 2) * (1 / 2 - r)) := by
  let q : ℝ := 2 * r - 1
  have hq : 0 < q := by dsimp only [q]; linarith
  have hqr : q < r := by dsimp only [q]; linarith
  obtain ⟨C, hC, hgamma⟩ :=
    exists_norm_GammaR_left_vertical_ratio_le hq hqr hrUpper.le
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hraw := hgamma t 0 ht (by simp; positivity)
  have hbaseEq :
      ((r - q : ℝ) : ℂ) + (t : ℂ) * I =
        ((1 - r : ℝ) : ℂ) + (t : ℂ) * I := by
    apply Complex.ext
    · simp [q]
      ring
    · simp
  have hsym :
      ‖Complex.Gammaℝ (((1 - r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
        ‖Complex.Gammaℝ (((1 - r : ℝ) : ℂ) + (t : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ := by
    rw [norm_div, norm_div, norm_GammaR_real_neg_im_eq]
  calc
    ‖Complex.Gammaℝ (((1 - r : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
        Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
      ‖Complex.Gammaℝ (((1 - r : ℝ) : ℂ) + (t : ℂ) * I) /
        Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ := hsym
    _ = ‖Complex.Gammaℝ (((r - q : ℝ) : ℂ) + (t : ℂ) * I) /
        Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ := by rw [hbaseEq]
    _ ≤ Real.exp (C + Real.log (t / 4 + 2) * (1 / 2 - r)) := by
      have hexp :
          C - Real.log (t / 4 + 2) * ((2 * r - 1) / 2) =
            C + Real.log (t / 4 + 2) * (1 / 2 - r) := by ring
      simpa only [add_zero, abs_zero, mul_zero, zero_div, q, hexp] using hraw

/-- Literal pointwise central-line majorant for one displaced coefficient on
the original side of the single-zeta AFE.  The conductor factor and the
Dirichlet power are displayed separately; their cancellation at
`n ≈ sqrt t` is performed only in the finite-head consumer. -/
theorem exists_norm_pintzZetaAFETermContourIntegrand_left_central_le
    {r q : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ) (n : ℕ),
      4 ≤ t → |u| ≤ t / 2 → n ≠ 0 →
      ‖pintzZetaAFETermContourIntegrand
          (((r : ℝ) : ℂ) + (t : ℂ) * I)
          (((r : ℝ) : ℂ) + (t : ℂ) * I) n
          (((-q : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        C * Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          (n : ℝ) ^ (-(r - q)) := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_GammaR_left_vertical_ratio_le hq hqr hr
  let C : ℝ := 4 * q⁻¹ * Real.exp (100 * q ^ 2 + Cgamma)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u n ht hu hn
  let s : ℂ := (r : ℂ) + (t : ℂ) * I
  let w : ℂ := ((-q : ℝ) : ℂ) + (u : ℂ) * I
  have hpoly := norm_pintzZetaAFE_polynomial_ratio_le_four
    hq hqr hr ht hu
  have hgam := hgamma t u ht hu
  have hdir : ‖pintzZetaDirichletTerm (s + w) n‖ =
      (n : ℝ) ^ (-(r - q)) := by
    rw [norm_pintzZetaDirichletTerm_of_ne_zero hn]
    congr 1
    simp [s, w]
    ring
  have hwInv := norm_inv_neg_real_add_im_le (u := u) hq
  have hgauss := norm_pintzZetaAFE_gaussian_vertical (-q) u
  have hsw :
      s + w = ((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [s, w]
      ring
    · simp [s, w]
  rw [pintzZetaAFETermContourIntegrand_factor]
  simp only [norm_div, norm_mul]
  rw [hgauss, hdir]
  have hpoly' :
      ‖(s + w) * (1 - (s + w)) / (s * (1 - s))‖ ≤ 4 := by
    rw [hsw]
    simpa only [s] using hpoly
  have hgam' :
      ‖Complex.Gammaℝ (s + w) / Complex.Gammaℝ s‖ ≤
        Real.exp (Cgamma + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2)) := by
    rw [hsw]
    simpa only [s] using hgam
  have hExp :
      Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
          Real.exp (Cgamma + Real.pi * |u| / 4 -
            Real.log (t / 4 + 2) * (q / 2)) =
        Real.exp (100 * q ^ 2 + Cgamma) *
          Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) := by
    repeat' rw [← Real.exp_add]
    congr 1
    ring
  simp only [norm_div, norm_mul] at hpoly' hgam'
  rw [div_eq_mul_inv]
  calc
    Real.exp (100 * (-q) ^ 2 - 100 * u ^ 2) *
          ((‖s + w‖ * ‖1 - (s + w)‖) /
            (‖s‖ * ‖1 - s‖)) *
          (‖Complex.Gammaℝ (s + w)‖ / ‖Complex.Gammaℝ s‖) *
          (n : ℝ) ^ (-(r - q)) * ‖w‖⁻¹ ≤
        Real.exp (100 * q ^ 2 - 100 * u ^ 2) * 4 *
          Real.exp (Cgamma + Real.pi * |u| / 4 -
            Real.log (t / 4 + 2) * (q / 2)) *
          (n : ℝ) ^ (-(r - q)) * q⁻¹ := by
      rw [neg_sq]
      gcongr
    _ = 4 * q⁻¹ *
          (Real.exp (100 * q ^ 2 - 100 * u ^ 2) *
            Real.exp (Cgamma + Real.pi * |u| / 4 -
              Real.log (t / 4 + 2) * (q / 2))) *
          (n : ℝ) ^ (-(r - q)) := by ring
    _ = C * Real.exp (-100 * u ^ 2) *
          Real.exp (Real.pi * |u| / 4) *
          Real.exp (-Real.log (t / 4 + 2) * (q / 2)) *
          (n : ℝ) ^ (-(r - q)) := by
      rw [hExp]
      dsimp only [C]
      ring

#print axioms norm_pintzZetaAFE_gaussian_vertical
#print axioms norm_pintzZetaAFE_polynomial_ratio_le_four
#print axioms pintzZetaAFETermContourIntegrand_factor
#print axioms norm_pintzZetaDirichletTerm_of_ne_zero
#print axioms norm_inv_neg_real_add_im_le
#print axioms norm_GammaR_real_neg_im_eq
#print axioms exists_norm_GammaR_dual_ratio_le
#print axioms exists_norm_pintzZetaAFETermContourIntegrand_left_central_le

end

end GafniTao
