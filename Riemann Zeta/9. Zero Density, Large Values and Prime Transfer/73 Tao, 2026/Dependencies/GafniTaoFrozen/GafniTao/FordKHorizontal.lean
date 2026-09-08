import GafniTao.FordKFiniteEdges
import GafniTao.SharpPerronHorizontalIntegrand
import GafniTao.SharpPerronSelectedHeight

/-!
# Horizontal estimates for Ford's `K(s)` rectangle

The selected-height logarithmic-derivative estimate from the sharp Perron
formalization is applied here to Ford's literal `F₀(s-w)` integrand.  The
distance from `s` to both horizontal edges is proved explicitly.
-/

open Complex Set Filter Topology MeasureTheory
open RiemannZeta.GuthMaynard
open scoped Interval

namespace GafniTao

noncomputable section

/-- Distance from `s` to the upper selected horizontal edge. -/
theorem fordK_upper_weight_distance
    {s : ℂ} {sigma T R : ℝ} (ht : 0 ≤ s.im)
    (hT : 2 * s.im ≤ T) (hR : T ≤ R) :
    T / 2 ≤ ‖s - ((sigma : ℂ) + (R : ℂ) * I)‖ := by
  have him :
      (s - ((sigma : ℂ) + (R : ℂ) * I)).im = s.im - R := by
    simp
  have hRs : s.im ≤ R := by linarith
  have habs :
      |(s - ((sigma : ℂ) + (R : ℂ) * I)).im| = R - s.im := by
    rw [him, abs_of_nonpos (by linarith)]
    ring
  have hcoord := Complex.abs_im_le_norm
    (s - ((sigma : ℂ) + (R : ℂ) * I))
  rw [habs] at hcoord
  linarith

/-- Distance from `s` to the lower selected horizontal edge. -/
theorem fordK_lower_weight_distance
    {s : ℂ} {sigma T R : ℝ} (ht : 0 ≤ s.im) (hT : 0 ≤ T)
    (hR : T ≤ R) :
    T ≤ ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖ := by
  have him :
      (s - ((sigma : ℂ) - (R : ℂ) * I)).im = s.im + R := by
    simp
  have habs :
      |(s - ((sigma : ℂ) - (R : ℂ) * I)).im| = s.im + R := by
    rw [him, abs_of_nonneg (by linarith)]
  have hcoord := Complex.abs_im_le_norm
    (s - ((sigma : ℂ) - (R : ℂ) * I))
  rw [habs] at hcoord
  linarith

/-- Literal pointwise upper-edge bound before replacing the weight distance
by a power of the selected height. -/
theorem norm_fordKSurrogateIntegrand_upper_le
    {s : ℂ} {F₀ : ℂ → ℂ} {C D eta T sigma R : ℝ}
    (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hsigma : -1 ≤ sigma)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * I)‖ ≤ C * Real.log T ^ 2)
    (hweight : 0 ≤ (s - ((sigma : ℂ) + (R : ℂ) * I)).re)
    (heta : eta ≤ ‖s - ((sigma : ℂ) + (R : ℂ) * I)‖)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) + (R : ℂ) * I)‖ ≤
      (C * Real.log T ^ 2) *
        (D / ‖s - ((sigma : ℂ) + (R : ℂ) * I)‖ ^ 2) := by
  have hzeta := sharpPerron_extended_positive_zeta_ne_zero
    hT hR hsigma hfar
  have hw1 : ((sigma : ℂ) + (R : ℂ) * I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      zero_mul, mul_one, zero_add, one_im] at him
    linarith [hR.1]
  rw [fordKSurrogateIntegrand_eq hw1 hzeta, logDeriv_apply]
  rw [norm_mul, norm_neg]
  have hCLog : 0 ≤ C * Real.log T ^ 2 :=
    (norm_nonneg _).trans hlog
  calc
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * I) /
          riemannZeta ((sigma : ℂ) + (R : ℂ) * I)‖ *
        ‖F₀ (s - ((sigma : ℂ) + (R : ℂ) * I))‖ ≤
        (C * Real.log T ^ 2) *
          ‖F₀ (s - ((sigma : ℂ) + (R : ℂ) * I))‖ :=
      mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ ≤ (C * Real.log T ^ 2) *
          (D / ‖s - ((sigma : ℂ) + (R : ℂ) * I)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hF₀ _ hweight heta) hCLog

/-- Literal pointwise lower-edge analogue. -/
theorem norm_fordKSurrogateIntegrand_lower_le
    {s : ℂ} {F₀ : ℂ → ℂ} {C D eta T sigma R : ℝ}
    (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hsigma : -1 ≤ sigma)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ‖deriv riemannZeta ((sigma : ℂ) - (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) - (R : ℂ) * I)‖ ≤ C * Real.log T ^ 2)
    (hweight : 0 ≤ (s - ((sigma : ℂ) - (R : ℂ) * I)).re)
    (heta : eta ≤ ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) - (R : ℂ) * I)‖ ≤
      (C * Real.log T ^ 2) *
        (D / ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖ ^ 2) := by
  have hzeta := sharpPerron_extended_negative_zeta_ne_zero
    hT hR hsigma hfar
  have hw1 : ((sigma : ℂ) - (R : ℂ) * I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      zero_mul, mul_one, zero_sub, one_im] at him
    linarith [hR.1]
  rw [fordKSurrogateIntegrand_eq hw1 hzeta, logDeriv_apply]
  rw [norm_mul, norm_neg]
  have hCLog : 0 ≤ C * Real.log T ^ 2 :=
    (norm_nonneg _).trans hlog
  calc
    ‖deriv riemannZeta ((sigma : ℂ) - (R : ℂ) * I) /
          riemannZeta ((sigma : ℂ) - (R : ℂ) * I)‖ *
        ‖F₀ (s - ((sigma : ℂ) - (R : ℂ) * I))‖ ≤
        (C * Real.log T ^ 2) *
          ‖F₀ (s - ((sigma : ℂ) - (R : ℂ) * I))‖ :=
      mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ ≤ (C * Real.log T ^ 2) *
          (D / ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hF₀ _ hweight heta) hCLog

private theorem fordK_weight_quotient_le
    {D T r : ℝ} (hD : 0 ≤ D) (hT : 0 < T) (hdist : T / 2 ≤ r) :
    D / r ^ 2 ≤ 4 * D / T ^ 2 := by
  have hr : 0 < r := lt_of_lt_of_le (by linarith) hdist
  have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hTSq : 0 < T ^ 2 := sq_pos_of_pos hT
  apply (div_le_iff₀ hrSq).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hTSq).2
  have hsquares : T ^ 2 ≤ 4 * r ^ 2 := by nlinarith [sq_nonneg (2 * r - T)]
  calc
    D * T ^ 2 ≤ D * (4 * r ^ 2) :=
      mul_le_mul_of_nonneg_left hsquares hD
    _ = 4 * D * r ^ 2 := by ring

/-- Uniform upper-edge decay of Ford's literal horizontal integrand. -/
theorem norm_fordKSurrogateIntegrand_upper_le_four_mul
    {s : ℂ} {F₀ : ℂ → ℂ} {C D eta T alpha sigma R : ℝ}
    (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (ht : 0 ≤ s.im) (hheight : 2 * s.im ≤ T)
    (halpha : alpha < s.re) (hsigma : sigma ∈ Set.Icc (-(1 / 2)) alpha)
    (hD : 0 ≤ D) (heta : eta ≤ T / 2)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * I)‖ ≤ C * Real.log T ^ 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) + (R : ℂ) * I)‖ ≤
      4 * C * D * Real.log T ^ 2 / T ^ 2 := by
  have hdist := fordK_upper_weight_distance (sigma := sigma) ht hheight hR.1
  have hraw := norm_fordKSurrogateIntegrand_upper_le
    hT hR (by linarith [hsigma.1]) hfar hlog
    (by simp only [sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero]; linarith [hsigma.2])
    (heta.trans hdist) hF₀
  have hCLog : 0 ≤ C * Real.log T ^ 2 :=
    (norm_nonneg _).trans hlog
  calc
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) + (R : ℂ) * I)‖ ≤
        (C * Real.log T ^ 2) *
          (D / ‖s - ((sigma : ℂ) + (R : ℂ) * I)‖ ^ 2) := hraw
    _ ≤ (C * Real.log T ^ 2) * (4 * D / T ^ 2) :=
      mul_le_mul_of_nonneg_left
        (fordK_weight_quotient_le hD (by linarith) hdist) hCLog
    _ = 4 * C * D * Real.log T ^ 2 / T ^ 2 := by ring

/-- Uniform lower-edge decay of Ford's literal horizontal integrand. -/
theorem norm_fordKSurrogateIntegrand_lower_le_four_mul
    {s : ℂ} {F₀ : ℂ → ℂ} {C D eta T alpha sigma R : ℝ}
    (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (ht : 0 ≤ s.im) (halpha : alpha < s.re)
    (hsigma : sigma ∈ Set.Icc (-(1 / 2)) alpha)
    (hD : 0 ≤ D) (heta : eta ≤ T / 2)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ‖deriv riemannZeta ((sigma : ℂ) - (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) - (R : ℂ) * I)‖ ≤ C * Real.log T ^ 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) - (R : ℂ) * I)‖ ≤
      4 * C * D * Real.log T ^ 2 / T ^ 2 := by
  have hdist := fordK_lower_weight_distance (sigma := sigma) ht (by linarith) hR.1
  have hdist' : T / 2 ≤
      ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖ := by linarith
  have hraw := norm_fordKSurrogateIntegrand_lower_le
    hT hR (by linarith [hsigma.1]) hfar hlog
    (by simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero]; linarith [hsigma.2])
    (heta.trans hdist') hF₀
  have hCLog : 0 ≤ C * Real.log T ^ 2 :=
    (norm_nonneg _).trans hlog
  calc
    ‖fordKSurrogateIntegrand s F₀
        ((sigma : ℂ) - (R : ℂ) * I)‖ ≤
        (C * Real.log T ^ 2) *
          (D / ‖s - ((sigma : ℂ) - (R : ℂ) * I)‖ ^ 2) := hraw
    _ ≤ (C * Real.log T ^ 2) * (4 * D / T ^ 2) :=
      mul_le_mul_of_nonneg_left
        (fordK_weight_quotient_le hD (by linarith) hdist') hCLog
    _ = 4 * C * D * Real.log T ^ 2 / T ^ 2 := by ring

private theorem fordK_HIntegral_norm_from_pointwise
    {s : ℂ} {F₀ : ℂ → ℂ} {alpha height M : ℝ}
    (halpha : -(1 / 2 : ℝ) ≤ alpha)
    (hpoint : ∀ sigma ∈ Set.Icc (-(1 / 2)) alpha,
      ‖fordKSurrogateIntegrand s F₀
          ((sigma : ℂ) + (height : ℂ) * I)‖ ≤ M) :
    ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha height‖ ≤
      (1 / (2 * Real.pi)) * (alpha + 1 / 2) * M := by
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun sigma : ℝ => fordKSurrogateIntegrand s F₀
      ((sigma : ℂ) + (height : ℂ) * I))
    (a := (-(1 / 2) : ℝ)) (b := alpha) (C := M)
    (fun sigma hsigma => hpoint sigma (by
      have hu := Set.uIoc_subset_uIcc hsigma
      rw [Set.uIcc_of_le halpha] at hu
      exact hu))
  have hlen : |alpha - (-(1 / 2 : ℝ))| = alpha + 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    ring
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
    ring
  rw [HIntegral', HIntegral]
  simp only [smul_eq_mul, norm_mul, hscalar]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ sigma in (-(1 / 2 : ℝ))..alpha,
          fordKSurrogateIntegrand s F₀
            ((sigma : ℂ) + (height : ℂ) * I)‖ ≤
      (1 / (2 * Real.pi)) * (M * |alpha - (-(1 / 2 : ℝ))|) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (1 / (2 * Real.pi)) * (alpha + 1 / 2) * M := by
      rw [hlen]
      ring

/-- The exact selected upper horizontal edge in Ford's finite rectangle is
`O((alpha+1/2) D log²(T)/T²)`. -/
theorem exists_norm_fordKSurrogate_HIntegral_top_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {s : ℂ} {F₀ : ℂ → ℂ} {D eta T alpha R : ℝ},
      ∀ (hT : 8 ≤ T), R ∈ Set.Icc T (T + 1) →
      0 ≤ s.im → 2 * s.im ≤ T →
      -(1 / 2) ≤ alpha → alpha < s.re → 0 ≤ D → eta ≤ T / 2 →
      (∀ rho ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T rho).im|) →
      (∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
        ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) →
      ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha R‖ ≤
        C * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 := by
  obtain ⟨C₀, hC₀, hlog⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_positive_horizontal_le
  let C := (1 / (2 * Real.pi)) * (4 * C₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro s F₀ D eta T alpha R hT hR ht hheight halpha has hD heta hfar hF₀
  have hraw := fordK_HIntegral_norm_from_pointwise
    (s := s) (F₀ := F₀) halpha (height := R)
    (fun sigma hsigma =>
      norm_fordKSurrogateIntegrand_upper_le_four_mul
        hT hR ht hheight has hsigma hD heta hfar
        (hlog hT hR (by linarith [hsigma.1]) hfar) hF₀)
  calc
    ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha R‖ ≤
        (1 / (2 * Real.pi)) * (alpha + 1 / 2) *
          (4 * C₀ * D * Real.log T ^ 2 / T ^ 2) := hraw
    _ = C * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 := by
      dsimp [C]
      ring

/-- The corresponding selected lower horizontal edge satisfies the same
uniform decay estimate. -/
theorem exists_norm_fordKSurrogate_HIntegral_bottom_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {s : ℂ} {F₀ : ℂ → ℂ} {D eta T alpha R : ℝ},
      ∀ (hT : 8 ≤ T), R ∈ Set.Icc T (T + 1) →
      0 ≤ s.im → -(1 / 2) ≤ alpha → alpha < s.re →
      0 ≤ D → eta ≤ T / 2 →
      (∀ rho ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T rho).im|) →
      (∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
        ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) →
      ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha (-R)‖ ≤
        C * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 := by
  obtain ⟨C₀, hC₀, hlog⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_negative_horizontal_le
  let C := (1 / (2 * Real.pi)) * (4 * C₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro s F₀ D eta T alpha R hT hR ht halpha has hD heta hfar hF₀
  have hraw := fordK_HIntegral_norm_from_pointwise
    (s := s) (F₀ := F₀) halpha (height := -R)
    (fun sigma hsigma => by
      simpa [sub_eq_add_neg] using
        norm_fordKSurrogateIntegrand_lower_le_four_mul
          hT hR ht has hsigma hD heta hfar
          (hlog hT hR (by linarith [hsigma.1]) hfar) hF₀)
  calc
    ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha (-R)‖ ≤
        (1 / (2 * Real.pi)) * (alpha + 1 / 2) *
          (4 * C₀ * D * Real.log T ^ 2 / T ^ 2) := hraw
    _ = C * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 := by
      dsimp [C]
      ring

/-- A single selected height simultaneously satisfies Ford's exact finite
residue identity and the quantitative estimates for both horizontal edges.
This is the finite-height source assembly prior to taking the vertical-line
and zero-series limits. -/
theorem exists_fordK_selected_rectangle_with_horizontal_bounds :
    ∃ Ctop Cbottom : ℝ, 0 < Ctop ∧ 0 < Cbottom ∧
      ∀ {s : ℂ} {F₀ : ℂ → ℂ} {alpha D eta T : ℝ},
      ∀ (hT : 8 ≤ T), 1 < alpha → alpha < s.re →
      0 ≤ s.im → 2 * s.im ≤ T → 0 ≤ D → eta ≤ T / 2 →
      (∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) →
      (∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
        ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) →
      ∃ R : ℝ, R ∈ Set.Icc T (T + 1) ∧
        (∀ rho ∈ sharpLandauZeroFinset T hT,
          1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
            |R - (sharpLandauMap T rho).im|) ∧
        (∀ rho ∈ zeroSet 0 R, |rho.im| < R) ∧
        VIntegral' (fordKSurrogateIntegrand s F₀) alpha (-R) R =
          F₀ (s - 1) -
              ∑ rho ∈ zeroSet 0 R,
                (analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho) -
            HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha (-R) +
            HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha R +
            VIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) (-R) R ∧
        ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha R‖ ≤
          Ctop * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 ∧
        ‖HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha (-R)‖ ≤
          Cbottom * (alpha + 1 / 2) * D * Real.log T ^ 2 / T ^ 2 := by
  obtain ⟨Ctop, hCtop, htop⟩ := exists_norm_fordKSurrogate_HIntegral_top_le
  obtain ⟨Cbottom, hCbottom, hbottom⟩ :=
    exists_norm_fordKSurrogate_HIntegral_bottom_le
  refine ⟨Ctop, Cbottom, hCtop, hCbottom, ?_⟩
  intro s F₀ alpha D eta T hT halpha has ht hheight hD heta hdiff hF₀
  obtain ⟨R, hR, hfar, hstrict⟩ := exists_sharpPerron_residue_good_height hT
  refine ⟨R, hR, hfar, hstrict, ?_, ?_, ?_⟩
  · exact fordK_rightEdge_eq_residues_add_edges
      halpha (by linarith [hR.1]) has hstrict hdiff
  · exact htop hT hR ht hheight (by linarith) has hD heta hfar hF₀
  · exact hbottom hT hR ht (by linarith) has hD heta hfar hF₀

end

end GafniTao
