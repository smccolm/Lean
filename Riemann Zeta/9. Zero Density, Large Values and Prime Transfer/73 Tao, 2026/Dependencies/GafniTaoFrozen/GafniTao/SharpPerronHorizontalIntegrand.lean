import GafniTao.SharpPerronHorizontalAll
import GafniTao.SharpPerronRightEdge

/-!
# Pointwise bounds for the complete zeta Perron horizontal integrand

The estimates here retain the literal integrand used by the rectangle
identity.  In particular, the power, denominator, and selected height are
not replaced by abstract bounded weights.
-/

open Complex Set MeasureTheory Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

set_option maxHeartbeats 800000

namespace GafniTao

theorem sharpPerron_extended_positive_zeta_ne_zero
    {T σ R : ℝ} (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hσ : -1 ≤ σ)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    riemannZeta ((σ : ℂ) + (R : ℂ) * I) ≠ 0 := by
  by_cases hs₁ : σ ≤ 1 / 2
  · exact sharpPerron_left_zeta_ne_zero hT hR ⟨hσ, hs₁⟩ hfar
  · by_cases hs₂ : σ ≤ 2
    · rw [← sharpLandauMap_coord]
      exact sharpLandau_physical_zeta_ne_zero hT hR
        ⟨le_of_not_ge hs₁, hs₂⟩ hfar
    · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

theorem sharpPerron_extended_negative_zeta_ne_zero
    {T σ R : ℝ} (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hσ : -1 ≤ σ)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    riemannZeta ((σ : ℂ) - (R : ℂ) * I) ≠ 0 := by
  have hpos := sharpPerron_extended_positive_zeta_ne_zero hT hR hσ hfar
  have hconj : starRingEnd ℂ
      ((σ : ℂ) + (R : ℂ) * I) =
      (σ : ℂ) - (R : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hconj, _root_.riemannZeta_conj]
  exact (map_ne_zero (starRingEnd ℂ)).2 hpos

private theorem sharpPerron_horizontal_point_ne_zero
    {σ R sign : ℝ} (hR : 0 < R) (hsign : |sign| = 1) :
    ((σ : ℂ) + (sign * R : ℝ) * I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hsign0 : sign ≠ 0 := by
    intro hs
    simp [hs] at hsign
  have himEq :
      ((σ : ℂ) + (sign * R : ℝ) * I).im = sign * R := by simp
  rw [himEq] at him
  simp only [Complex.zero_im] at him
  exact (mul_ne_zero hsign0 hR.ne') him

private theorem norm_sharpZetaPerronIntegrand_horizontal_le
    {C T y σ R sign : ℝ}
    (hy : 2 ≤ y) (hT : 8 ≤ T) (hTy : T ≤ y)
    (hR : R ∈ Set.Icc T (T + 1))
    (hσhigh : σ ≤ sharpPerronAbscissa y) (hsign : |sign| = 1)
    (hzeta : riemannZeta
      ((σ : ℂ) + (sign * R : ℝ) * I) ≠ 0)
    (hlogDeriv :
      ‖deriv riemannZeta ((σ : ℂ) + (sign * R : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (sign * R : ℝ) * I)‖ ≤
          C * Real.log T ^ 2)
    (hC : 0 ≤ C) :
    ‖sharpZetaPerronIntegrand y
        ((σ : ℂ) + (sign * R : ℝ) * I)‖ ≤
      C * Real.exp 1 * y * Real.log y ^ 2 / T := by
  let s : ℂ := (σ : ℂ) + (sign * R : ℝ) * I
  have hypos : 0 < y := by linarith
  have hRpos : 0 < R := by linarith [hR.1]
  have hs0 : s ≠ 0 :=
    sharpPerron_horizontal_point_ne_zero hRpos hsign
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    have hsign0 : sign ≠ 0 := by
      intro hs
      simp [hs] at hsign
    have himEq : s.im = sign * R := by simp [s]
    rw [himEq] at him
    simp only [one_im] at him
    exact (mul_ne_zero hsign0 hRpos.ne') him
  have hcpow : ‖(y : ℂ) ^ s‖ = y ^ σ := by
    simpa [s] using Complex.norm_cpow_eq_rpow_re_of_pos hypos s
  have hpow : y ^ σ ≤ Real.exp 1 * y := by
    calc
      y ^ σ ≤ y ^ sharpPerronAbscissa y :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hσhigh
      _ = Real.exp 1 * y := rpow_sharpPerronAbscissa (by linarith)
  have hden : T ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    have hsIm : s.im = sign * R := by simp [s]
    have himEq : |s.im| = R := by
      rw [hsIm, abs_mul, hsign, one_mul, abs_of_pos hRpos]
    rw [himEq] at him
    exact hR.1.trans him
  have hlog : Real.log T ≤ Real.log y :=
    Real.log_le_log (by linarith) hTy
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogY0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogSq : Real.log T ^ 2 ≤ Real.log y ^ 2 := by nlinarith
  have hlogDeriv' :
      ‖deriv riemannZeta s‖ / ‖riemannZeta s‖ ≤
        C * Real.log T ^ 2 := by
    simpa only [norm_div] using hlogDeriv
  rw [sharpZetaPerronIntegrand_eq hs0 hs1 hzeta, logDeriv_apply]
  simp only [norm_mul, norm_neg, norm_div]
  rw [hcpow]
  calc
    (‖deriv riemannZeta s‖ / ‖riemannZeta s‖) *
        (y ^ σ / ‖s‖) ≤
      (C * Real.log T ^ 2) *
        ((Real.exp 1 * y) / T) := by
          exact mul_le_mul hlogDeriv'
            (div_le_div₀ (mul_nonneg (Real.exp_pos 1).le hypos.le) hpow
              (by linarith) hden)
            (div_nonneg (Real.rpow_nonneg hypos.le σ) (norm_nonneg _))
            (mul_nonneg hC (sq_nonneg _))
    _ ≤ (C * Real.log y ^ 2) *
        ((Real.exp 1 * y) / T) := by
          gcongr
    _ = C * Real.exp 1 * y * Real.log y ^ 2 / T := by ring

/-- Positive selected-edge bound for the literal rectangle integrand. -/
theorem exists_norm_sharpZetaPerronIntegrand_positive_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T y σ R : ℝ} (hT : 8 ≤ T), 2 ≤ y → T ≤ y →
      R ∈ Set.Icc T (T + 1) →
      σ ∈ Set.Icc (-1) (sharpPerronAbscissa y) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖sharpZetaPerronIntegrand y
          ((σ : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.exp 1 * y * Real.log y ^ 2 / T := by
  obtain ⟨C, hC, hlog⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_positive_horizontal_le
  refine ⟨C, hC, ?_⟩
  intro T y σ R hT hy hTy hR hσ hfar
  have hzeta : riemannZeta
      ((σ : ℂ) + ((1 : ℝ) * R : ℝ) * I) ≠ 0 := by
    simpa using sharpPerron_extended_positive_zeta_ne_zero
      hT hR hσ.1 hfar
  have hlog' :
      ‖deriv riemannZeta
          ((σ : ℂ) + ((1 : ℝ) * R : ℝ) * I) /
        riemannZeta ((σ : ℂ) + ((1 : ℝ) * R : ℝ) * I)‖ ≤
        C * Real.log T ^ 2 := by
    simpa using hlog hT hR hσ.1 hfar
  have hpoint := norm_sharpZetaPerronIntegrand_horizontal_le
    (C := C) (sign := 1) hy hT hTy hR hσ.2
    (by norm_num) hzeta hlog' hC.le
  simpa only [one_mul] using hpoint

/-- Negative selected-edge bound for the literal rectangle integrand. -/
theorem exists_norm_sharpZetaPerronIntegrand_negative_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T y σ R : ℝ} (hT : 8 ≤ T), 2 ≤ y → T ≤ y →
      R ∈ Set.Icc T (T + 1) →
      σ ∈ Set.Icc (-1) (sharpPerronAbscissa y) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖sharpZetaPerronIntegrand y
          ((σ : ℂ) - (R : ℂ) * I)‖ ≤
        C * Real.exp 1 * y * Real.log y ^ 2 / T := by
  obtain ⟨C, hC, hlog⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_negative_horizontal_le
  refine ⟨C, hC, ?_⟩
  intro T y σ R hT hy hTy hR hσ hfar
  have hzeta := sharpPerron_extended_negative_zeta_ne_zero
    hT hR hσ.1 hfar
  have hzeta' : riemannZeta
      ((σ : ℂ) + ((-1 : ℝ) * R : ℝ) * I) ≠ 0 := by
    simpa [sub_eq_add_neg] using hzeta
  have hlog' :
      ‖deriv riemannZeta
          ((σ : ℂ) + ((-1 : ℝ) * R : ℝ) * I) /
        riemannZeta ((σ : ℂ) + ((-1 : ℝ) * R : ℝ) * I)‖ ≤
        C * Real.log T ^ 2 := by
    simpa [sub_eq_add_neg] using hlog hT hR hσ.1 hfar
  have hpoint := norm_sharpZetaPerronIntegrand_horizontal_le
    (C := C) (sign := -1) hy hT hTy hR hσ.2
    (by norm_num) hzeta' hlog' hC.le
  simpa only [neg_mul, one_mul, ofReal_neg, ofReal_one] using
    hpoint

end GafniTao
