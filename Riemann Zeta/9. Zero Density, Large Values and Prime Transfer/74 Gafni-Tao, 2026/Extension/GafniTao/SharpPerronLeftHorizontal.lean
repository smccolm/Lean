import GafniTao.SharpPerronHorizontalSymmetry
import GafniTao.SharpPerronFunctionalEquation

/-!
# The left half of the Perron horizontal edge

The completed-zeta functional equation reflects `-1 ≤ Re s ≤ 1/2` into
the already controlled strip.  Digamma is shifted once into the positive
half-plane and bounded by the proved vertical-strip series estimate.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Gammaℝ s ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
  apply hs
  have him := congrArg Complex.im hn
  simpa using him

theorem riemannZeta_ne_zero_of_reflected
    {s : ℂ} (hs0 : s ≠ 0) (h1s0 : 1 - s ≠ 0)
    (hΓs : Gammaℝ s ≠ 0)
    (href : riemannZeta (1 - s) ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hcompS : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hΓs
  have hcompRef : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompS
  apply href
  rw [riemannZeta_def_of_ne_zero h1s0, hcompRef, zero_div]

theorem sharpPerron_reflected_zeta_ne_zero
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (-1) (1 / 2))
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    riemannZeta (1 - ((σ : ℂ) + (R : ℂ) * Complex.I)) ≠ 0 := by
  have hσref : 1 - σ ∈ Set.Icc (1 / 2) 2 := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hpos := sharpLandau_physical_zeta_ne_zero hT hR hσref hfar
  rw [sharpLandauMap_coord] at hpos
  let u : ℂ := ((1 - σ : ℝ) : ℂ) + (R : ℂ) * Complex.I
  have hreflect : 1 - ((σ : ℂ) + (R : ℂ) * Complex.I) =
      starRingEnd ℂ u := by
    apply Complex.ext <;> simp [u]
  rw [hreflect, _root_.riemannZeta_conj]
  simpa [u] using ((map_ne_zero (starRingEnd ℂ)).2 hpos)

theorem sharpPerron_left_zeta_ne_zero
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (-1) (1 / 2))
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) ≠ 0 := by
  let s : ℂ := (σ : ℂ) + (R : ℂ) * Complex.I
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hR.1
  have hsIm : s.im = R := by simp [s]
  have hrefIm : (1 - s).im = -R := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hsIm] at this
    linarith
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hrefIm] at this
    linarith
  apply riemannZeta_ne_zero_of_reflected hs0 h1s0
  · exact Gammaℝ_ne_zero_of_im_ne_zero (by rw [hsIm]; linarith)
  · exact sharpPerron_reflected_zeta_ne_zero hT hR hσ hfar

theorem sharpPerron_digamma_shift {s : ℂ}
    (hpoles : ∀ m : ℕ, s / 2 ≠ -m) :
    digamma (s / 2) = digamma ((s + 2) / 2) - (s / 2)⁻¹ := by
  have hrec := digamma_apply_add_one (s / 2) hpoles
  rw [show s / 2 + 1 = (s + 2) / 2 by ring] at hrec
  linear_combination -hrec

theorem sharpPerron_digamma_poles_avoided
    {s : ℂ} (hsIm : s.im ≠ 0) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m h
  apply hsIm
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- Uniform logarithmic-square bound on the positive-height left half-edge. -/
theorem exists_norm_riemannZeta_logDeriv_left_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → σ ∈ Set.Icc (-1) (1 / 2) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * Complex.I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C₁, hC₁, hdig₁⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1) (b := 5 / 2)
      (by norm_num)
  obtain ⟨C₂, hC₂, hdig₂⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1 / 2) (b := 2)
      (by norm_num)
  let H : ℝ := (4 / 7 : ℝ) *
    (202 * sharpLandauPartialFractionConstant +
      (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
        sharpLandauMassConstant)
  have hH : 0 ≤ H := by
    have hP : 0 ≤ sharpLandauPartialFractionConstant :=
      sharpLandauPartialFractionConstant_pos.le
    have hM : 0 ≤ sharpLandauMassConstant := sharpLandauMassConstant_pos.le
    unfold H
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) hP)
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hM))
  refine ⟨|Real.log Real.pi| + H + 2 * C₁ + C₂ + 2, ?_, ?_⟩
  · nlinarith [abs_nonneg (Real.log Real.pi), hC₁.le, hC₂.le]
  intro T σ R hT hR hσ hfar
  let s : ℂ := (σ : ℂ) + (R : ℂ) * Complex.I
  have hRpos : 0 < R := by linarith [hR.1]
  have hTpos : 0 < T := by linarith
  have hlogOne : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hlogNonneg : 0 ≤ Real.log T := by linarith
  have hsIm : s.im = R := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hsIm] at this
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [hsIm] at this
    linarith
  have hζs := sharpPerron_left_zeta_ne_zero hT hR hσ hfar
  have hζref := sharpPerron_reflected_zeta_ne_zero hT hR hσ hfar
  have hFE := sharpPerron_zeta_logDeriv_functional_eq hs1 hs0 hζs hζref
  have hσref : 1 - σ ∈ Set.Icc (1 / 2) 2 := by
    constructor <;> linarith [hσ.1, hσ.2]
  have hrefBound := norm_riemannZeta_logDeriv_negative_horizontal_le
    hT hR hσref hfar
  have hRlog : Real.log (R + 2) ≤ 2 * Real.log T := by
    have hR2pos : 0 < R + 2 := by linarith
    have hle1 : R + 2 ≤ T + 3 := by linarith [hR.2]
    have hle2 : T + 3 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    have hle : R + 2 ≤ T ^ 2 := hle1.trans hle2
    calc
      Real.log (R + 2) ≤ Real.log (T ^ 2) :=
        Real.log_le_log hR2pos hle
      _ = 2 * Real.log T := by
        rw [show T ^ 2 = T ^ (2 : ℝ) by
          exact (Real.rpow_natCast T 2).symm, Real.log_rpow hTpos]
  have hshiftReLow : (1 : ℝ) ≤ (s + 2).re := by simp [s]; linarith [hσ.1]
  have hshiftReHigh : (s + 2).re ≤ (5 / 2 : ℝ) := by simp [s]; linarith [hσ.2]
  have hrefReLow : (1 / 2 : ℝ) ≤ (1 - s).re := by simp [s]; linarith [hσ.2]
  have hrefReHigh : (1 - s).re ≤ (2 : ℝ) := by simp [s]; linarith [hσ.1]
  have hdigShift := hdig₁ (s + 2) hshiftReLow hshiftReHigh
  have hdigRef := hdig₂ (1 - s) hrefReLow hrefReHigh
  have himShift : |(s + 2).im| = R := by simp [s, abs_of_pos hRpos]
  have himRef : |(1 - s).im| = R := by simp [s, abs_of_pos hRpos]
  rw [himShift] at hdigShift
  rw [himRef] at hdigRef
  have hdigShift' : ‖digamma ((s + 2) / 2)‖ ≤
      2 * C₁ * Real.log T := by
    exact hdigShift.trans (by
      calc
        C₁ * Real.log (R + 2) ≤ C₁ * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hRlog hC₁.le
        _ = 2 * C₁ * Real.log T := by ring)
  have hdigRef' : ‖digamma ((1 - s) / 2)‖ ≤
      2 * C₂ * Real.log T := by
    exact hdigRef.trans (by
      calc
        C₂ * Real.log (R + 2) ≤ C₂ * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hRlog hC₂.le
        _ = 2 * C₂ * Real.log T := by ring)
  have hpoles := sharpPerron_digamma_poles_avoided
    (s := s) (by rw [hsIm]; linarith)
  have hshiftEq := sharpPerron_digamma_shift hpoles
  have hinv : ‖(s / 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one₀]
    · have himle := Complex.abs_im_le_norm (s / 2)
      have hsdivIm : (s / 2).im = R / 2 := by simp [s]
      rw [hsdivIm, abs_of_pos (by linarith)] at himle
      have hRhalf : 1 ≤ R / 2 := by linarith [hR.1, hT]
      exact hRhalf.trans himle
    · exact norm_pos_iff.mpr (div_ne_zero hs0 (by norm_num))
  have hdigS : ‖digamma (s / 2)‖ ≤
      2 * C₁ * Real.log T + 1 := by
    rw [hshiftEq]
    exact (norm_sub_le _ _).trans (add_le_add hdigShift' hinv)
  have hnormFE :
      ‖deriv riemannZeta s / riemannZeta s‖ ≤
        |Real.log Real.pi| + H * Real.log T ^ 2 +
          (1 / 2 : ℝ) *
            ((2 * C₁ * Real.log T + 1) +
              2 * C₂ * Real.log T) := by
    have hnegNorm : ‖-deriv riemannZeta s / riemannZeta s‖ =
        ‖deriv riemannZeta s / riemannZeta s‖ := by
      rw [neg_div, norm_neg]
    rw [← hnegNorm, hFE]
    calc
      ‖(((-Real.log Real.pi : ℝ) : ℂ) +
          deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
            (1 / 2 : ℂ) *
              (digamma (s / 2) + digamma ((1 - s) / 2))‖ ≤
          ‖((-Real.log Real.pi : ℝ) : ℂ)‖ +
            ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ +
              ‖(1 / 2 : ℂ) *
                (digamma (s / 2) + digamma ((1 - s) / 2))‖ := by
        calc
          _ ≤ ‖(((-Real.log Real.pi : ℝ) : ℂ) +
              deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖ +
                ‖(1 / 2 : ℂ) *
                  (digamma (s / 2) + digamma ((1 - s) / 2))‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ |Real.log Real.pi| + H * Real.log T ^ 2 +
          (1 / 2 : ℝ) *
            ((2 * C₁ * Real.log T + 1) +
              2 * C₂ * Real.log T) := by
        have hhalfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
        rw [norm_real, Real.norm_eq_abs, abs_neg, norm_mul, hhalfNorm]
        gcongr
        · rw [show 1 - s = ((1 - σ : ℝ) : ℂ) - (R : ℂ) * Complex.I by
            apply Complex.ext <;> simp [s]]
          exact hrefBound
        · exact (norm_add_le _ _).trans (add_le_add hdigS hdigRef')
  change ‖deriv riemannZeta s / riemannZeta s‖ ≤ _
  exact hnormFE.trans (by
    have hLsq : 1 ≤ Real.log T ^ 2 := by nlinarith
    have hLle : Real.log T ≤ Real.log T ^ 2 := by nlinarith
    have habs : |Real.log Real.pi| ≤
        |Real.log Real.pi| * Real.log T ^ 2 := by
      calc
        |Real.log Real.pi| = |Real.log Real.pi| * 1 := by ring
        _ ≤ |Real.log Real.pi| * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_left hLsq (abs_nonneg _)
    have hC₁L : C₁ * Real.log T ≤ C₁ * Real.log T ^ 2 :=
      mul_le_mul_of_nonneg_left hLle hC₁.le
    have hC₂L : C₂ * Real.log T ≤ C₂ * Real.log T ^ 2 :=
      mul_le_mul_of_nonneg_left hLle hC₂.le
    nlinarith [hH, hC₁.le, hC₂.le])

/-- The same left-half-strip estimate on the conjugate horizontal edge. -/
theorem exists_norm_riemannZeta_logDeriv_left_negative_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → σ ∈ Set.Icc (-1) (1 / 2) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) - (R : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) - (R : ℂ) * Complex.I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_riemannZeta_logDeriv_left_horizontal_le
  refine ⟨C, hC, ?_⟩
  intro T σ R hT hR hσ hfar
  have hconj : starRingEnd ℂ
      ((σ : ℂ) + (R : ℂ) * Complex.I) =
      (σ : ℂ) - (R : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [← hconj, norm_riemannZeta_logDeriv_conj]
  exact hbound hT hR hσ hfar

end GafniTao
