import GafniTao.SharpPerronHorizontalIntegrand

/-!
# Integrated selected horizontal edges

The pointwise logarithmic-derivative estimate is integrated over the exact
rectangle segment.  The optimized right endpoint and the normalization by
`2πi` remain explicit through the calculation.
-/

open Complex Set MeasureTheory Metric Finset
open RiemannZeta.GuthMaynard
open scoped Interval

noncomputable section

namespace GafniTao

private noncomputable def sharpPerronHorizontalLengthConstant : ℝ :=
  2 + 1 / Real.log 2

private theorem sharpPerronHorizontalLengthConstant_pos :
    0 < sharpPerronHorizontalLengthConstant := by
  unfold sharpPerronHorizontalLengthConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

private theorem sharpPerron_horizontal_length_le
    {y : ℝ} (hy : 2 ≤ y) :
    sharpPerronAbscissa y + 1 ≤ sharpPerronHorizontalLengthConstant := by
  have hc := sharpPerronAbscissa_le_logTwoConstant hy
  unfold sharpPerronHorizontalLengthConstant
  linarith

private theorem sharpPerron_HIntegral_norm_from_pointwise
    {C T y R sign : ℝ} (hC : 0 ≤ C) (hT : 0 < T) (hy : 2 ≤ y)
    (hpoint : ∀ σ ∈ Set.Icc (-1) (sharpPerronAbscissa y),
      ‖sharpZetaPerronIntegrand y
          ((σ : ℂ) + (sign * R : ℝ) * I)‖ ≤
        C * Real.exp 1 * y * Real.log y ^ 2 / T) :
    ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
        (sharpPerronAbscissa y) (sign * R)‖ ≤
      (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
        (C * Real.exp 1 * y * Real.log y ^ 2 / T) := by
  have hc : -1 ≤ sharpPerronAbscissa y := by
    linarith [one_lt_sharpPerronAbscissa (by linarith : 1 < y)]
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => sharpZetaPerronIntegrand y
      ((σ : ℂ) + (sign * R : ℝ) * I))
    (a := (-1 : ℝ)) (b := sharpPerronAbscissa y)
    (C := C * Real.exp 1 * y * Real.log y ^ 2 / T)
    (fun σ hσ => hpoint σ (by
      have hu := Set.uIoc_subset_uIcc hσ
      rw [Set.uIcc_of_le hc] at hu
      exact hu))
  have hlenAbs : |sharpPerronAbscissa y - (-1)| =
      sharpPerronAbscissa y + 1 := by
    rw [abs_of_nonneg]
    · ring
    · linarith
  have hM : 0 ≤ C * Real.exp 1 * y * Real.log y ^ 2 / T := by
    positivity
  have hlen := sharpPerron_horizontal_length_le hy
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
        ‖∫ σ in (-1)..sharpPerronAbscissa y,
          sharpZetaPerronIntegrand y
            ((σ : ℂ) + (sign * R : ℝ) * I)‖ ≤
      (1 / (2 * Real.pi)) *
        ((C * Real.exp 1 * y * Real.log y ^ 2 / T) *
          |sharpPerronAbscissa y - (-1)|) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (1 / (2 * Real.pi)) *
        ((C * Real.exp 1 * y * Real.log y ^ 2 / T) *
          (sharpPerronAbscissa y + 1)) := by rw [hlenAbs]
    _ ≤ (1 / (2 * Real.pi)) *
        ((C * Real.exp 1 * y * Real.log y ^ 2 / T) *
          sharpPerronHorizontalLengthConstant) := by
        gcongr
    _ = (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
        (C * Real.exp 1 * y * Real.log y ^ 2 / T) := by ring

/-- The selected upper horizontal edge is `O(y log² y / T)`. -/
theorem exists_norm_sharpZetaPerron_HIntegral_top_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T y R : ℝ} (hT : 8 ≤ T), 2 ≤ y → T ≤ y →
      R ∈ Set.Icc T (T + 1) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) R‖ ≤
        C * y * Real.log y ^ 2 / T := by
  obtain ⟨C₀, hC₀, hpoint⟩ :=
    exists_norm_sharpZetaPerronIntegrand_positive_horizontal_le
  let C := (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
    (C₀ * Real.exp 1)
  have hC : 0 < C := by
    have hlen := sharpPerronHorizontalLengthConstant_pos
    unfold C
    positivity
  refine ⟨C, hC, ?_⟩
  intro T y R hT hy hTy hR hfar
  have hraw := sharpPerron_HIntegral_norm_from_pointwise
    (T := T) (y := y) hC₀.le (by linarith) hy (sign := 1) (R := R)
    (fun σ hσ => by simpa using hpoint hT hy hTy hR hσ hfar)
  have heq :
      (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
          (C₀ * Real.exp 1 * y * Real.log y ^ 2 / T) =
        C * y * Real.log y ^ 2 / T := by
    dsimp [C]
    ring
  simpa only [one_mul] using hraw.trans_eq heq

/-- The selected lower horizontal edge is `O(y log² y / T)`. -/
theorem exists_norm_sharpZetaPerron_HIntegral_bottom_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T y R : ℝ} (hT : 8 ≤ T), 2 ≤ y → T ≤ y →
      R ∈ Set.Icc T (T + 1) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) (-R)‖ ≤
        C * y * Real.log y ^ 2 / T := by
  obtain ⟨C₀, hC₀, hpoint⟩ :=
    exists_norm_sharpZetaPerronIntegrand_negative_horizontal_le
  let C := (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
    (C₀ * Real.exp 1)
  have hC : 0 < C := by
    have hlen := sharpPerronHorizontalLengthConstant_pos
    unfold C
    positivity
  refine ⟨C, hC, ?_⟩
  intro T y R hT hy hTy hR hfar
  have hraw := sharpPerron_HIntegral_norm_from_pointwise
    (T := T) (y := y) hC₀.le (by linarith) hy (sign := -1) (R := R)
    (fun σ hσ => by
      simpa [sub_eq_add_neg] using hpoint hT hy hTy hR hσ hfar)
  have heq :
      (1 / (2 * Real.pi)) * sharpPerronHorizontalLengthConstant *
          (C₀ * Real.exp 1 * y * Real.log y ^ 2 / T) =
        C * y * Real.log y ^ 2 / T := by
    dsimp [C]
    ring
  simpa only [neg_mul, one_mul] using hraw.trans_eq heq

end GafniTao
