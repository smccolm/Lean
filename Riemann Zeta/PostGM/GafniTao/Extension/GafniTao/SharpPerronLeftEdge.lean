import GafniTao.SharpPerronLeftVertical

/-!
# The integrated left edge of the sharp Perron rectangle

The logarithmic derivative estimate on `Re s = -1` is inserted into the
literal Perron integrand and integrated on the exact segment `[-R,R]`.
No abstract contour-error hypothesis is introduced.
-/

open Complex Set MeasureTheory
open scoped Interval

noncomputable section

namespace GafniTao

/-- Pointwise estimate for the literal sharp Perron integrand on `Re s=-1`. -/
theorem exists_norm_sharpZetaPerronIntegrand_left_vertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {y t : ℝ}, 2 ≤ y →
      ‖sharpZetaPerronIntegrand y ((-1 : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.log (|t| + 2) / y := by
  obtain ⟨C, hC, hlogDeriv⟩ :=
    exists_norm_riemannZeta_logDeriv_left_vertical_le
  refine ⟨C, hC, ?_⟩
  intro y t hy
  let s : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hypos : 0 < y := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hzeta : riemannZeta s ≠ 0 :=
    sharpPerron_left_vertical_zeta_ne_zero t
  have hcpow : ‖(y : ℂ) ^ s‖ = y⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos]
    have hsre : s.re = -1 := by simp [s]
    rw [hsre, Real.rpow_neg_one]
  have hden : 1 ≤ ‖s‖ := by
    have hre := Complex.abs_re_le_norm s
    have hsre : s.re = -1 := by simp [s]
    rw [hsre] at hre
    norm_num at hre
    exact hre
  have hpowDen : y⁻¹ / ‖s‖ ≤ 1 / y := by
    calc
      y⁻¹ / ‖s‖ ≤ y⁻¹ / 1 :=
        div_le_div_of_nonneg_left (inv_nonneg.mpr hypos.le) (by norm_num) hden
      _ = 1 / y := by rw [div_one, one_div]
  have hlogDeriv' :
      ‖deriv riemannZeta s‖ / ‖riemannZeta s‖ ≤
        C * Real.log (|t| + 2) := by
    simpa only [norm_div] using hlogDeriv t
  have hlogNonneg : 0 ≤ Real.log (|t| + 2) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  rw [show ((-1 : ℂ) + (t : ℂ) * I) = s from rfl]
  rw [sharpZetaPerronIntegrand_eq hs0 hs1 hzeta, logDeriv_apply]
  simp only [norm_mul, norm_neg, norm_div, hcpow]
  exact mul_le_mul hlogDeriv' (by simpa [one_div] using hpowDen)
    (div_nonneg (inv_nonneg.mpr hypos.le) (norm_nonneg _))
    (mul_nonneg hC.le hlogNonneg)

/-- The normalized left vertical edge has the exact pre-simplification bound
`(2π)⁻¹ · (C log(R+2)/y) · 2R`. -/
theorem exists_norm_sharpZetaPerron_VIntegral_left_raw_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {y R : ℝ}, 2 ≤ y → 0 ≤ R →
      ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
        (1 / (2 * Real.pi)) *
          ((C * Real.log (R + 2) / y) * (2 * R)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_sharpZetaPerronIntegrand_left_vertical_le
  refine ⟨C, hC, ?_⟩
  intro y R hy hR
  have hR2pos : 0 < R + 2 := by linarith
  have hM : 0 ≤ C * Real.log (R + 2) / y := by
    exact div_nonneg
      (mul_nonneg hC.le (Real.log_nonneg (by linarith))) (by linarith)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R)
    (C := C * Real.log (R + 2) / y)
    (f := fun t : ℝ =>
      sharpZetaPerronIntegrand y ((-1 : ℂ) + (t : ℂ) * I))
    (fun t ht => by
      have htmem := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at htmem
      have htAbs : |t| ≤ R := (abs_le).2 htmem
      have hlog : Real.log (|t| + 2) ≤ Real.log (R + 2) := by
        apply Real.log_le_log
        · linarith [abs_nonneg t]
        · linarith
      exact (hpoint hy).trans (by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hC.le) (by linarith)))
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ =
      1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I]
    ring
  rw [VIntegral', VIntegral]
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, one_mul, hscalar]
  have hint' :
      ‖∫ t in (-R)..R,
          sharpZetaPerronIntegrand y (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        (C * Real.log (R + 2) / y) * |R - (-R)| := by
    simpa using hint
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t in (-R)..R,
          sharpZetaPerronIntegrand y (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      (1 / (2 * Real.pi)) *
        ((C * Real.log (R + 2) / y) * |R - (-R)|) := by
          exact mul_le_mul_of_nonneg_left hint' (by positivity)
    _ = (1 / (2 * Real.pi)) *
        ((C * Real.log (R + 2) / y) * (2 * R)) := by
          rw [show R - -R = 2 * R by ring, abs_of_nonneg (by positivity)]

/-- The left vertical edge is absorbed by the same `y log² y / T` error
budget as the selected horizontal edges. -/
theorem exists_norm_sharpZetaPerron_VIntegral_left_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T y R : ℝ}, 8 ≤ T → 2 ≤ y → T ≤ y →
      R ∈ Set.Icc T (T + 1) →
      ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
        C * y * Real.log y ^ 2 / T := by
  obtain ⟨C₀, hC₀, hraw⟩ :=
    exists_norm_sharpZetaPerron_VIntegral_left_raw_le
  let C : ℝ := (1 / (2 * Real.pi)) * (9 / 2 : ℝ) * C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro T y R hT hy hTy hR
  have hTpos : 0 < T := by linarith
  have hypos : 0 < y := by linarith
  have hRnonneg : 0 ≤ R := by linarith [hR.1]
  have hRbound : R ≤ (9 / 8 : ℝ) * T := by
    calc
      R ≤ T + 1 := hR.2
      _ ≤ (9 / 8 : ℝ) * T := by nlinarith
  have hRratio : R / y ≤ (9 / 8 : ℝ) * (y / T) := by
    rw [show (9 / 8 : ℝ) * (y / T) = ((9 / 8 : ℝ) * y) / T by ring]
    rw [div_le_div_iff₀ hypos hTpos]
    nlinarith [sq_nonneg (y - T)]
  have hRlog : Real.log (R + 2) ≤ 2 * Real.log y := by
    have hR2pos : 0 < R + 2 := by linarith
    have hle1 : R + 2 ≤ T + 3 := by linarith [hR.2]
    have hle2 : T + 3 ≤ y ^ 2 := by
      nlinarith [sq_nonneg (y - 1)]
    calc
      Real.log (R + 2) ≤ Real.log (y ^ 2) :=
        Real.log_le_log hR2pos (hle1.trans hle2)
      _ = 2 * Real.log y := by
        rw [show y ^ 2 = y ^ (2 : ℝ) by
          exact (Real.rpow_natCast y 2).symm, Real.log_rpow hypos]
  have hlogNonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hraw' := hraw hy hRnonneg
  calc
    ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
        (1 / (2 * Real.pi)) *
          ((C₀ * Real.log (R + 2) / y) * (2 * R)) := hraw'
    _ ≤ (1 / (2 * Real.pi)) *
          ((C₀ * (2 * Real.log y) / y) * (2 * R)) := by
            gcongr
    _ = (1 / (2 * Real.pi)) * 4 * C₀ *
          Real.log y * (R / y) := by ring
    _ ≤ (1 / (2 * Real.pi)) * 4 * C₀ *
          Real.log y * ((9 / 8 : ℝ) * (y / T)) := by
            gcongr
    _ ≤ C * y * Real.log y ^ 2 / T := by
            dsimp [C]
            have hlogOne : 1 ≤ Real.log y := by
              apply (Real.le_log_iff_exp_le hypos).2
              exact Real.exp_one_lt_three.le.trans
                ((by norm_num : (3 : ℝ) ≤ 8).trans (hT.trans hTy))
            field_simp [Real.pi_ne_zero, hTpos.ne']
            nlinarith [hlogNonneg]

end GafniTao
