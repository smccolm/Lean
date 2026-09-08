import GafniTao.SharpPerronLeftHorizontal

/-!
# Uniform logarithmic derivative on the selected horizontal edges

This file joins the functional-equation half-strip to the direct Landau
disk estimate.  The resulting theorem covers the complete source contour
segment `-1 ≤ Re s ≤ 2`, on both chosen horizontal edges.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

private noncomputable def sharpPerronRightHorizontalConstant : ℝ :=
  (4 / 7 : ℝ) *
    (202 * sharpLandauPartialFractionConstant +
      (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
        sharpLandauMassConstant)

private theorem sharpPerronRightHorizontalConstant_pos :
    0 < sharpPerronRightHorizontalConstant := by
  unfold sharpPerronRightHorizontalConstant
  have hP := sharpLandauPartialFractionConstant_pos
  have hM := sharpLandauMassConstant_pos
  positivity

/-- Complete positive-height logarithmic-derivative estimate on
`-1 ≤ Re s ≤ 2`. -/
theorem exists_norm_riemannZeta_logDeriv_full_positive_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → σ ∈ Set.Icc (-1) 2 →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨Cₗ, hCₗ, hleft⟩ :=
    exists_norm_riemannZeta_logDeriv_left_horizontal_le
  let C := max Cₗ sharpPerronRightHorizontalConstant
  have hC : 0 < C := hCₗ.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T σ R hT hR hσ hfar
  have hlogSq : 0 ≤ Real.log T ^ 2 := sq_nonneg _
  by_cases hs : σ ≤ 1 / 2
  · exact (hleft hT hR ⟨hσ.1, hs⟩ hfar).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogSq)
  · have hright := norm_riemannZeta_logDeriv_positive_horizontal_le
      hT hR ⟨le_of_not_ge hs, hσ.2⟩ hfar
    exact hright.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hlogSq)

/-- Complete negative-height logarithmic-derivative estimate on
`-1 ≤ Re s ≤ 2`. -/
theorem exists_norm_riemannZeta_logDeriv_full_negative_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → σ ∈ Set.Icc (-1) 2 →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) - (R : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C, hC, hpositive⟩ :=
    exists_norm_riemannZeta_logDeriv_full_positive_horizontal_le
  refine ⟨C, hC, ?_⟩
  intro T σ R hT hR hσ hfar
  have hconj : starRingEnd ℂ
      ((σ : ℂ) + (R : ℂ) * I) =
      (σ : ℂ) - (R : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hconj, norm_riemannZeta_logDeriv_conj]
  exact hpositive hT hR hσ hfar

private noncomputable def sharpPerronFarRightConstant : ℝ :=
  ‖deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)‖ + 1

private theorem sharpPerronFarRightConstant_pos :
    0 < sharpPerronFarRightConstant := by
  unfold sharpPerronFarRightConstant
  positivity

/-- The Landau-disk bound joined to the absolutely convergent Dirichlet
series half-plane.  There is deliberately no artificial upper endpoint. -/
theorem exists_norm_riemannZeta_logDeriv_extended_positive_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → -1 ≤ σ →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C₀, hC₀, hbounded⟩ :=
    exists_norm_riemannZeta_logDeriv_full_positive_horizontal_le
  let C := max C₀ sharpPerronFarRightConstant
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T σ R hT hR hσ hfar
  have hlogOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := by linarith
    rw [Real.le_log_iff_exp_le hTpos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hlogSq : 1 ≤ Real.log T ^ 2 := by nlinarith
  by_cases hs : σ ≤ 2
  · exact (hbounded hT hR ⟨hσ, hs⟩ hfar).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · have hdir := dlog_riemannZeta_bdd_on_vertical_lines_generalized
      2 σ R (by norm_num) (le_of_not_ge hs)
    have hneg :
        ‖-deriv riemannZeta ((σ : ℂ) + (R : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ =
          ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ := by
      rw [neg_div, norm_neg]
    rw [hneg] at hdir
    calc
      ‖deriv riemannZeta ((σ : ℂ) + (R : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ ≤
          ‖deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)‖ := hdir
      _ ≤ sharpPerronFarRightConstant := by
        unfold sharpPerronFarRightConstant
        linarith
      _ ≤ C := le_max_right _ _
      _ ≤ C * Real.log T ^ 2 := by
        calc
          C = C * 1 := by ring
          _ ≤ C * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_left hlogSq hC.le

/-- Conjugate version of the extended half-plane estimate. -/
theorem exists_norm_riemannZeta_logDeriv_extended_negative_horizontal_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T σ R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → -1 ≤ σ →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      ‖deriv riemannZeta ((σ : ℂ) - (R : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2 := by
  obtain ⟨C, hC, hpositive⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_positive_horizontal_le
  refine ⟨C, hC, ?_⟩
  intro T σ R hT hR hσ hfar
  have hconj : starRingEnd ℂ
      ((σ : ℂ) + (R : ℂ) * I) =
      (σ : ℂ) - (R : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hconj, norm_riemannZeta_logDeriv_conj]
  exact hpositive hT hR hσ hfar

end GafniTao
