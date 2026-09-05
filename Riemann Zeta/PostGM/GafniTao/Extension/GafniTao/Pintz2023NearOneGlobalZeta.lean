import GafniTao.Pintz2023MellinMoment
import GafniTao.PintzNearOneZetaSum
import RiemannZeta.GuthMaynard.HughesYoungShiftRegularization

/-!
# A global-height form of Pintz's near-one zeta estimate

The large-height estimate is the native coefficient-one-half bound.  On the
remaining compact height range we use the holomorphic pole-removed zeta
factor and retain the exact distance `1 - sigma` from the pole.
-/

open Complex Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

private theorem exists_uniform_norm_riemannZetaPoleRemoved_four_le :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℂ, ‖z‖ ≤ 4 →
      ‖riemannZetaPoleRemoved z‖ ≤ D := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 4) :=
    isCompact_closedBall _ _
  obtain ⟨z₀, hz₀, hmax⟩ := hcompact.exists_isMaxOn
    (by exact ⟨0, by simp⟩)
    (differentiable_riemannZetaPoleRemoved.continuous.norm.continuousOn)
  let D : ℝ := max 1 ‖riemannZetaPoleRemoved z₀‖
  refine ⟨D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 4 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact (hmax hzmem).trans (le_max_right _ _)

/-- Pintz's coefficient-one-half zeta estimate, continued uniformly through
bounded heights with the distance from the pole displayed explicitly. -/
theorem exists_norm_riemannZeta_le_pintz_nearOne_global
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ),
      11 / 12 ≤ sigma → sigma < 1 →
      ‖riemannZeta ((sigma : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 - sigma)⁻¹ *
          (|t| + 3) ^ ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨C₀, hC₀, hlarge⟩ :=
    norm_riemannZeta_le_pintz_nearOne hepsilon
  obtain ⟨D, hD, hcompact⟩ :=
    exists_uniform_norm_riemannZetaPoleRemoved_four_le
  let C : ℝ := max C₀ D
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigmaLower hsigmaUpper
  let d : ℝ := 1 - sigma
  let p : ℝ := (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon
  have hd : 0 < d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 := by dsimp only [d]; linarith
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hbase : 1 ≤ |t| + 3 := by linarith [abs_nonneg t]
  have hbasePow : 1 ≤ (|t| + 3) ^ p :=
    Real.one_le_rpow (by linarith) hp.le
  have hInvOne : 1 ≤ d⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hd).2 hdUpper
  by_cases ht : 3 ≤ |t|
  · have hPositive := hlarge sigma |t| (by linarith) hsigmaLower ht
    have hSymmetry := norm_riemannZeta_height_abs sigma t
    have hFord : fordComplexHeight sigma |t| = sigma + I * |t| := by
      simp [fordComplexHeight, mul_comm]
    rw [hFord] at hPositive
    have hAbsPow : |t| ^ p ≤ (|t| + 3) ^ p := by
      exact Real.rpow_le_rpow (abs_nonneg t) (by linarith) hp.le
    calc
      ‖riemannZeta ((sigma : ℂ) + I * (t : ℂ))‖ =
          ‖riemannZeta ((sigma : ℂ) + I * ((|t| : ℝ) : ℂ))‖ := by
            simpa using hSymmetry
      _ ≤ C₀ * |t| ^ p := by simpa only [d, p] using hPositive
      _ ≤ C * |t| ^ p := by
        gcongr
        exact le_max_left _ _
      _ ≤ C * (|t| + 3) ^ p := by gcongr
      _ ≤ C * d⁻¹ * (|t| + 3) ^ p := by
        have hpowNonneg : 0 ≤ (|t| + 3) ^ p := by positivity
        nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hInvOne)]
  · have htUpper : |t| < 3 := lt_of_not_ge ht
    let z : ℂ := ((sigma : ℂ) + I * (t : ℂ)) - 1
    have hzRe : z.re = -d := by
      dsimp only [z, d]
      simp
    have hzIm : z.im = t := by simp [z]
    have hzNorm : ‖z‖ ≤ 4 := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = d + |t| := by rw [hzRe, hzIm, abs_neg, abs_of_pos hd]
        _ ≤ 4 := by linarith
    have hz : z ≠ 0 := by
      intro hzero
      have := congrArg Complex.re hzero
      rw [hzRe] at this
      simp at this
      linarith
    have hZetaPoint :
        (sigma : ℂ) + I * (t : ℂ) = 1 + z := by
      dsimp only [z]
      ring
    have hRemoved := riemannZetaPoleRemoved_eq_mul_riemannZeta hz
    have hNormZ : d ≤ ‖z‖ := by
      rw [← abs_of_pos hd, ← abs_neg d, ← hzRe]
      exact Complex.abs_re_le_norm z
    have hZeta :
        ‖riemannZeta ((sigma : ℂ) + I * (t : ℂ))‖ ≤ D / d := by
      rw [hZetaPoint]
      have hEq : ‖riemannZeta (1 + z)‖ =
          ‖riemannZetaPoleRemoved z‖ / ‖z‖ := by
        rw [hRemoved, norm_mul]
        field_simp [norm_ne_zero_iff.mpr hz]
      rw [hEq]
      exact (div_le_div_of_nonneg_right (hcompact z hzNorm) (norm_nonneg z)).trans
        (div_le_div_of_nonneg_left hD.le hd hNormZ)
    calc
      ‖riemannZeta ((sigma : ℂ) + I * (t : ℂ))‖ ≤ D / d := hZeta
      _ ≤ C * d⁻¹ := by
        rw [div_eq_mul_inv]
        gcongr
        exact le_max_right _ _
      _ ≤ C * d⁻¹ * (|t| + 3) ^ p := by
        exact le_mul_of_one_le_right (by positivity) hbasePow

#print axioms exists_norm_riemannZeta_le_pintz_nearOne_global

end

end GafniTao
