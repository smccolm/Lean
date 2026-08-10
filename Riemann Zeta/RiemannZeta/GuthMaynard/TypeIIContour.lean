import RiemannZeta.GuthMaynard.GammaVerticalDecay
import RiemannZeta.GuthMaynard.TypeIIZeros
import RiemannZeta.GuthMaynard.ZetaBounds

open Complex MeasureTheory
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- A global linear bound for zeta on the critical line, including the compact
part around height zero. -/
theorem norm_riemannZeta_criticalLine_le (v : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ 4 * (1 + |v|) := by
  let s : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  have hsRe : s.re = 1 / 2 := by simp [s]
  have hsPos : 0 < s.re := by rw [hsRe]; norm_num
  have hsOne : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp [s] at hRe
  have hDen : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 / 2 : ℝ) = |(s - 1).re| := by
        rw [sub_re, hsRe, one_re]
        rw [abs_of_neg (by norm_num)]
        norm_num
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hDenPos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hDen
  have hRem : ‖abelZetaRemainder s‖ ≤ 2 := by
    calc
      ‖abelZetaRemainder s‖ ≤ 1 / s.re := norm_abelZetaRemainder_le hsPos
      _ = 2 := by rw [hsRe]; norm_num
  have hDiv : ‖s‖ / ‖s - 1‖ ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ hDenPos).2
    nlinarith [norm_nonneg s]
  have hNormS : ‖s‖ ≤ 1 + |v| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |v| := by simp [s]; norm_num
  rw [riemannZeta_eq_abel hsPos hsOne]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖
        ≤ ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by
      rw [norm_div, norm_mul]
    _ ≤ 2 * ‖s‖ + ‖s‖ * 2 := add_le_add hDiv
      (mul_le_mul_of_nonneg_left hRem (norm_nonneg s))
    _ = 4 * ‖s‖ := by ring
    _ ≤ 4 * (1 + |v|) := by gcongr

/-- Zeta on a translated critical line is bounded by a fixed multiple of the
linear weight used in `integrable_one_add_abs_mul_typeII_Gamma_horizontal`. -/
theorem norm_riemannZeta_shifted_criticalLine_le (b u : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + ((b + u : ℝ) : ℂ) * I)‖ ≤
      (4 * (1 + |b|)) * (1 + |u|) := by
  calc
    ‖riemannZeta ((1 / 2 : ℂ) + ((b + u : ℝ) : ℂ) * I)‖
        ≤ 4 * (1 + |b + u|) := norm_riemannZeta_criticalLine_le (b + u)
    _ ≤ (4 * (1 + |b|)) * (1 + |u|) := by
      have hTri : |b + u| ≤ |b| + |u| := abs_add_le b u
      nlinarith [abs_nonneg b, abs_nonneg u]

/-- Complex exponentiation with a fixed nonzero base is continuous in the exponent. -/
lemma continuous_const_cpow_of_ne_zero (z : ℂ) (hz : z ≠ 0)
    {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (fun u => z ^ (f u)) := by
  simp_rw [Complex.cpow_def_of_ne_zero hz]
  exact Complex.continuous_exp.comp (continuous_const.mul hf)

/-- The finite Möbius polynomial is continuous on every vertical line. -/
theorem continuous_shortMobiusPolynomial_vertical (T : ℝ) (w : ℂ) :
    Continuous (fun u : ℝ => shortMobiusPolynomial T (w + (u : ℂ) * I)) := by
  unfold shortMobiusPolynomial
  apply continuous_finsetSum
  intro m hm
  apply continuous_const.mul
  have hmPos : 0 < m := by
    have := (Finset.mem_Ico.mp hm).1
    omega
  apply continuous_const_cpow_of_ne_zero (m : ℂ) (by exact_mod_cast (Nat.ne_of_gt hmPos))
  fun_prop

/-- On the critical line, every term of the short Möbius polynomial has norm
at most one. -/
theorem norm_shortMobiusPolynomial_criticalLine_le (T u : ℝ) :
    ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      (detectorCutoff T : ℝ) := by
  unfold shortMobiusPolynomial
  calc
    ‖∑ m ∈ Finset.Ico 1 (detectorCutoff T),
        (ArithmeticFunction.moebius m : ℂ) *
          (m : ℂ) ^ (-((1 / 2 : ℂ) + (u : ℂ) * I))‖
        ≤ ∑ _m ∈ Finset.Ico 1 (detectorCutoff T), (1 : ℝ) := by
          apply norm_sum_le_of_le
          intro m hm
          rw [norm_mul]
          have hMobius := norm_moebius_cast_le_one m
          have hmOne : 1 ≤ m := (Finset.mem_Ico.mp hm).1
          have hmPosReal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmOne)
          have hPow :
              ‖(m : ℂ) ^ (-((1 / 2 : ℂ) + (u : ℂ) * I))‖ ≤ 1 := by
            rw [← Complex.ofReal_natCast]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hmPosReal]
            have hmOneReal : (1 : ℝ) ≤ m := by exact_mod_cast hmOne
            apply Real.rpow_le_one_of_one_le_of_nonpos hmOneReal
            norm_num
          nlinarith [norm_nonneg (ArithmeticFunction.moebius m : ℂ)]
    _ = ((Finset.Ico 1 (detectorCutoff T)).card : ℝ) := by simp
    _ ≤ (detectorCutoff T : ℝ) := by
      norm_cast
      simp [Nat.card_Ico]

/-- The point on the shifted contour always lies on the critical line. -/
lemma rho_add_typeIIContourShift (ρ : ℂ) (u : ℝ) :
    ρ + typeIIContourShift ρ u =
      (1 / 2 : ℂ) + ((ρ.im + u : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [typeIIContourShift]
  · simp [typeIIContourShift]

set_option maxHeartbeats 800000 in
/-- Every integral occurring in the source Type-II detector is a genuine
whole-line Bochner integral, not merely a totalized expression. -/
theorem integrable_typeIIContourIntegrand {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hρLower : 7 / 10 ≤ ρ.re) (hρUpper : ρ.re ≤ 4 / 5) :
    Integrable (typeIIContourIntegrand ρ T) := by
  let a : ℝ := 1 / 2 - ρ.re
  have haLower : -(3 / 10 : ℝ) ≤ a := by dsimp [a]; linarith
  have haUpper : a ≤ -(1 / 5 : ℝ) := by dsimp [a]; linarith
  let base : ℝ → ℂ := fun u =>
    ((1 + |u| : ℝ) : ℂ) * Complex.Gamma ((a : ℂ) + (u : ℂ) * I)
  have hBase : Integrable base := by
    simpa [base] using
      integrable_one_add_abs_mul_typeII_Gamma_horizontal haLower haUpper
  let C : ℝ := T ^ (a / 2) * (detectorCutoff T : ℝ) * (4 * (1 + |ρ.im|))
  have hDom : Integrable (fun u => C * ‖base u‖) := hBase.norm.const_mul C
  apply Integrable.mono' hDom
  · have hPowContinuous : Continuous (fun u : ℝ =>
        (T : ℂ) ^ (typeIIContourShift ρ u / 2)) := by
      apply continuous_const_cpow_of_ne_zero (T : ℂ) (by exact_mod_cast ne_of_gt hT)
      simp only [typeIIContourShift]
      fun_prop
    have hGammaContinuous : Continuous (fun u : ℝ =>
        Complex.Gamma (typeIIContourShift ρ u)) := by
      simpa [typeIIContourShift, a] using
        continuous_typeII_Gamma_horizontal haLower haUpper
    have hMobiusContinuous : Continuous (fun u : ℝ =>
        shortMobiusPolynomial T (ρ + typeIIContourShift ρ u)) := by
      simpa [typeIIContourShift, add_assoc] using
        continuous_shortMobiusPolynomial_vertical T
          (ρ + ((1 / 2 - ρ.re : ℝ) : ℂ))
    have hZetaContinuous : Continuous (fun u : ℝ =>
        riemannZeta (ρ + typeIIContourShift ρ u)) := by
      apply continuous_iff_continuousAt.2
      intro u
      have hPoint : ρ + typeIIContourShift ρ u ≠ 1 := by
        intro h
        have hRe := congrArg Complex.re h
        simp [typeIIContourShift] at hRe
      have hInner : ContinuousAt (fun v : ℝ => ρ + typeIIContourShift ρ v) u := by
        simp only [typeIIContourShift]
        fun_prop
      exact ContinuousAt.comp' (differentiableAt_riemannZeta hPoint).continuousAt hInner
    exact (hPowContinuous.mul hGammaContinuous |>.mul hMobiusContinuous |>.mul
      hZetaContinuous).aestronglyMeasurable
  · filter_upwards with u
    have hShiftRe : (typeIIContourShift ρ u / 2).re = a / 2 := by
      simp [typeIIContourShift, a]
    have hPowNorm : ‖(T : ℂ) ^ (typeIIContourShift ρ u / 2)‖ = T ^ (a / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hT]
      exact congrArg (fun x : ℝ => T ^ x) hShiftRe
    have hCritical := rho_add_typeIIContourShift ρ u
    have hMobius :
        ‖shortMobiusPolynomial T (ρ + typeIIContourShift ρ u)‖ ≤
          (detectorCutoff T : ℝ) := by
      rw [hCritical]
      exact norm_shortMobiusPolynomial_criticalLine_le T (ρ.im + u)
    have hZeta :
        ‖riemannZeta (ρ + typeIIContourShift ρ u)‖ ≤
          (4 * (1 + |ρ.im|)) * (1 + |u|) := by
      rw [hCritical]
      exact norm_riemannZeta_shifted_criticalLine_le ρ.im u
    rw [typeIIContourIntegrand]
    rw [norm_mul, norm_mul, norm_mul, hPowNorm]
    change T ^ (a / 2) * ‖Complex.Gamma (typeIIContourShift ρ u)‖ *
      ‖shortMobiusPolynomial T (ρ + typeIIContourShift ρ u)‖ *
          ‖riemannZeta (ρ + typeIIContourShift ρ u)‖ ≤
      C * ‖base u‖
    have hBaseNorm : ‖base u‖ = (1 + |u|) *
        ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ := by
      dsimp [base]
      rw [norm_mul]
      congr 1
      change ‖Complex.ofReal (1 + |u|)‖ = 1 + |u|
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 + |u| : ℝ))]
    rw [hBaseNorm]
    have hShiftEq : typeIIContourShift ρ u = (a : ℂ) + (u : ℂ) * I := by
      simp [typeIIContourShift, a]
    rw [hShiftEq] at hMobius hZeta ⊢
    dsimp [C]
    calc
      T ^ (a / 2) * ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ *
          ‖shortMobiusPolynomial T (ρ + ((a : ℂ) + (u : ℂ) * I))‖ *
            ‖riemannZeta (ρ + ((a : ℂ) + (u : ℂ) * I))‖
          ≤ T ^ (a / 2) * ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ *
              (detectorCutoff T : ℝ) *
                ((4 * (1 + |ρ.im|)) * (1 + |u|)) := by
            gcongr
      _ = T ^ (a / 2) * (detectorCutoff T : ℝ) * (4 * (1 + |ρ.im|)) *
          ((1 + |u|) * ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖) := by
            ring

end RiemannZeta.GuthMaynard
