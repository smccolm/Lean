import TaoTrudgianYang2025.ZetaSquareContourShift
import GuthMaynard.HughesYoungEquation84SourceLine
import GuthMaynard.HughesYoungAFE

/-!
# Absolutely integrable right kernel for the one-sided zeta square

The fixed right line is `Re w = 1`, where `Re(s+w) = 3/2` and the actual
ordinary divisor series converges absolutely. The Gaussian majorant below
is sufficient for Tonelli and contour limits. Its constants are not the
uniform local-mean-square remainder required later in the twelfth moment.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaSquareRightKernel (t u : ℝ) : ℂ :=
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    (s * (1 - s)) ^ 2 * Complex.Gammaℝ s ^ 2 /
    zetaSquarePoleNormalization t / w

theorem continuous_zetaSquareRightKernel (t : ℝ) :
    Continuous (zetaSquareRightKernel t) := by
  have hGamma : Continuous (fun u : ℝ =>
      Complex.Gammaℝ (afeCriticalPoint t + (1 + (u : ℂ) * I))) := by
    simpa using continuous_GammaR_afe_vertical t (c := 1) (by norm_num)
  have hw : ∀ u : ℝ, (1 : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    norm_num at this
  unfold zetaSquareRightKernel
  dsimp only
  have haux := differentiable_hughesYoungAuxiliaryZero.continuous
  apply Continuous.div ?_ (by fun_prop) hw
  apply Continuous.div_const
  fun_prop (disch := assumption)

/-- An explicit-degree Gaussian majorant on the complete right line,
with one constant independent of both real height variables. -/
theorem exists_zetaSquareRightKernel_uniform_gaussian_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t u : ℝ,
      ‖zetaSquareRightKernel t u‖ ≤
        C * Real.exp (100 - 100 * u ^ 2) * (3 + |t| + |u|) ^ 12 := by
  let G : ℝ := Real.pi ^ (-(3 / 2 : ℝ) / 2) * Real.Gamma ((3 / 2 : ℝ) / 2)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num))
  let C : ℝ := 10000 * G ^ 2
  refine ⟨C, (by dsimp [C]; positivity), ?_⟩
  intro t u
  have hden := zetaSquarePoleNormalization_norm_lower t
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  let R : ℝ := 3 + |t| + |u|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg t, abs_nonneg u]
  have hwupper : ‖w‖ ≤ 1 + |u| := by
    simpa [w, Real.norm_eq_abs] using norm_add_le (1 : ℂ) ((u : ℂ) * I)
  have hwlower : 1 ≤ ‖w‖ := by
    simpa [w] using Complex.abs_re_le_norm w
  have hwR : ‖w‖ ≤ R := hwupper.trans (by dsimp [R]; linarith [abs_nonneg t])
  have hcrit (v : ℝ) : ‖afeCriticalPoint v‖ ≤ 1 / 2 + |v| := by
    simpa [afeCriticalPoint, Real.norm_eq_abs] using
      norm_add_le ((1 / 2 : ℝ) : ℂ) ((v : ℂ) * I)
  have hsR : ‖s‖ ≤ R := (norm_add_le _ _).trans (by
    dsimp [R]
    linarith [hcrit t])
  have hsubR : ‖1 - s‖ ≤ R := by
    have heq : 1 - s = afeCriticalPoint (-t) - w := by
      dsimp [s]
      rw [← one_sub_afeCriticalPoint]
      ring
    rw [heq]
    apply (norm_sub_le _ _).trans
    have hc := hcrit (-t)
    rw [abs_neg] at hc
    dsimp [R]
    linarith
  have hpoly : ‖(s * (1 - s)) ^ 2‖ ≤ R ^ 4 := by
    rw [norm_pow, norm_mul]
    calc
      _ ≤ (R * R) ^ 2 := by gcongr
      _ = R ^ 4 := by ring
  have haux := norm_hughesYoungAuxiliaryZero_le_polynomial hR hwR
  have hsre : s.re = 3 / 2 := by norm_num [s, w, afeCriticalPoint]
  have hgamma : ‖Complex.Gammaℝ s‖ ≤ G := by
    simpa only [hsre, G] using norm_GammaR_le_realGamma_re
      (show 0 < s.re by rw [hsre]; norm_num)
  have hexp : ‖Complex.exp (100 * w ^ 2)‖ = Real.exp (100 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [w, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  change ‖Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    (s * (1 - s)) ^ 2 * Complex.Gammaℝ s ^ 2 / zetaSquarePoleNormalization t / w‖ ≤ _
  simp only [norm_div, norm_mul, norm_pow, hexp]
  simp only [norm_pow, norm_mul] at hpoly
  calc
    _ ≤ (Real.exp (100 - 100 * u ^ 2) * (625 * R ^ 8) * R ^ 4 * G ^ 2 /
        (1 / 16)) / 1 := by gcongr
    _ = C * Real.exp (100 - 100 * u ^ 2) * R ^ 12 := by dsimp [C]; ring

theorem exists_zetaSquareRightKernel_gaussian_bound (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖zetaSquareRightKernel t u‖ ≤
        C * Real.exp (100 - 100 * u ^ 2) * (3 + |t| + |u|) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaSquareRightKernel_uniform_gaussian_bound
  exact ⟨C, hC, hbound t⟩

theorem integrable_zetaSquareRightKernel (t : ℝ) : Integrable (zetaSquareRightKernel t) := by
  obtain ⟨C, _, hbound⟩ := exists_zetaSquareRightKernel_gaussian_bound t
  apply ((integrable_exp_sub_mul_sq_mul_add_abs_pow (C := 3 + |t|) 100
    (by norm_num : (0 : ℝ) < 100) 12).const_mul C).mono'
    (continuous_zetaSquareRightKernel t).aestronglyMeasurable
  filter_upwards with u
  simpa only [mul_assoc] using hbound u

/-- Exact ordinary-divisor opening of the actual one-sided contour. -/
theorem zetaSquareContourIntegrand_eq_rightKernel_mul_divisor (t u : ℝ) :
    zetaSquareContourIntegrand t (1 + (u : ℂ) * I) =
      zetaSquareRightKernel t u *
        LSeries (fun n : ℕ => (n.divisors.card : ℂ))
          (afeCriticalPoint t + (1 + (u : ℂ) * I)) := by
  let w : ℂ := 1 + (u : ℂ) * I
  let s := afeCriticalPoint t + w
  have hsre : 1 < s.re := by norm_num [s, w, afeCriticalPoint]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold zetaSquareContourIntegrand zetaSquareContourNumerator zetaSquareRightKernel
  change (Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * completedXiNumerator s ^ 2 /
    zetaSquarePoleNormalization t) / w = _
  rw [completedXiNumerator_eq s hs0 hs1,
    completedRiemannZeta_eq_zeta_mul_GammaR (zero_lt_one.trans hsre)]
  simp only [mul_pow]
  rw [riemannZeta_sq_eq_divisorLSeries hsre]
  ring

end TaoTrudgianYang2025
