import TaoTrudgianYang2025.ZetaSquareDivisorSeries
import TaoTrudgianYang2025.ZetaMomentTransfer

/-!
# Actual critical-line mean-square source entry

The complete ordinary-divisor contour series is normalized back to
`|zeta(1/2+it)|^2`, including at height zero. Its convergence comes from
the integrated norm estimates, not a convention for divergent sums.
This exact entry does not assert the uniform Atkinson local mean-square
estimate or the twelfth-moment bound.
-/

noncomputable section

open Complex MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaSquareGammaNormalization (t : ℝ) : ℂ :=
  Gammaℝ (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint (-t))

theorem zetaSquareGammaNormalization_ne_zero (t : ℝ) :
    zetaSquareGammaNormalization t ≠ 0 := by
  exact mul_ne_zero
    (Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))
    (Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))

theorem zetaSquareGammaNormalization_neg (t : ℝ) :
    zetaSquareGammaNormalization (-t) = zetaSquareGammaNormalization t := by
  simp [zetaSquareGammaNormalization, mul_comm]

theorem completedZeta_square_eq_norm_mul_gamma (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      (zetaMomentCriticalNorm t ^ 2 : ℝ) * zetaSquareGammaNormalization t := by
  have hreflection : completedRiemannZeta (afeCriticalPoint (-t)) =
      completedRiemannZeta (afeCriticalPoint t) := by
    rw [← one_sub_afeCriticalPoint, completedRiemannZeta_one_sub]
  have hnorm : ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) =
      riemannZeta (afeCriticalPoint t) * riemannZeta (afeCriticalPoint (-t)) := by
    rw [riemannZeta_afeCriticalPoint_neg_eq_star]
    simp only [zetaMomentCriticalNorm, afeCriticalPoint, Complex.ofReal_div, Complex.ofReal_one]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    exact mul_comm _ _
  calc
    _ = completedRiemannZeta (afeCriticalPoint t) *
        completedRiemannZeta (afeCriticalPoint (-t)) := by rw [hreflection, pow_two]
    _ = (riemannZeta (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint t)) *
        (riemannZeta (afeCriticalPoint (-t)) * Gammaℝ (afeCriticalPoint (-t))) := by
      rw [completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint]),
        completedRiemannZeta_eq_zeta_mul_GammaR (by norm_num [afeCriticalPoint])]
    _ = _ := by rw [hnorm]; unfold zetaSquareGammaNormalization; ring

def zetaSquareNormalizedContribution (t : ℝ) (n : ℕ) : ℂ :=
  (zetaSquareDivisorContribution t n + zetaSquareDivisorContribution (-t) n) /
    zetaSquareGammaNormalization t

theorem hasSum_zetaSquareNormalizedContribution (t : ℝ) :
    HasSum (zetaSquareNormalizedContribution t) ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) := by
  have h := ((hasSum_zetaSquareDivisorContribution t).add
    (hasSum_zetaSquareDivisorContribution (-t))).div_const (zetaSquareGammaNormalization t)
  rw [← completedZeta_square_eq_divisor_integrals,
    completedZeta_square_eq_norm_mul_gamma,
    mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t)] at h
  exact h

theorem zetaSquareNorm_eq_divisor_series (t : ℝ) :
    zetaMomentCriticalNorm t ^ 2 = (∑' n : ℕ, zetaSquareNormalizedContribution t n).re := by
  rw [(hasSum_zetaSquareNormalizedContribution t).tsum_eq, Complex.ofReal_re]

end TaoTrudgianYang2025
