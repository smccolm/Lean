import TaoTrudgianYang2025.ZetaSquareRealSource
import TaoTrudgianYang2025.PointValueLowMoment

/-!
# The genuine fourth moment and its one-sided contour source

The source is the actual completed-zeta contour already proved in the
package, normalized by its genuine Gamma factors. No mollifier occurs.
The pointwise fourth-power bound retains the full contour contribution.
-/

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaFourthRightPiece (t : ℝ) : ℂ :=
  zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t

theorem zetaSquareNorm_eq_two_re_fourthRightPiece (t : ℝ) :
    zetaMomentCriticalNorm t^2 = 2*(zetaFourthRightPiece t).re :=
  zetaSquareNorm_eq_reflected_source t

theorem zetaFourthRightPiece_neg (t : ℝ) :
    zetaFourthRightPiece (-t) = conj (zetaFourthRightPiece t) := by
  simp only [zetaFourthRightPiece, neg_neg, zetaSquareGammaNormalization_neg,
    map_div₀, conj_zetaSquareGammaNormalization,
    zetaSquareDivisorIntegral_conj, conj_conj]

theorem zetaFourthRightPiece_re_nonneg (t : ℝ) :
    0 ≤ (zetaFourthRightPiece t).re := by
  have h := zetaSquareNorm_eq_two_re_fourthRightPiece t
  nlinarith [sq_nonneg (zetaMomentCriticalNorm t)]

theorem zeta_fourth_le_four_mul_rightPiece_sq (t : ℝ) :
    zetaMomentCriticalNorm t^4 ≤ 4*‖zetaFourthRightPiece t‖^2 := by
  have h := zetaSquareNorm_eq_two_re_fourthRightPiece t
  have hre := Complex.re_le_norm (zetaFourthRightPiece t)
  have hn := zetaFourthRightPiece_re_nonneg t
  have hs := pow_le_pow_left₀ hn hre 2
  nlinarith [sq_nonneg (zetaMomentCriticalNorm t^2 - 2*(zetaFourthRightPiece t).re)]

theorem norm_zetaSquareGammaNormalization (t : ℝ) :
    ‖zetaSquareGammaNormalization t‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖^2 := by
  have he : ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint t)‖ := by
    have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) :=
      afeCriticalPoint_neg_eq_star t
    rw [hs, gammaReal_conj, Complex.norm_conj]
  rw [zetaSquareGammaNormalization, norm_mul, he, pow_two]

theorem norm_gammaSquare_div_zetaSquareGammaNormalization (t : ℝ) (w : ℂ) :
    ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t‖ =
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ := by
  rw [norm_div, norm_pow, norm_zetaSquareGammaNormalization,
    norm_pow, norm_div, div_pow]

theorem zeta_fourth_integral_le_four_mul_rightPiece_sq
    {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => ‖zetaFourthRightPiece t‖^2) volume a b) :
    (∫ t in a..b, zetaMomentCriticalNorm t^4) ≤
      4*(∫ t in a..b, ‖zetaFourthRightPiece t‖^2) := by
  have hz : IntervalIntegrable (fun t => zetaMomentCriticalNorm t^4) volume a b :=
    (continuous_zetaMomentCriticalNorm.pow 4).intervalIntegrable a b
  calc
    _ ≤ ∫ t in a..b, 4*‖zetaFourthRightPiece t‖^2 :=
      intervalIntegral.integral_mono_on hab hz (hint.const_mul 4)
        (fun t _ => zeta_fourth_le_four_mul_rightPiece_sq t)
    _ = _ := intervalIntegral.integral_const_mul _ _

end TaoTrudgianYang2025
