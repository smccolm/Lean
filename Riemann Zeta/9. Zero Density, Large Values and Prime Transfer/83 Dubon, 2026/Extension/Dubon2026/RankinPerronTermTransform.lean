import Dubon2026.RankinConductorMellin
import Dubon2026.GammaRieszDualCutoff

/-! # The exact termwise Mellin transform of the genuine Rankin coefficients -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- Every actual reflected coefficient term has the precise reciprocal conductor and Gamma Mellin factor. -/
theorem rankinPerron_reflected_term {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (s : ℂ) (n : ℕ) :
    ((x : ℂ) ^ (s + 2) * (a : ℂ) ^ (2 * s - 1) * gammaRieszSymbol k 2 s) *
        LSeries.term (rankinConvolutionCoefficients f) (1 - s) n =
      ((a : ℂ)⁻¹ * (rankinConvolutionCoefficients f n / (n : ℂ)) * (x : ℂ) ^ 2) *
        gammaRieszMellinFunction k 2 (a ^ 2 * n * x) s := by
  rw [rankinConvolution_reflected_term]
  by_cases hn : n = 0
  · simp [hn, rankinConvolutionCoefficients_zero]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he := rankin_conductor_mellin_power ha hx hn0 s
    simp only [Complex.ofReal_natCast] at he
    rw [gammaRieszMellinFunction]
    calc
      _ = rankinConvolutionCoefficients f n * gammaRieszSymbol k 2 s *
          ((x : ℂ) ^ (s + 2) * (a : ℂ) ^ (2 * s - 1) * (n : ℂ) ^ (s - 1)) := by ring
      _ = _ := by rw [he]; push_cast; ring

/-- The actual normalized finite integral of each reflected coefficient is exactly the corresponding Gamma cutoff term. -/
theorem rankinPerron_reflected_term_integral {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (T : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t in -T..T,
      ((x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
        (a : ℂ) ^ (2 * gammaVerticalPoint (-1 / 8) t - 1) *
        gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) *
      LSeries.term (rankinConvolutionCoefficients f) (1 - gammaVerticalPoint (-1 / 8) t) n) =
      (a : ℂ)⁻¹ * gammaRieszDualCutoffTerm
        (fun n => (rankinConvolutionCoefficients f n).re) k (a ^ 2) x T n := by
  simp_rw [rankinPerron_reflected_term f ha hx]
  rw [intervalIntegral.integral_const_mul]
  simp only [gammaRieszDualCutoffTerm, gammaRieszVerticalCutoff,
    Complex.ofReal_div, Complex.ofReal_natCast, rankinConvolutionCoefficients_ofReal_re,
    gammaRieszLine, show (3 / 8 : ℝ) - 2 / 4 = -1 / 8 by norm_num, Complex.real_smul]
  ring

end
end Dubon2026
