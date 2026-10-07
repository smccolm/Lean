import Dubon2026.RankinConvolutionGlobalResidue
import Dubon2026.GammaRieszSymbol

/-! # The exact full-level reflection factor for the genuine Rankin series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The two actual completion powers combine to the precise degree-four conductor factor. -/
theorem rankinCompletionPower_reflection (k : ℤ) (s : ℂ) :
    (Real.pi : ℂ) ^ (-(1 - s)) * (4 * Real.pi : ℂ) ^ (-((1 - s) + (k : ℂ) - 1)) *
      (Real.pi : ℂ) ^ s * (4 * Real.pi : ℂ) ^ (s + (k : ℂ) - 1) =
      (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h4π : (4 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  calc
    _ = (Real.pi : ℂ) ^ (-(1 - s) + s) *
        (4 * Real.pi : ℂ) ^ (-((1 - s) + (k : ℂ) - 1) + (s + (k : ℂ) - 1)) := by
      rw [Complex.cpow_add _ _ hπ, Complex.cpow_add _ _ h4π]
      ring
    _ = (Real.pi : ℂ) ^ (2 * s - 1) * (4 * Real.pi : ℂ) ^ (2 * s - 1) := by
      congr 2 <;> ring
    _ = (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) := by
      have hp := Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le
        (show (0 : ℝ) ≤ 4 * Real.pi by positivity) (2 * s - 1)
      push_cast at hp
      rw [← hp]
      congr 1
      ring

/-- Away from zero and one the actual global continuation is the genuine completion times its inverse factor. -/
theorem rankinConvolutionGlobalContinuation_eq_completed {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rankinConvolutionGlobalContinuation f s =
      s * gamma0CompletedCusp f s * rankinConvolutionInverseFactor k s := by
  rw [rankinConvolutionGlobalContinuation, rankinConvolutionEntireNumerator,
    gamma0CuspEntire_eq f hs0 hs1]
  field_simp [sub_ne_zero.mpr hs1]

/-- The literal full-level Rankin continuation reflects to the original absolutely convergent coefficient series. -/
theorem rankinConvolutionGlobalContinuation_reflection {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : s.re < 0) :
    rankinConvolutionGlobalContinuation f s =
      s * (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * Gamma (1 - s) * Gamma ((k : ℂ) - s) /
        (Gamma (s + 1) * Gamma (s + (k : ℂ) - 1)) *
        LSeries (rankinConvolutionCoefficients f) (1 - s) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, one_re] at hs; linarith
  have hr : 1 < (1 - s).re := by simp only [sub_re, one_re]; linarith
  rw [rankinConvolutionGlobalContinuation_eq_completed f hs0 hs1,
    ← gamma0CompletedCusp_levelOne_functional_equation f s,
    gamma0CompletedCusp_eq_convolution f hk hr]
  have he : (1 - s) + (k : ℂ) - 1 = (k : ℂ) - s := by ring
  dsimp only [cuspRankinFactor, rankinConvolutionInverseFactor]
  have hp := rankinCompletionPower_reflection k s
  rw [← hp]
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Gamma recurrence converts the actual reflected Riesz integrand into its order-two kernel symbol. -/
theorem rankinConvolution_riesz_reflection {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2)) =
      (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * gammaRieszSymbol (k : ℝ) 2 s *
        LSeries (rankinConvolutionCoefficients f) (1 - s) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hr; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hh
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hG : Gamma (s + 3) = (s + 2) * (s + 1) * Gamma (s + 1) := by
    rw [show s + 3 = (s + 2) + 1 by ring, Gamma_add_one _ hs2,
      show s + 2 = (s + 1) + 1 by ring, Gamma_add_one _ hs1]
    ring
  rw [rankinConvolutionGlobalContinuation_reflection f hk hr]
  simp only [gammaRieszSymbol, ofReal_add, ofReal_sub, ofReal_one, ofReal_ofNat, ofReal_intCast]
  rw [show s + (2 + 1) = s + 3 by ring, show s + ((k : ℂ) - 1) = s + (k : ℂ) - 1 by ring, hG]
  field_simp [hs0, hs1, hs2]

end
end Dubon2026
