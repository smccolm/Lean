import Dubon2026.DivisorRectangularDual
import Dubon2026.RectangularConductorPower

/-! # Exact finite-component Riesz reflection of the actual general-level Rankin series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The exact positive degree-four conductor of the genuine component indexed by a level divisor. -/
def divisorRankinConductor (Q d : ℕ) : ℝ :=
  (4 * Real.pi ^ 2) ^ 2 / ((Q : ℝ) ^ 2 * (d : ℝ))

/-- The actual Mobius coefficient and diagonal slash normalization give this signed component amplitude. -/
def divisorRankinAmplitude (Q d : ℕ) (k : ℤ) : ℂ :=
  (ArithmeticFunction.moebius d : ℂ) * ((Q / d : ℕ) : ℂ) ^ (k - 2) *
    (Q : ℂ) ^ k / (4 * Real.pi ^ 2 : ℂ)

/-- Every component conductor is strictly positive at a genuine divisor of a positive level. -/
theorem divisorRankinConductor_pos {Q : ℕ} [NeZero Q] (d : Q.divisors) :
    0 < divisorRankinConductor Q d.val := by
  have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_neZero Q)
  have hd : (0 : ℝ) < d.val := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors d.property)
  unfold divisorRankinConductor
  positivity

/-- Gamma recurrence cancels the literal Riesz denominator of the reflected common-period completion. -/
theorem cuspTraceRankinFactor_riesz_reflection {Q : ℕ} [NeZero Q] (k : ℤ) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    s * cuspTraceRankinFactor Q k (1 - s) * rankinConvolutionInverseFactor k s /
      (s * (s + 1) * (s + 2)) =
        (Q : ℂ) ^ ((k : ℂ) - s) * (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * gammaRieszSymbol (k : ℝ) 2 s := by
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
  have hp := rankinCompletionPower_reflection k s
  rw [cuspTraceRankinFactor_eq_width, ← hp]
  simp only [cuspRankinFactor, rankinConvolutionInverseFactor, gammaRieszSymbol,
    ofReal_add, ofReal_sub, ofReal_one, ofReal_ofNat, ofReal_intCast]
  rw [show (1 - s) + (k : ℂ) - 1 = (k : ℂ) - s by ring,
    show s + (2 + 1) = s + 3 by ring,
    show s + ((k : ℂ) - 1) = s + (k : ℂ) - 1 by ring, hG]
  field_simp [hs0, hs1, hs2]

/-- The actual Rankin continuation reflects to a finite family of genuine cusp coefficient series, each with its precise positive conductor and signed amplitude. -/
theorem general_rankinConvolution_riesz_reflection {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    rankinConvolutionGlobalContinuation f s / (s * (s + 1) * (s + 2)) =
      ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k *
        (divisorRankinConductor Q d.val : ℂ) ^ s * gammaRieszSymbol (k : ℝ) 2 s *
          LSeries (divisorRectangularDualCoefficients f d) (1 - s) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hr; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, one_re] at hr; linarith
  rw [rankinConvolutionGlobalContinuation_eq_completed f hs0 hs1,
    gamma0CompletedCusp_reflected_dual f hk hr, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_neZero Q)
  have hd : (0 : ℝ) < d.val := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors d.property)
  have hp := rectangular_completion_power_reflection hQ hd k s
  push_cast at hp
  calc
    _ = (ArithmeticFunction.moebius d.val : ℂ) * ((Q / d.val : ℕ) : ℂ) ^ (k - 2) *
        ((Q : ℂ) * d.val) ^ (-s) *
          (s * cuspTraceRankinFactor Q k (1 - s) * rankinConvolutionInverseFactor k s /
            (s * (s + 1) * (s + 2))) * LSeries (divisorRectangularDualCoefficients f d) (1 - s) := by
      simp only [rectangularDualFactor, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)]
      ring
    _ = _ := by
      rw [cuspTraceRankinFactor_riesz_reflection k hl hr]
      have he := congrArg (fun t : ℂ => (ArithmeticFunction.moebius d.val : ℂ) *
        ((Q / d.val : ℕ) : ℂ) ^ (k - 2) * t * gammaRieszSymbol (k : ℝ) 2 s *
          LSeries (divisorRectangularDualCoefficients f d) (1 - s)) hp
      unfold divisorRankinAmplitude divisorRankinConductor
      push_cast at he ⊢
      convert he using 1 <;> ring

end
end Dubon2026
