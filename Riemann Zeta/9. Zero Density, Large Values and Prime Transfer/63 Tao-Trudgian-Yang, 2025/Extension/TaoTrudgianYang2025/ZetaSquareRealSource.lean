import TaoTrudgianYang2025.ZetaDivisorWeightFreezing

/-!
# The real zeta square and the reflected divisor source

Conjugation pairs the two actual right contours. This turns the normalized
source and its proved frozen-weight approximation into statements about
the real critical-line zeta square, including the correct factor two.
-/

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem divisorDirichletTerm_conj (s : ℂ) (n : ℕ) :
    divisorDirichletTerm (conj s) n = conj (divisorDirichletTerm s n) := by
  have hpow := Complex.cpow_conj (n : ℂ) (-s)
    (by rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
        exact Real.pi_ne_zero.symm)
  simp only [map_neg, map_natCast] at hpow
  simp only [divisorDirichletTerm_eq_divisorWeight_mul_cpow, map_mul, divisorWeight,
    map_natCast, hpow]

theorem zetaSquareRightKernel_conj (t u : ℝ) :
    zetaSquareRightKernel (-t) (-u) = conj (zetaSquareRightKernel t u) := by
  have hw : (1 : ℂ) + ((-u : ℝ) : ℂ) * I = conj (1 + (u : ℂ) * I) := by simp
  have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) := afeCriticalPoint_neg_eq_star t
  unfold zetaSquareRightKernel
  dsimp only
  rw [hw, hs, ← map_add, gammaReal_conj]
  simp only [hughesYoungAuxiliaryZero, zetaSquarePoleNormalization_eq,
    map_div₀, map_mul, map_pow, map_sub, map_ofNat, map_one, conj_ofReal, ← Complex.exp_conj]
  simp only [neg_sq]

theorem zetaSquareDivisorTerm_conj (t u : ℝ) (n : ℕ) :
    zetaSquareDivisorTerm (-t) n (-u) = conj (zetaSquareDivisorTerm t n u) := by
  have hs : afeCriticalPoint (-t) + (1 + ((-u : ℝ) : ℂ) * I) =
      conj (afeCriticalPoint t + (1 + (u : ℂ) * I)) := by
    rw [afeCriticalPoint_neg_eq_star]
    simp
  simp only [zetaSquareDivisorTerm, hs, divisorDirichletTerm_conj, zetaSquareRightKernel_conj, map_mul]

theorem zetaSquareDivisorContribution_conj (t : ℝ) (n : ℕ) :
    zetaSquareDivisorContribution (-t) n = conj (zetaSquareDivisorContribution t n) := by
  unfold zetaSquareDivisorContribution
  rw [← integral_neg_eq_self (zetaSquareDivisorTerm (-t) n) volume]
  simp_rw [zetaSquareDivisorTerm_conj, integral_conj]
  simp only [map_mul, map_div₀, map_one, map_ofNat, conj_ofReal]

theorem zetaSquareDivisorIntegral_conj (t : ℝ) :
    zetaSquareDivisorIntegral (-t) = conj (zetaSquareDivisorIntegral t) := by
  rw [← (hasSum_zetaSquareDivisorContribution (-t)).tsum_eq,
    ← (hasSum_zetaSquareDivisorContribution t).tsum_eq, Complex.conj_tsum]
  congr 1
  funext n
  exact zetaSquareDivisorContribution_conj t n

theorem conj_zetaSquareGammaNormalization (t : ℝ) :
    conj (zetaSquareGammaNormalization t) = zetaSquareGammaNormalization t := by
  have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) := afeCriticalPoint_neg_eq_star t
  simp only [zetaSquareGammaNormalization, hs, gammaReal_conj, map_mul, conj_conj]
  ring

/-- The full source entry, not just its reflected branch. -/
theorem zetaSquareNorm_eq_reflected_source (t : ℝ) :
    zetaMomentCriticalNorm t ^ 2 =
      2 * (zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t).re := by
  have h : ((zetaMomentCriticalNorm t ^ 2 : ℝ) : ℂ) =
      (zetaSquareDivisorIntegral t + zetaSquareDivisorIntegral (-t)) /
        zetaSquareGammaNormalization t := by
    rw [← completedZeta_square_eq_divisor_integrals, completedZeta_square_eq_norm_mul_gamma,
      mul_div_cancel_right₀ _ (zetaSquareGammaNormalization_ne_zero t)]
  have hc : zetaSquareDivisorIntegral t / zetaSquareGammaNormalization t =
      conj (zetaSquareDivisorIntegral (-t) / zetaSquareGammaNormalization t) := by
    rw [map_div₀, conj_zetaSquareGammaNormalization, zetaSquareDivisorIntegral_conj, conj_conj]
  rw [add_div, hc] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.conj_re, two_mul] using hr

/-- The actual zeta square is approximated by the complete frozen
oscillatory source on the closed half-height window. -/
theorem exists_abs_zetaSquareNorm_sub_frozen_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 8 ≤ T → ∀ x : ℝ, |x| ≤ T / 2 →
      |zetaMomentCriticalNorm (T + x) ^ 2 - 2 * (zetaSquareFrozenDivisorIntegral T x).re| ≤
        C * (1 + |x| * T ^ (-1 / 2 + ε)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSquareSource_sub_frozen_le ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT x hx
  rw [zetaSquareNorm_eq_reflected_source, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ‖zetaSquareDivisorIntegral (-(T + x)) / zetaSquareGammaNormalization (T + x) -
        zetaSquareFrozenDivisorIntegral T x‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm
        (zetaSquareDivisorIntegral (-(T + x)) / zetaSquareGammaNormalization (T + x) -
          zetaSquareFrozenDivisorIntegral T x)
    _ ≤ 2 * (C * (1 + |x| * T ^ (-1 / 2 + ε))) :=
      mul_le_mul_of_nonneg_left (hbound T hT x hx) (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025
