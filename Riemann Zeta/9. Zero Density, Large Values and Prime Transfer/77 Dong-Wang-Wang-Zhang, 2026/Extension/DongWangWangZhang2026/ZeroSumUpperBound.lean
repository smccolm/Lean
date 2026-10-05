import DongWangWangZhang2026.XiLogDerivative
import DongWangWangZhang2026.GammaLogBounds
import DongWangWangZhang2026.ZetaLogDerivativeBounds

/-!
# The source zero-sum upper bound

Lemma 3.4 is assembled for the actual multiplicity-indexed xi zeros.
The harmonic digamma estimate and the von Mangoldt pole estimate retain
the source coefficients one half and one, uniformly for every positive
horizontal displacement and both signs of the height.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex

/-- The rational factors are uniformly bounded away from the real axis. -/
theorem norm_one_div_le_half_of_two_le_abs_im {s : ℂ} (hs : 2 ≤ |s.im|) :
    ‖1 / s‖ ≤ 1 / 2 := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by norm_num) (hs.trans (abs_im_le_norm s))

/-- Source Lemma 3.4, with actual zero multiplicity and absolute convergence. -/
theorem exists_source_zero_sum_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : ℝ, 0 < a → 2 ≤ |v| →
      Summable (fun p : XiZero =>
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p)).re) ∧
      (∑' p : XiZero,
        (1 / ((((1 + a : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p)).re) ≤
        (1 / 2) * Real.log (2 + a + |v|) + 1 / a + C := by
  obtain ⟨Cζ, hCζ, hzeta⟩ := exists_norm_logDeriv_zeta_le_pole
  refine ⟨Cζ + (14 + |Real.eulerMascheroniConstant|) / 2 +
    |Real.log Real.pi| / 2 + 1, by positivity, ?_⟩
  intro a v ha hv
  let s : ℂ := ((1 + a : ℝ) : ℂ) + (v : ℂ) * I
  have hre : s.re = 1 + a := by simp [s]
  have him : s.im = v := by simp [s]
  have hs : 1 < s.re := by rw [hre]; linarith
  obtain ⟨hconv, hid⟩ := tsum_xiZero_re_eq_zeta_gamma hs
  refine ⟨hconv, ?_⟩
  have hrat₀ := norm_one_div_le_half_of_two_le_abs_im (s := s) (by simpa [him] using hv)
  have hrat₁ := norm_one_div_le_half_of_two_le_abs_im (s := s - 1) (by simpa [him] using hv)
  have hr₀ := (re_le_norm (1 / s)).trans hrat₀
  have hr₁ := (re_le_norm (1 / (s - 1))).trans hrat₁
  have hζ := (re_le_norm (logDeriv riemannZeta s)).trans (hzeta s hs)
  rw [hre, add_sub_cancel_left] at hζ
  have hΓ := re_digamma_source_upper ha hv
  change (logDeriv Gamma (s / 2)).re ≤
    Real.log (2 + a + |v|) + (14 + |Real.eulerMascheroniConstant|) at hΓ
  have hπ : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    simp [Complex.log_re]
  change (∑' p : XiZero, (1 / (s - xiZeroPoint p)).re) ≤ _
  rw [hid]
  simp only [add_re, sub_re, div_ofNat_re, hπ]
  linarith [neg_abs_le (Real.log Real.pi)]

end
end DongWangWangZhang2026
