import Dubon2026.ConvolutionSummatory
import Dubon2026.RankinConvolution
import Dubon2026.CuspNormalizedEnergy

/-! # Genuine linear summatory bounds for the nonnegative completed Rankin coefficients -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual zero-or-one principal square coefficient has norm equal to its real part. -/
theorem principalSquareCoefficients_norm (Q n : ℕ) :
    ‖principalSquareCoefficients Q n‖ = (principalSquareCoefficients Q n).re := by
  rcases principalSquareCoefficients_eq_zero_or_one Q n with h | h <;> simp [h]

/-- The true reciprocal principal square weights are summable at the boundary needed for convolution means. -/
theorem principalSquare_reciprocal_summable (Q : ℕ) :
    Summable (fun n : ℕ => (principalSquareCoefficients Q n).re / (n : ℝ)) := by
  have hh := (principalSquare_lseriesSummable Q (s := 1) (by norm_num)).norm
  apply hh.congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_def]
  · simp [hn, principalSquareCoefficients_norm]

/-- Taking real parts of the literal Rankin convolution is exactly the real nonnegative convolution. -/
theorem rankinConvolution_re_eq_real_convolution {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    (rankinConvolutionCoefficients f n).re =
      LSeries.convolution (fun d => (principalSquareCoefficients Q d).re)
        (fun m => ‖normalizedCuspCoefficients f m‖ ^ 2) n := by
  rw [rankinConvolutionCoefficients_eq, LSeries.convolution_def, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro uv _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The actual convolution partial sums have the exact finite hyperbola expansion. -/
theorem rankinConvolution_summatory_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re) =
      ∑ d ∈ Finset.Icc 1 N, (principalSquareCoefficients Q d).re *
        ∑ n ∈ Finset.Icc 1 (N / d), ‖normalizedCuspCoefficients f n‖ ^ 2 := by
  simp_rw [rankinConvolution_re_eq_real_convolution]
  exact sum_convolution_Icc _ _ N

/-- The genuine Rankin convolution satisfies a positive linear summatory bound, derived from the proved cusp energy bound. -/
theorem exists_rankinConvolution_sum_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, (rankinConvolutionCoefficients f n).re) ≤ C * N := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_cusp_square_upper f hk
  let S : ℝ := ∑' n : ℕ, (principalSquareCoefficients Q n).re / (n : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun n => div_nonneg
    (principalSquareCoefficients_re_nonneg Q n) (Nat.cast_nonneg n))
  refine ⟨B * (S + 1), mul_pos hB (by linarith), fun N => ?_⟩
  simp_rw [rankinConvolution_re_eq_real_convolution]
  have hh := sum_convolution_le_linear (principalSquareCoefficients_re_nonneg Q) hB.le hb
    (principalSquare_reciprocal_summable Q) N
  change _ ≤ B * (S + 1) * N
  change _ ≤ B * N * S at hh
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end
end Dubon2026
