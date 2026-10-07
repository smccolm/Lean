import Dubon2026.RankinDeconvolution
import Dubon2026.RankinConvolutionMean
import Dubon2026.ConvolutionPowerRemainder

/-! # Transfer of genuine quantitative Rankin errors to normalized cusp coefficient squares -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The true complex convolution partial sum is exactly the real nonnegative coefficient sum embedded in C. -/
theorem rankinConvolution_complexSummatory {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) :
    complexCoefficientSummatory (rankinConvolutionCoefficients f) x =
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re : ℝ) : ℂ) := by
  simp only [complexCoefficientSummatory, Complex.ofReal_sum, rankinConvolutionCoefficients_ofReal_re]

/-- The genuine inverted convolution partial sum is the literal normalized cusp square sum. -/
theorem rankinDeconvolution_complexSummatory {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) (x : ℝ) :
    complexCoefficientSummatory
      (LSeries.convolution (moebiusSquareCoefficients Q) (rankinConvolutionCoefficients f)) x =
        (squareSummatory (normalizedCuspCoefficients f) x : ℂ) := by
  simp only [complexCoefficientSummatory, rankin_deconvolution_coefficients f hk,
    squareSummatory, Complex.ofReal_sum]

/-- The actual inverse Dirichlet-series value cancels the true principal-square residue factor exactly. -/
theorem rankinConvolutionResidue_mul_moebiusSquare {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    (rankinConvolutionResidue f : ℂ) * LSeries (moebiusSquareCoefficients Q) 1 = (cuspRankinResidue f : ℂ) := by
  have hp : LSeries (principalSquareCoefficients Q) 1 = (principalSquareMass Q : ℂ) := by
    rw [principalSquare_LSeries Q (by norm_num), mul_one]
    exact (principalSquareMass_eq_LFunction Q).symm
  have hc := principalSquare_mul_moebiusSquare_LSeries Q (s := 1) (by norm_num)
  rw [hp] at hc
  simp only [rankinConvolutionResidue, Complex.ofReal_mul]
  calc
    _ = ((principalSquareMass Q : ℂ) * LSeries (moebiusSquareCoefficients Q) 1) *
        (cuspRankinResidue f : ℂ) := by ring
    _ = _ := by rw [hc, one_mul]

/-- A quantitative bound on the actual completed convolution transfers, by its proved Möbius inversion, to the exact cusp square sum and genuine Petersson residue. -/
theorem exists_cusp_square_remainder_of_rankinConvolution {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
        C * x ^ (3 / 5 : ℝ)) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      |squareSummatory (normalizedCuspCoefficients f) x - cuspRankinResidue f * x| ≤ D * x ^ (3 / 5 : ℝ) := by
  have hbC (x : ℝ) (hx : 1 ≤ x) :
      ‖complexCoefficientSummatory (rankinConvolutionCoefficients f) x - (rankinConvolutionResidue f : ℂ) * x‖ ≤
        C * x ^ (3 / 5 : ℝ) := by
    rw [rankinConvolution_complexSummatory, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hb x hx
  have hb0 := complexCoefficientSummatory_bound_nonneg hC (by norm_num : (3 / 5 : ℝ) ≤ 1) hbC
  let S : ℝ := ∑' n : ℕ, ‖LSeries.term (moebiusSquareCoefficients Q) ((3 / 5 : ℝ) : ℂ) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun n => norm_nonneg _)
  refine ⟨(C + ‖(rankinConvolutionResidue f : ℂ)‖) * S + 1, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have he := complexCoefficientSummatory_convolution_power_bound (by norm_num : (3 / 5 : ℝ) ≤ 1)
    (moebiusSquare_lseriesSummable Q (s := ((3 / 5 : ℝ) : ℂ)) (by norm_num)) hb0 hx0
  rw [rankinDeconvolution_complexSummatory f hk] at he
  have hc : (rankinConvolutionResidue f : ℂ) * (x : ℂ) * LSeries (moebiusSquareCoefficients Q) 1 =
      ((cuspRankinResidue f * x : ℝ) : ℂ) := by
    rw [mul_right_comm, rankinConvolutionResidue_mul_moebiusSquare, Complex.ofReal_mul]
  rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  apply he.trans
  change (C + ‖(rankinConvolutionResidue f : ℂ)‖) * x ^ (3 / 5 : ℝ) * S ≤ _
  nlinarith [Real.rpow_nonneg hx0 (3 / 5 : ℝ)]

end
end Dubon2026
