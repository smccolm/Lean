import Dubon2026.RieszSecondError
import Dubon2026.RankinConvolutionMean

/-! # Positive Riesz smoothing for the actual Rankin convolution coefficients -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The literal second Riesz mean of the real nonnegative Rankin convolution coefficients. -/
def rankinConvolutionRiesz {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℝ → ℝ :=
  rieszSecondSum (fun n => (rankinConvolutionCoefficients f n).re)

/-- The actual Riesz error after subtracting the cubic main term with the proved Rankin residue. -/
def rankinConvolutionRieszError {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℝ → ℝ :=
  rieszSecondError (fun n => (rankinConvolutionCoefficients f n).re) (rankinConvolutionResidue f)

/-- The genuine Rankin Riesz mean is exactly the source's quadratic finite coefficient sum. -/
theorem rankinConvolutionRiesz_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) :
    rankinConvolutionRiesz f x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (rankinConvolutionCoefficients f n).re * (x - n) ^ 2 / 2 :=
  rieszSecondSum_eq _ x

/-- Actual forward and backward Rankin Riesz means bracket the true unsmoothed coefficient sum. -/
theorem rankinConvolution_riesz_bounds {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    rieszSecondDifference (rankinConvolutionRiesz f) (x - 2 * h) h / h ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) ∧
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) ≤
      rieszSecondDifference (rankinConvolutionRiesz f) x h / h ^ 2 :=
  realCoefficientSummatory_riesz_bounds (rankinConvolutionCoefficients_re_nonneg f) x hh

/-- The actual Rankin counting error is bounded by genuine second differences, without any arithmetic estimate supplied as a hypothesis. -/
theorem rankinConvolution_error_le_riesz {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
      rankinConvolutionResidue f * h +
      max |rieszSecondDifference (rankinConvolutionRieszError f) x h|
        |rieszSecondDifference (rankinConvolutionRieszError f) (x - 2 * h) h| / h ^ 2 :=
  realCoefficientSummatory_error_le_riesz (rankinConvolutionCoefficients_re_nonneg f) _ x hh

end
end Dubon2026
