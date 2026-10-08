import Dubon2026.CuspMellinFEPair
import Dubon2026.PrimitiveFirstSpectralConvergence
import Dubon2026.ExponentialMellinSeries
import Dubon2026.CuspFourierEnergy

/-! # Exact Mellin identity for the original normalized cusp coefficient L-series -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Set MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- The genuine imaginary-axis values have their actual exponentially decaying Fourier expansion. -/
theorem cuspVerticalProfile_hasSum {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => cuspCoefficients f n *
      (Real.exp (-((2 * Real.pi) * n) * y) : ℂ)) (cuspVerticalProfile f y) := by
  have he := cuspCoefficients_hasSum f ⟨(y : ℂ) * Complex.I, by simpa using hy⟩
  have hq : Function.Periodic.qParam 1 ((y : ℂ) * Complex.I) =
      (Real.exp (-2 * Real.pi * y) : ℂ) := by
    simpa using qParam_horizontal_period 0 y
  rw [cuspVerticalProfile, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  convert he using 1
  funext n
  rw [hq, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  ring_nf

/-- The exact half-weight shift identifies every original and normalized L-series term, including the zero index. -/
theorem cusp_coefficient_lseries_term_shift {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) (n : ℕ) :
    LSeries.term (cuspCoefficients f) (s + ((k : ℂ) - 1) / 2) n =
      LSeries.term (normalizedCuspCoefficients f) s n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      normalizedCuspCoefficients, shiftedCoefficients]
    push_cast
    simp only [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [mul_assoc, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    congr 2
    ring

/-- The actual original coefficient series is summable at the exact shifted parameter. -/
theorem cusp_raw_lseries_summable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cuspCoefficients f) (s + ((k : ℂ) - 1) / 2) :=
  (normalized_cusp_lseries_summable f hk hs).congr
    (fun n => (cusp_coefficient_lseries_term_shift f s n).symm)

/-- The genuine cusp Mellin completion has the exact one-Gamma normalization of the original coefficient L-series. -/
theorem cuspCompletedLFunction_eq_normalized_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    cuspCompletedLFunction f (s + ((k : ℂ) - 1) / 2) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + ((k : ℂ) - 1) / 2)) *
        Complex.Gamma (s + ((k : ℂ) - 1) / 2) * LSeries (normalizedCuspCoefficients f) s := by
  have hz : 0 < (s + ((k : ℂ) - 1) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.intCast_re, Complex.one_re]
    have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have he := mellin_exponential_series (cuspCoefficients_zero f) hz
    (cusp_raw_lseries_summable f hk hs) (by positivity : 0 < 2 * Real.pi)
    (fun _ hy => cuspVerticalProfile_hasSum f hy)
  have hs' : LSeries (cuspCoefficients f) (s + ((k : ℂ) - 1) / 2) =
      LSeries (normalizedCuspCoefficients f) s :=
    tsum_congr (cusp_coefficient_lseries_term_shift f s)
  simpa only [hs', cuspCompletedLFunction] using he

end
end Dubon2026
