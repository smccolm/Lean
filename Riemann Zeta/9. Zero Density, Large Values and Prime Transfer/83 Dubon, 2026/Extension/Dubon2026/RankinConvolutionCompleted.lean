import Dubon2026.RankinConvolution
import Dubon2026.Gamma0CuspEntire

/-! # The actual completed convolution series and its full-level functional equation -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The completed cusp integral is the actual nonnegative convolution series times both exact Gamma factors. -/
theorem gamma0CompletedCusp_eq_convolution {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    gamma0CompletedCusp f s =
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * cuspRankinFactor k s) *
        LSeries (rankinConvolutionCoefficients f) s := by
  rw [gamma0CompletedCusp_eq_rankin f hk hs, rankinConvolution_LSeries f hk hs,
    gamma0CompletionFactor]
  ring

/-- The genuine finite entire completion agrees with s(s−1) times the actual completed convolution series on Re(s)>1. -/
theorem gamma0CuspEntire_eq_convolution {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    gamma0CuspEntire f s = s * (s - 1) *
      (((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * cuspRankinFactor k s) *
        LSeries (rankinConvolutionCoefficients f) s) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re] at hs; linarith
  rw [gamma0CuspEntire_eq f hs0 hs1, gamma0CompletedCusp_eq_convolution f hk hs]

/-- At full level the actual completed convolution continuation has the scalar reflection equation s↦1−s. -/
theorem gamma0CompletedCusp_levelOne_functional_equation {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (s : ℂ) :
    gamma0CompletedCusp f (1 - s) = gamma0CompletedCusp f s := by
  rw [gamma0CompletedCusp_reflected_sum, gamma0CompletedCusp_eq_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : d.val = 1 := Nat.dvd_one.mp (Nat.dvd_of_mem_divisors d.property)
  simp only [Nat.cast_one, hd1, mul_one, Complex.one_cpow]

end
end Dubon2026
