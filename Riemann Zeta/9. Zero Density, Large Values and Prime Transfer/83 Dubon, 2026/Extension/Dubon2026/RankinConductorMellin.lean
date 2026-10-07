import Dubon2026.RankinPerronContinuation

/-! # Exact positive conductor and Mellin power identities for the genuine Rankin transform -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual conductor, cutoff and positive coefficient powers combine with their precise reciprocal factors. -/
theorem rankin_conductor_mellin_power {a x n : ℝ} (ha : 0 < a) (hx : 0 < x) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ (s + 2) * (a : ℂ) ^ (2 * s - 1) * (n : ℂ) ^ (s - 1) =
      ((x : ℂ) ^ 2 / ((a : ℂ) * n)) * ((a ^ 2 * n * x : ℝ) : ℂ) ^ s := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have ha2 : (((a ^ 2 : ℝ) : ℂ) ^ s) = (a : ℂ) ^ (2 * s) := by
    rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le ha.le,
      ← Complex.cpow_add _ _ ha0]
    congr 1
    ring
  have hp : ((a ^ 2 * n * x : ℝ) : ℂ) ^ s =
      (a : ℂ) ^ (2 * s) * (n : ℂ) ^ s * (x : ℂ) ^ s := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_nonneg (sq_nonneg a) hn.le) hx.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (sq_nonneg a) hn.le, ha2]
  rw [hp, Complex.cpow_add _ _ hx0, Complex.cpow_sub _ _ ha0,
    Complex.cpow_sub _ _ hn0, Complex.cpow_one, Complex.cpow_one]
  norm_num only [Complex.cpow_ofNat]
  ring

/-- The exact reflected L-series term retains its genuine positive-index reciprocal coefficient. -/
theorem rankinConvolution_reflected_term {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) (n : ℕ) :
    LSeries.term (rankinConvolutionCoefficients f) (1 - s) n =
      rankinConvolutionCoefficients f n * (n : ℂ) ^ (s - 1) := by
  rw [LSeries.term_def₀ (rankinConvolutionCoefficients_zero f)]
  congr 1
  congr 1
  ring

/-- The genuine reflected full-level Perron function has its exact conductor and original convergent series. -/
theorem rankinPerronContinuation_reflected {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 0 ≤ k) (x : ℝ) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    rankinPerronContinuation f x s =
      ((x : ℂ) ^ (s + 2) * (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * gammaRieszSymbol (k : ℝ) 2 s) *
        LSeries (rankinConvolutionCoefficients f) (1 - s) := by
  rw [rankinPerronContinuation, mul_div_assoc, rankinConvolution_riesz_reflection f hk hl hr]
  ring

end
end Dubon2026
