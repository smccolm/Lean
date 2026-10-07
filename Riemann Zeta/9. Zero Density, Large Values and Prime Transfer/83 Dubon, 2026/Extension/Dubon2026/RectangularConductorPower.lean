import Dubon2026.RectangularDualSeries
import Dubon2026.RankinConvolutionReflection

/-! # Exact positive conductor powers for the genuine rectangular dual series -/

namespace Dubon2026

noncomputable section

/-- Principal complex powers preserve quotients of strictly positive real bases. -/
theorem positive_real_div_cpow {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (s : ℂ) :
    ((u / v : ℝ) : ℂ) ^ s = (u : ℂ) ^ s / (v : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.mpr hv.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hv.le]; exact Real.pi_ne_zero.symm),
    div_eq_mul_inv]

/-- Squaring a positive real base doubles its actual complex exponent. -/
theorem positive_real_square_cpow {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ((u ^ 2 : ℝ) : ℂ) ^ s = (u : ℂ) ^ (2 * s) := by
  rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le hu.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
  congr 1
  ring

/-- All actual level powers combine into the precise positive degree-four conductor. -/
theorem rectangular_conductor_power {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (k : ℤ) (s : ℂ) :
    (u : ℂ) ^ (2 * s - 1) * (v : ℂ) ^ ((k : ℂ) - 2 * s) * (w : ℂ) ^ (-s) =
      ((v : ℂ) ^ k / (u : ℂ)) * ((u ^ 2 / (v ^ 2 * w) : ℝ) : ℂ) ^ s := by
  have hu0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hv0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [positive_real_div_cpow (sq_pos_of_pos hu) (mul_pos (sq_pos_of_pos hv) hw),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (sq_nonneg v) hw.le,
    positive_real_square_cpow hu, positive_real_square_cpow hv,
    Complex.cpow_sub _ _ hu0, Complex.cpow_sub _ _ hv0, Complex.cpow_one,
    Complex.cpow_intCast, Complex.cpow_neg]
  ring

/-- The exact arbitrary-period completion differs from period one by its genuine width power. -/
theorem cuspTraceRankinFactor_eq_width {N : ℕ} [NeZero N] (k : ℤ) (s : ℂ) :
    cuspTraceRankinFactor N k s = (N : ℂ) ^ (s + (k : ℂ) - 1) *
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * cuspRankinFactor k s) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  rw [cuspTraceRankinFactor, positive_real_div_cpow (by positivity) hN,
    cuspRankinFactor]
  simp_rw [Complex.cpow_neg]
  push_cast
  rw [div_inv_eq_mul]
  ring

/-- The exact level factor in the reflected completion reduces to its positive conductor and signed constant amplitude. -/
theorem rectangular_completion_power_reflection {Q d : ℝ} (hQ : 0 < Q) (hd : 0 < d)
    (k : ℤ) (s : ℂ) :
    ((Q * d : ℝ) : ℂ) ^ (-s) * (Q : ℂ) ^ ((k : ℂ) - s) *
      (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) =
      ((Q : ℂ) ^ k / (4 * Real.pi ^ 2 : ℂ)) *
        (((4 * Real.pi ^ 2) ^ 2 / (Q ^ 2 * d) : ℝ) : ℂ) ^ s := by
  have hQ0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hQ.le hd.le]
  have hp : (Q : ℂ) ^ (-s) * (Q : ℂ) ^ ((k : ℂ) - s) =
      (Q : ℂ) ^ ((k : ℂ) - 2 * s) := by
    rw [← Complex.cpow_add _ _ hQ0]
    congr 1
    ring
  calc
    _ = (4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) *
        ((Q : ℂ) ^ (-s) * (Q : ℂ) ^ ((k : ℂ) - s)) * (d : ℂ) ^ (-s) := by ring
    _ = _ := by
      rw [hp]
      have he := rectangular_conductor_power (u := 4 * Real.pi ^ 2) (by positivity) hQ hd k s
      push_cast at he ⊢
      exact he

end
end Dubon2026
