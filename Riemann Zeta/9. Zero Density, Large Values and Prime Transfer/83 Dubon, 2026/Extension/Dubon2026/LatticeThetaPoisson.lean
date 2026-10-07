import Dubon2026.LatticeThetaFourier

/-! # Poisson summation for the actual determinant-one lattice -/

namespace Dubon2026

open UpperHalfPlane Complex

noncomputable section

/-- The principal complex square-root factor agrees exactly with the positive real factor. -/
theorem gaussianPoissonFactor_real {a : ℝ} (ha : 0 < a) :
    1 / (a : ℂ) ^ (1 / 2 : ℂ) = ((1 / Real.sqrt a : ℝ) : ℂ) := by
  have he : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Real.rpow_one] using (Complex.ofReal_cpow ha.le (1 / 2 : ℝ)).symm.trans
        (congrArg Complex.ofReal (Real.rpow_div_two_eq_sqrt 1 ha.le))
  rw [he, Complex.ofReal_div, Complex.ofReal_one]

/-- The actual lattice kernel splits into a vertical Gaussian and a translated horizontal Gaussian. -/
theorem latticeThetaTerm_split (z : ℍ) (t : ℝ) (m n : ℤ) :
    (latticeThetaTerm z t (m, n) : ℂ) =
      Complex.exp (-(Real.pi : ℂ) * (t * z.im) * (m : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (t / z.im) * ((n : ℂ) + m * z.re) ^ 2) := by
  rw [latticeThetaTerm, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold latticeQuadratic
  push_cast
  field_simp
  ring

/-- One genuine Gaussian Poisson summation in the horizontal coordinate gives the exact bilinear phase. -/
theorem latticeTheta_row_poisson (z : ℍ) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    (∑' n : ℤ, (latticeThetaTerm z t (m, n) : ℂ)) =
      ((1 / Real.sqrt (t / z.im) : ℝ) : ℂ) *
        ∑' n : ℤ, latticeFourierTerm (t * z.im) (z.im / t) z.re (m, n) := by
  have hy0 : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have ha : 0 < ((t / z.im : ℝ) : ℂ).re := div_pos ht z.im_pos
  simp_rw [latticeThetaTerm_split]
  rw [tsum_mul_left]
  have hp := tsum_shifted_complex_gaussian ha ((m : ℂ) * z.re)
  push_cast at hp
  rw [hp]
  have hf := gaussianPoissonFactor_real (div_pos ht z.im_pos)
  push_cast at hf
  rw [hf, ← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc, ← tsum_mul_left]
  rw [Complex.ofReal_div, Complex.ofReal_one]
  congr 1
  apply tsum_congr
  intro n
  rw [← Complex.exp_add, latticeFourierTerm]
  congr 1
  push_cast
  field_simp
  ring

/-- Absolute convergence justifies summing the coordinate Poisson identities over the actual lattice. -/
theorem latticeTheta_complex_fourier (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (latticeTheta z t : ℂ) = ((1 / Real.sqrt (t / z.im) : ℝ) : ℂ) *
      ∑' v : ℤ × ℤ, latticeFourierTerm (t * z.im) (z.im / t) z.re v := by
  rw [latticeTheta_eq_iterated z ht, Complex.ofReal_tsum]
  simp_rw [Complex.ofReal_tsum, latticeTheta_row_poisson z ht]
  rw [tsum_mul_left, ← (summable_norm_latticeFourierTerm
    (mul_pos ht z.im_pos) (div_pos z.im_pos ht) z.re).of_norm.tsum_prod]

/-- The positive real Poisson factors have the exact reciprocal-parameter scaling. -/
theorem latticeTheta_factor_reciprocal (z : ℍ) {t : ℝ} (ht : 0 < t) :
    1 / Real.sqrt (t / z.im) = t⁻¹ * (1 / Real.sqrt (t⁻¹ / z.im)) := by
  rw [Real.sqrt_div ht.le, Real.sqrt_div (inv_pos.mpr ht).le, Real.sqrt_inv]
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp
  nlinarith [Real.sq_sqrt ht.le]

/-- The genuine covolume-one lattice theta series satisfies its exact Poisson transformation. -/
theorem latticeTheta_reciprocal (z : ℍ) {t : ℝ} (ht : 0 < t) :
    latticeTheta z t = t⁻¹ * latticeTheta z t⁻¹ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, latticeTheta_complex_fourier z ht,
    latticeTheta_complex_fourier z (inv_pos.mpr ht)]
  have he : t⁻¹ * z.im = z.im / t := by ring
  have he' : z.im / t⁻¹ = t * z.im := by simp [div_eq_mul_inv, mul_comm]
  rw [he, he', latticeFourier_tsum_swap (t * z.im) (z.im / t) z.re,
    ← mul_assoc, ← Complex.ofReal_mul, ← latticeTheta_factor_reciprocal z ht]

end
end Dubon2026
