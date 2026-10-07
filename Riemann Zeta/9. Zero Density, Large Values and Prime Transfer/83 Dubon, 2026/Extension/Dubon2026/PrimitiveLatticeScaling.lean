import Dubon2026.LatticeEpsteinMellin
import Dubon2026.Gamma0Eisenstein
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Actual dilation and gcd decomposition of Eisenstein lattice rows -/

namespace Dubon2026

open UpperHalfPlane EisensteinSeries

noncomputable section

/-- Dilating the actual integer row divides its genuine height by the square of the dilation. -/
theorem eisensteinRowHeight_nsmul (n : ℕ) (v : Fin 2 → ℤ) (z : ℍ) :
    eisensteinRowHeight (n • v) z = ((n : ℝ) ^ 2)⁻¹ * eisensteinRowHeight v z := by
  have he : (((n • v) 0 : ℤ) : ℂ) * z + (n • v) 1 =
      (n : ℂ) * ((v 0 : ℂ) * z + v 1) := by
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    ring
  simp only [eisensteinRowHeight, he, norm_mul, Complex.norm_natCast, mul_pow,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact complex Eisenstein factor of a natural dilation is n^(-2s). -/
theorem nonholomorphicEisensteinTerm_nsmul (n : ℕ) (s : ℂ) (v : Fin 2 → ℤ) (z : ℍ) :
    nonholomorphicEisensteinTerm s (n • v) z =
      (n : ℂ) ^ (-(2 * s)) * nonholomorphicEisensteinTerm s v z := by
  rw [nonholomorphicEisensteinTerm, eisensteinRowHeight_nsmul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (eisensteinRowHeight_nonneg v z), Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.inv_cpow _ _ (by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow,
        Complex.arg_ofReal_of_nonneg (sq_nonneg _)]
      exact Real.pi_ne_zero.symm),
    ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_neg]
  rfl

/-- Every actual gcd fiber has its exact homogeneous Eisenstein factor. -/
theorem nonholomorphicEisensteinTerm_gcd (s : ℂ) (z : ℍ) {n : ℕ}
    (v : gammaSet 1 n 0) :
    nonholomorphicEisensteinTerm s v.val z =
      (n : ℂ) ^ (-(2 * s)) * nonholomorphicEisensteinTerm s (divIntMap n v.val) z := by
  conv_lhs => rw [gammaSet_eq_gcd_mul_divIntMap v.property]
  exact nonholomorphicEisensteinTerm_nsmul n s _ z

/-- The true primitive full-level rows agree with pinned Mathlib's gcd-one lattice fiber. -/
theorem gamma0PrimitiveRows_one_eq : gamma0PrimitiveRows 1 = gammaSet 1 1 0 := by
  ext v
  simp [gamma0PrimitiveRows, gammaSet_one_eq]

end
end Dubon2026
