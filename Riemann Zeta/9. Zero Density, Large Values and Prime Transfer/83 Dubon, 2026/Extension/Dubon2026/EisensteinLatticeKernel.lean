import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # The genuine nonholomorphic Eisenstein lattice kernel -/

namespace Dubon2026

open UpperHalfPlane Matrix Complex
open scoped MatrixGroups

noncomputable section

/-- The actual height associated with the integer row (c,d), namely y/|cz+d|². -/
def eisensteinRowHeight (v : Fin 2 → ℤ) (z : ℍ) : ℝ :=
  z.im / ‖(v 0 : ℂ) * z + v 1‖ ^ 2

/-- The actual complex power used in the nonholomorphic Eisenstein series. -/
def nonholomorphicEisensteinTerm (s : ℂ) (v : Fin 2 → ℤ) (z : ℍ) : ℂ :=
  (eisensteinRowHeight v z : ℂ) ^ s

/-- The genuine row height is nonnegative, including the totalized zero row. -/
theorem eisensteinRowHeight_nonneg (v : Fin 2 → ℤ) (z : ℍ) :
    0 ≤ eisensteinRowHeight v z := div_nonneg z.im_pos.le (sq_nonneg _)

/-- A nonzero integer row has a nonzero actual linear denominator in the upper half-plane. -/
theorem eisenstein_row_denominator_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    (v 0 : ℂ) * z + v 1 ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (EisensteinSeries.r_pos z) (norm_pos_iff.mpr hv))
    (EisensteinSeries.r_mul_max_le z hv)

/-- The row height is positive for every nonzero lattice row. -/
theorem eisensteinRowHeight_pos {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    0 < eisensteinRowHeight v z :=
  div_pos z.im_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisenstein_row_denominator_ne_zero hv z)))

/-- The exact absolute value of the nonholomorphic summand retains its full complex parameter. -/
theorem norm_nonholomorphicEisensteinTerm (s : ℂ) (hs : s.re ≠ 0)
    (v : Fin 2 → ℤ) (z : ℍ) :
    ‖nonholomorphicEisensteinTerm s v z‖ =
      z.im ^ s.re * ‖(v 0 : ℂ) * z + v 1‖ ^ (-(2 * s.re)) := by
  rw [nonholomorphicEisensteinTerm,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (eisensteinRowHeight_nonneg v z) hs,
    eisensteinRowHeight, Real.div_rpow z.im_pos.le (sq_nonneg _),
    ← Real.rpow_natCast_mul (norm_nonneg _) 2,
    Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
  norm_num

/-- Pinned Mathlib's genuine lattice lower bound supplies an absolutely summable majorant. -/
theorem norm_nonholomorphicEisensteinTerm_le {s : ℂ} (hs : 1 < s.re)
    (v : Fin 2 → ℤ) (z : ℍ) :
    ‖nonholomorphicEisensteinTerm s v z‖ ≤
      (z.im ^ s.re * (EisensteinSeries.r z) ^ (-(2 * s.re))) * ‖v‖ ^ (-(2 * s.re)) := by
  rw [norm_nonholomorphicEisensteinTerm s (by linarith)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (EisensteinSeries.summand_bound z (by linarith : 0 ≤ 2 * s.re) v)
    (Real.rpow_nonneg z.im_pos.le _)

/-- The literal full lattice series is absolutely convergent for Re(s)>1. -/
theorem summable_norm_nonholomorphicEisensteinTerm {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable (fun v : Fin 2 → ℤ => ‖nonholomorphicEisensteinTerm s v z‖) := by
  apply ((EisensteinSeries.summable_one_div_norm_rpow (by linarith : 2 < 2 * s.re)).mul_left
    (z.im ^ s.re * (EisensteinSeries.r z) ^ (-(2 * s.re)))).of_nonneg_of_le
      (fun v => norm_nonneg _) (fun v => norm_nonholomorphicEisensteinTerm_le hs v z)

/-- Absolute convergence also holds on every actual subset of lattice rows. -/
theorem summable_nonholomorphicEisensteinTerm_subtype {s : ℂ} (hs : 1 < s.re)
    (S : Set (Fin 2 → ℤ)) (z : ℍ) :
    Summable (fun v : S => nonholomorphicEisensteinTerm s v.val z) :=
  ((summable_norm_nonholomorphicEisensteinTerm hs z).subtype S).of_norm

/-- Actual fractional-linear action on z equals right multiplication of the integer row. -/
theorem eisensteinRowHeight_SL2 (v : Fin 2 → ℤ) (A : SL(2, ℤ)) (z : ℍ) :
    eisensteinRowHeight v (A • z) = eisensteinRowHeight (v ᵥ* A.val) z := by
  have hlin := EisensteinSeries.eisSummand_SL2_apply (-1) v A z
  simp only [EisensteinSeries.eisSummand, neg_neg, zpow_one, zpow_neg_one] at hlin
  have hd : ‖UpperHalfPlane.denom A z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero A z)
  rw [eisensteinRowHeight, eisensteinRowHeight, hlin,
    ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  simp only [norm_mul, norm_inv, mul_pow, inv_pow, div_div,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hd), one_mul]

/-- The genuine nonholomorphic kernel has exact SL₂ covariance, without a holomorphic slash factor. -/
theorem nonholomorphicEisensteinTerm_SL2 (s : ℂ) (v : Fin 2 → ℤ) (A : SL(2, ℤ)) (z : ℍ) :
    nonholomorphicEisensteinTerm s v (A • z) =
      nonholomorphicEisensteinTerm s (v ᵥ* A.val) z := by
  rw [nonholomorphicEisensteinTerm, nonholomorphicEisensteinTerm, eisensteinRowHeight_SL2]

end
end Dubon2026
