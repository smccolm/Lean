import Dubon2026.SourceEllipticGenericXCoordinates

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction ->
reverse genus -> finite exceptional fibers -> actual elliptic torsion count
-> division-polynomial point multiplication. The actual universal point is
multiplied using the native elliptic-curve group law. The identities will
descend to the integral coordinate ring and specialize to every nonsingular
point. Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticUniversal.AffineFormula
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open WeierstrassCurve (ψ φ)
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate nonZeroDivisors
noncomputable section
variable {m n : ℤ}

private theorem polynomial_two_ne_zero : (2 : Poly) ≠ 0 := by norm_num

private theorem smulY_sub_negY_aux {F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

theorem smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [WeierstrassCurve.Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ωe_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

theorem smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

theorem smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

/-- The doubling slope of the actual generic affine point. -/
def slopeOne : FunctionField :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

theorem slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, WeierstrassCurve.Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, WeierstrassCurve.Affine.polynomialX]
  congr
  simp [algebraMap_field_eq_comp, Polynomial.algebraMap_apply, map_ofNat]

private theorem addX_smul_one_smul_one_aux {F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by

  field_simp; ring

theorem addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, WeierstrassCurve.Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq, ← neg_div _ (polyToField _),
    slopeOne_eq_neg_div, addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private theorem addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open Dubon2026.SourceEllipticSequence in
theorem addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ωe, redInvarDenom_two, one_mul, complEDS₂Aux_two, sub_zero, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, addX_smul_one_smul_one, smulX_two, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private theorem smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

open Polynomial (CC) in

theorem ωe_neg' : (ωe curve) (-n) =
    (ωe curve) n + CC curve.a₁ * curve.φ n * curve.ψ n + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero polynomial_two_ne_zero)]
  simp_rw [left_distrib, two_mul_ωe, ψc_neg, ψ_neg, φ_neg]; ring

theorem smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [WeierstrassCurve.Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψ_neg, ωe_neg',
    map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)


end
end Dubon2026.SourceEllipticUniversal.AffineFormula
