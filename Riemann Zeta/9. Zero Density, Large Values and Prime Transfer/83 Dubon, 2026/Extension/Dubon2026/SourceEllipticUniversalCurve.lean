import Dubon2026.SourceEllipticDivisionCoordinateMap
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction ->
reverse genus -> finite exceptional fibers -> elliptic inertia orbits ->
actual torsion cardinality -> division-polynomial point multiplication.
The universal curve and its generic point allow an integral polynomial
identity to specialize to every actual point, including characteristics
two and three. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticUniversal
open WeierstrassCurve
open scoped Polynomial Polynomial.Bivariate
noncomputable section
/-- The five coefficients of the universal Weierstrass equation. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

theorem coordinate_algebraMap_injective {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R) :
    Function.Injective (algebraMap R W.CoordinateRing) := by
  have h : Function.Injective (algebraMap (Polynomial R) W.CoordinateRing) :=
    (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W) (q := 0) <| by
        rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, Polynomial.C_0, map_zero, zero_mul, add_zero]
        exact hp
  exact h.comp Polynomial.C_injective


open Coeff

open MvPolynomial (X) in

/-- The Weierstrass curve with five independent integral coefficients. -/
def curve : WeierstrassCurve.Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

theorem Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- The bivariate polynomial ring over the universal coefficients. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

/-- The native commutative-ring structure cached at the universal polynomial alias. -/
instance polyCommRing : CommRing Poly := Polynomial.commRing

/-- The actual coordinate ring of the universal Weierstrass curve. -/
abbrev Coord : Type := curve.CoordinateRing

/-- The fraction field of the actual universal coordinate ring. -/
abbrev FunctionField : Type := FractionRing Coord

/-- The natural quotient map from bivariate polynomials to the function field. -/
def polyToField : Poly →+* FunctionField := (algebraMap Coord _).comp <| AdjoinRoot.mk _

theorem polyToField_apply (p : Poly) :
    polyToField p = algebraMap Coord _ (AdjoinRoot.mk _ p) := rfl

theorem algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) FunctionField = polyToField.comp (algebraMap _ _) := rfl

theorem algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Coord = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] theorem polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

theorem algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) FunctionField) :=
  (IsFractionRing.injective Coord FunctionField).comp
    (coordinate_algebraMap_injective _)

/-- The universal curve after base change to its function field. -/
abbrev pointedCurve : WeierstrassCurve FunctionField :=
  baseChange curve FunctionField

/-- The nonzero universal discriminant makes the generic curve elliptic. -/
instance pointedCurveElliptic : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by

    simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial in
theorem equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  simpa [WeierstrassCurve.Affine.Equation, pointedCurve, baseChange,
    WeierstrassCurve.Affine.polynomial, algebraMap_field_eq_comp,
    WeierstrassCurve.map, Polynomial.evalEval, Polynomial.algebraMap_apply,
    map_sub, map_add, map_mul, map_pow]
    using polyToField_polynomial

open Polynomial in

/-- The nonsingular generic affine point of the actual universal curve. -/
def affinePoint : WeierstrassCurve.Affine.Point pointedCurve.toAffine :=
  .some (polyToField (C X)) (polyToField Y)
    ((pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (by simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
        using Δ_curve_ne_zero)).mp equation_point)

/-- The actual generic point in Jacobian coordinates. -/
def jacobianPoint : WeierstrassCurve.Jacobian.Point (WeierstrassCurve.baseChange curve FunctionField) :=
  WeierstrassCurve.Jacobian.Point.fromAffine affinePoint

open Polynomial (CC)

theorem pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
theorem pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
theorem pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
theorem pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
theorem pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

/-- The universal curve over its bivariate polynomial ring. -/
abbrev curvePoly : WeierstrassCurve Poly := WeierstrassCurve.baseChange curve Poly

/-- The universal curve over its coordinate ring. -/
abbrev curveRing : WeierstrassCurve Coord :=
  WeierstrassCurve.baseChange curve Coord

/-- The universal curve over its function field. -/
abbrev curveField : WeierstrassCurve FunctionField :=
  WeierstrassCurve.baseChange curve FunctionField

theorem curveField_eq : curveField = pointedCurve := rfl


end
end Dubon2026.SourceEllipticUniversal
