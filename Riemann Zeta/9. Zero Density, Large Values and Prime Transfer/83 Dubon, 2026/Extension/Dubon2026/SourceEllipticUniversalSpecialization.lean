import Dubon2026.SourceEllipticUniversalCurve

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
/-- The integral cuspidal Weierstrass equation used for specialization. -/
def cusp : WeierstrassCurve.Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

theorem cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.polynomial, cusp, Polynomial.evalEval]

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Coefficient evaluation at the specified Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

theorem map_specialize : WeierstrassCurve.map curve (specialize W) = W := by
  simp [specialize, curve, map]


variable (x y : R)

open Polynomial (eval₂RingHom) in

/-- Evaluation of a universal bivariate polynomial at the specified coordinates. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom (specialize W) x) y

open Polynomial in
theorem polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom (specialize W)).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : WeierstrassCurve.Affine.Equation W x y)

open Polynomial in

/-- The coordinate-ring homomorphism induced by a point on the curve. -/
def ringEval : Coord →+* R :=
  AdjoinRoot.lift (eval₂RingHom (specialize W) x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]

    rw [← WeierstrassCurve.Affine.map_polynomial]
    simpa only [WeierstrassCurve.Affine.map, map_specialize, WeierstrassCurve.Affine.Equation, evalEval, coe_evalRingHom] using eqn

theorem ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

theorem ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

theorem polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = (specialize W) := by
  ext <;> simp [polyEval]

theorem ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = (specialize W) := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

theorem functionField_two_ne_zero : (2 : FunctionField) ≠ 0 := by
  rw [← map_ofNat (algebraMap Coord _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

theorem curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    ringEval_comp_eq_specialize, map_specialize]



end
end Dubon2026.SourceEllipticUniversal
