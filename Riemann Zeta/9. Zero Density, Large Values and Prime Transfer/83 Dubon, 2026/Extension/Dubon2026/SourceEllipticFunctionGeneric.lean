/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEllipticFunctionEvaluation

/-! Actual function-field coordinates for the odd quotient pullback (DUB-17/18).
Adapted from TauCeti bfcff79b60964ba7bdb78b952828313686c327ba,
Affine/FunctionField/GenericPoint/Basic.lean, Apache-2.0, with its documented
AINTLIB provenance. No specialization principle or quotient equation is assumed. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The generic `x`-coordinate: the class of `X` in the function field. -/
noncomputable def genericX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))

/-- The generic `y`-coordinate: the class of `Y` in the function field. -/
noncomputable def genericY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

/-- The generic coordinate `x` is the image of the coordinate-ring class of `X` in the function
field. -/
theorem genericX_def :
    genericX W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := (rfl)

/-- The generic coordinate `y` is the image of the coordinate-ring class of `Y` in the function
field. -/
theorem genericY_def :
    genericY W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := (rfl)

/-- The generic coordinate `x` is the image of polynomial `X` under the induced map from `F[X]`
to the function field. -/
theorem genericX_eq_algebraMap : genericX W = algebraMap F[X] W.FunctionField X := by
  rw [genericX_def, AdjoinRoot.mk_C,
    IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
  rfl

/-- **Evaluating at the generic point is reduction modulo the Weierstrass relation.** A bivariate
polynomial over `R`, pushed to the function field and evaluated at `(genericX, genericY)`, is the
image of its class in the coordinate ring.

This is the workhorse: it converts any polynomial expression at the generic point into the image
of a coordinate-ring element, where the ring's own API applies. -/
theorem evalEval_genericX_genericY (p : F[X][Y]) :
    (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genericX W) (genericY W) =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p) :=
  (algHom_mk_eq_evalEval
    (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField) p).symm

/-- **The generic coordinate functions satisfy the equation of the curve.** `(X, Y)` satisfies
the equation of `W` base-changed to the function field, because the Weierstrass polynomial is
precisely what the coordinate ring quotients out. -/
theorem equation_genericX_genericY :
    (W⁄W.FunctionField).toAffine.Equation (genericX W) (genericY W) :=
  equation_of_algHom
    (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)

/-- The generic `y`-coordinate is a root of the Weierstrass polynomial.

This is AINTLIB's `root_aeval_polynomial_map` of `projects/HasseWeil/HasseWeil/Ramification.lean`
at revision `513e83879e2f`, Apache-2.0, stated over `F[X]` rather than over a fraction field. -/
@[simp]
theorem aeval_genericY_polynomial : aeval (genericY W) W.polynomial = 0 := by
  rw [genericY_def, AdjoinRoot.mk_X]
  exact AdjoinRoot.aeval_algHom_eq_zero W.polynomial
    (IsScalarTower.toAlgHom F[X] W.CoordinateRing W.FunctionField)

/-- The generic `y`-coordinate is integral over any commutative `F[X]`-algebra `L` mapping
compatibly to the function field. `L` need not embed: no injectivity is assumed. -/
theorem isIntegral_genericY (L : Type*) [CommRing L] [Algebra F[X] L]
    [Algebra L W.FunctionField] [IsScalarTower F[X] L W.FunctionField] :
    IsIntegral L (genericY W) :=
  ⟨_, W.monic_polynomial.map _, by
    rw [← aeval_def, Polynomial.aeval_map_algebraMap]
    exact aeval_genericY_polynomial W⟩

/-- **The image of `F[X]` in the function field consists of the polynomials in the generic
`x`-coordinate.** -/
theorem algebraMap_eq_aeval_genericX (p : F[X]) :
    algebraMap F[X] W.FunctionField p = aeval (genericX W) p := by
  have h : IsScalarTower.toAlgHom F F[X] W.FunctionField = aeval (genericX W) := by
    apply Polynomial.algHom_ext
    rw [aeval_X, IsScalarTower.coe_toAlgHom', ← genericX_eq_algebraMap]
  exact congr($h p)

/-- The polynomial coordinate embeds in the actual function field. -/
theorem polynomial_algebraMap_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField]
  exact (IsFractionRing.injective W.CoordinateRing W.FunctionField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero (by simp [Affine.degree_polynomial]))

/-- **The coordinate function `x` is transcendental over the base field.** -/
theorem transcendental_genericX : Transcendental F (genericX W) := by
  rw [genericX_eq_algebraMap]
  exact (transcendental_algebraMap_iff
    (polynomial_algebraMap_injective W)).2 (Polynomial.transcendental_X F)


variable [W.IsElliptic]

/-- The generic coordinates are nonsingular, so they define an affine point of the base-changed
curve.

Ellipticity turns the equation into nonsingularity after scalar extension. -/
theorem nonsingular_genericX_genericY :
    (W⁄W.FunctionField).toAffine.Nonsingular (genericX W) (genericY W) := by
  haveI : (W⁄W.FunctionField).toAffine.IsElliptic := by
    change (WeierstrassCurve.map W (algebraMap F W.FunctionField)).IsElliptic
    infer_instance
  exact equation_iff_nonsingular.mp (equation_genericX_genericY W)

/-- **The generic point of `W`**: the tautological point of `W` with coordinates in its own
function field. -/
noncomputable def genericPoint : (W⁄W.FunctionField).toAffine.Point :=
  .some _ _ (nonsingular_genericX_genericY W)

/-- The generic point is the affine point whose coordinates are `genericX W` and `genericY W`. -/
theorem genericPoint_eq_some : genericPoint W =
    .some (genericX W) (genericY W) (nonsingular_genericX_genericY W) := (rfl)


end Dubon2026.SourceEllipticFunctionField
