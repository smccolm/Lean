/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEllipticFunctionInjective
import Dubon2026.SourceEllipticFunctionGeneric

/-! Extending actual elliptic coordinate evaluation to the fraction field.
Adapted from TauCeti bfcff79b60964ba7bdb78b952828313686c327ba,
Affine/FunctionField/Lift.lean, Apache-2.0. The equation and transcendence inputs
remain explicit until proved for the odd quotient coordinates (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Dubon2026.SourceEllipticFunctionField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {W : Affine K} {x y : L}

/-- Function-field algebra homomorphisms are determined by the two generic coordinates. -/
theorem functionFieldAlgHom_ext {f g : W.FunctionField →ₐ[K] L}
    (hx : f (genericX W) = g (genericX W))
    (hy : f (genericY W) = g (genericY W)) : f = g := by
  have h : f.comp (IsScalarTower.toAlgHom K W.CoordinateRing W.FunctionField) =
      g.comp (IsScalarTower.toAlgHom K W.CoordinateRing W.FunctionField) :=
    algHom_ext hx hy
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := W.CoordinateRing)
  intro z
  exact AlgHom.congr_fun h z

/-- The evaluation of the coordinate ring at a solution `(x, y)` of the Weierstrass equation is
injective when `x` is transcendental. -/
private theorem evalAlgHom_injective (h : (W⁄L).toAffine.Equation x y)
    (hx : Transcendental K x) : Function.Injective (evalAlgHom h) :=
  algHom_injective _ <| by
    rwa [CoordinateRing.mk, AdjoinRoot.mk_C, evalAlgHom_of_X]

/-- **The function field of a Weierstrass curve embeds at a solution of its equation**: a
solution `(x, y)` of the Weierstrass equation of `W` in a field `L` over `K`, with `x`
transcendental over `K`, defines the `K`-embedding `K(W) → L` sending the generic point to
`(x, y)`. -/
noncomputable def functionFieldLift (h : (W⁄L).toAffine.Equation x y)
    (hx : Transcendental K x) : W.FunctionField →ₐ[K] L :=
  IsFractionRing.liftAlgHom (evalAlgHom_injective h hx)

/-- On the coordinate ring, `functionFieldLift` is evaluation at the solution. -/
@[simp]
theorem functionFieldLift_algebraMap (h : (W⁄L).toAffine.Equation x y)
    (hx : Transcendental K x) (z : W.CoordinateRing) :
    functionFieldLift h hx (algebraMap W.CoordinateRing W.FunctionField z) =
      evalAlgHom h z := by
  simp [functionFieldLift, IsFractionRing.liftAlgHom_apply]

/-- `functionFieldLift` sends the generic `x`-coordinate to `x`. -/
@[simp]
theorem functionFieldLift_genericX (h : (W⁄L).toAffine.Equation x y)
    (hx : Transcendental K x) : functionFieldLift h hx (genericX W) = x := by
  rw [genericX_def, functionFieldLift_algebraMap, CoordinateRing.mk, AdjoinRoot.mk_C,
    evalAlgHom_of_X]

/-- `functionFieldLift` sends the generic `y`-coordinate to `y`. -/
@[simp]
theorem functionFieldLift_genericY (h : (W⁄L).toAffine.Equation x y)
    (hx : Transcendental K x) : functionFieldLift h hx (genericY W) = y := by
  rw [genericY_def, functionFieldLift_algebraMap, CoordinateRing.mk, AdjoinRoot.mk_X,
    evalAlgHom_root]

/-- **Uniqueness of `functionFieldLift`**: a `K`-embedding of `K(W)` into `L` is determined by the
images of the generic coordinates. -/
theorem eq_functionFieldLift (h : (W⁄L).toAffine.Equation x y) (hx : Transcendental K x)
    (f : W.FunctionField →ₐ[K] L) (hfx : f (genericX W) = x) (hfy : f (genericY W) = y) :
    f = functionFieldLift h hx :=
  functionFieldAlgHom_ext (by simp [hfx]) (by simp [hfy])

end Dubon2026.SourceEllipticFunctionField
