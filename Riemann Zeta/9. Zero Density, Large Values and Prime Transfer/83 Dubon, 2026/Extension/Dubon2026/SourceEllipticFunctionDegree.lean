/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEllipticFunctionGeneric
import Mathlib.RingTheory.Algebraic.Integral

/-! The actual elliptic function field is quadratic over its rational coordinate.
Adapted from TauCeti bfcff79b60964ba7bdb78b952828313686c327ba,
Affine/FunctionField/Finrank.lean, Apache-2.0, retaining its AINTLIB provenance.
The pinned Mathlib fraction-ring rank theorem replaces the newer API. This is
the degree input for the odd quotient field embedding on the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- The affine coordinate ring has rank two over the polynomial coordinate. -/
theorem finrank_coordinateRing : Module.finrank F[X] W.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W)).trans (Fintype.card_fin 2)

/-- The polynomial coordinate acts faithfully on the function field. -/
theorem faithfulSMul_polynomial : FaithfulSMul F[X] W.FunctionField :=
  (faithfulSMul_iff_algebraMap_injective F[X] W.FunctionField).mpr
    (polynomial_algebraMap_injective W)

/-- The canonical rational-coordinate action, obtained by extending the polynomial action. -/
noncomputable abbrev rationalFunctionAlgebra : Algebra (FractionRing F[X]) W.FunctionField := by
  letI := faithfulSMul_polynomial W
  exact FractionRing.liftAlgebra F[X] W.FunctionField

/-- The rational-coordinate action extends the actual polynomial-coordinate action. -/
theorem rationalFunction_scalarTower :
    letI := rationalFunctionAlgebra W
    IsScalarTower F[X] (FractionRing F[X]) W.FunctionField := by
  letI := faithfulSMul_polynomial W
  exact FractionRing.isScalarTower_liftAlgebra F[X] W.FunctionField

/-- The actual function field has degree two over any compatible fraction field of `F[X]`. -/
theorem finrank_functionField (L : Type*) [Field L] [Algebra F[X] L]
    [IsFractionRing F[X] L] [Algebra L W.FunctionField]
    [IsScalarTower F[X] L W.FunctionField] : Module.finrank L W.FunctionField = 2 := by
  letI : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)
  letI : FaithfulSMul F[X] W.CoordinateRing :=
    (faithfulSMul_iff_algebraMap_injective F[X] W.CoordinateRing).mpr
      (AdjoinRoot.of.injective_of_degree_ne_zero (by simp [Affine.degree_polynomial]))
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing F[X] L W.CoordinateRing W.FunctionField,
    finrank_coordinateRing]

/-- The quadratic degree supplies finite dimensionality without an extra hypothesis. -/
theorem finiteDimensional_functionField (L : Type*) [Field L] [Algebra F[X] L]
    [IsFractionRing F[X] L] [Algebra L W.FunctionField]
    [IsScalarTower F[X] L W.FunctionField] : FiniteDimensional L W.FunctionField :=
  .of_finrank_pos (by rw [finrank_functionField]; norm_num)

end Dubon2026.SourceEllipticFunctionField
