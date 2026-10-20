/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Adapted from TauCetiProject/TauCeti commit 469cd8e08a918e133b260bcad0b60b8a1daf591a,
GeneralLinear/Coordinate/HopfAlgebra.lean and GeneralLinear/FunctorOfPoints.lean.
Only determinant localization, actual matrix evaluation and the original generic
matrix are retained, using the unchanged Mathlib pin's localization API.
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Localization.Away.Basic

/-! Actual regular functions on GL_n over the original coefficient ring.
This is the required regular-function carrier of Geraghty's integral Borel
induction on DUB-17's unitary coefficient-module chain. No finite-dimensional
or finite-free conclusion about that induced module is assumed or claimed. -/

namespace Dubon2026
noncomputable section
open Matrix

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The original general-linear regular functions are the determinant localization of the original matrix polynomial ring. -/
abbrev GeneralLinearRegularFunctions :=
  Localization.Away (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))

/-- The actual polynomial coordinate map into the original determinant localization. -/
def generalLinearRegularPolynomialMap :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] GeneralLinearRegularFunctions R n :=
  IsScalarTower.toAlgHom R _ _

variable {R n} {A : Type*} [CommRing A] [Algebra R A]

/-- Matrix evaluation sends the original generic determinant to a unit. -/
theorem generalLinearRegularEval_det_isUnit (g : GeneralLinearGroup (Fin n) A) :
    IsUnit ((MvPolynomial.aeval fun ij : Fin n × Fin n => g.val ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  rw [AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval]
  exact Matrix.isUnits_det_units g

/-- Evaluation of original regular functions at an actual invertible matrix, over any original coefficient algebra. -/
def generalLinearRegularEval (g : GeneralLinearGroup (Fin n) A) :
    GeneralLinearRegularFunctions R n →ₐ[R] A :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))
    (f := MvPolynomial.aeval fun ij : Fin n × Fin n => g.val ij.1 ij.2) (by
      rintro ⟨y, hy⟩
      obtain ⟨m, rfl⟩ := hy
      rw [map_pow]
      exact (generalLinearRegularEval_det_isUnit g).pow m)

/-- Localized matrix evaluation agrees with the exact original polynomial evaluation. -/
theorem generalLinearRegularEval_polynomial (g : GeneralLinearGroup (Fin n) A)
    (p : MvPolynomial (Fin n × Fin n) R) :
    generalLinearRegularEval g (generalLinearRegularPolynomialMap R n p) =
      MvPolynomial.aeval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) p := by
  change IsLocalization.lift _ (algebraMap _ (GeneralLinearRegularFunctions R n) p) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- The original generic coordinate evaluates to the corresponding original matrix entry. -/
theorem generalLinearRegularEval_X (g : GeneralLinearGroup (Fin n) A) (i j : Fin n) :
    generalLinearRegularEval (R := R) g
      (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) = g.val i j := by
  rw [generalLinearRegularEval_polynomial, MvPolynomial.aeval_X]

variable (R n)

/-- The original generic matrix in the regular-function ring is an actual invertible matrix. -/
def generalLinearRegularGeneric : GeneralLinearGroup (Fin n) (GeneralLinearRegularFunctions R n) :=
  GeneralLinearGroup.mk'' ((Matrix.mvPolynomialX (Fin n) (Fin n) R).map
    (generalLinearRegularPolynomialMap R n)) (by
      rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The actual generic invertible matrix retains its exact original coordinate entries. -/
theorem generalLinearRegularGeneric_apply (i j : Fin n) :
    (generalLinearRegularGeneric R n).val i j =
      generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j)) := rfl

/-- Evaluating the original generic invertible matrix at an actual matrix recovers that same matrix. -/
theorem generalLinearRegularGeneric_eval (g : GeneralLinearGroup (Fin n) A) :
    GeneralLinearGroup.map (generalLinearRegularEval (R := R) g).toRingHom
      (generalLinearRegularGeneric R n) = g := by
  apply Units.ext
  ext i j
  exact generalLinearRegularEval_X g i j

end
end Dubon2026
