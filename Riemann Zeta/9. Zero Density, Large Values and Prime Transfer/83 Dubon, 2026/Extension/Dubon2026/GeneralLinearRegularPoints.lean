/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Adapted from GeneralLinear/FunctorOfPoints.lean at TauCeti commit
469cd8e08a918e133b260bcad0b60b8a1daf591a. The needed point identification
and naturality use the raw original coordinate ring and unchanged native APIs.
-/
import Dubon2026.GeneralLinearRegularFunctions

/-! The original regular-function algebra represents actual invertible
matrices over every coefficient algebra. This is the faithful evaluation
boundary for the exact integral induced coefficient module, the later IntegralInducedFiniteFree and source-tensor consumers establish
finite freeness of the literal induced module. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {n : ℕ}

/-- Original regular-function algebra maps are determined by their values on the actual matrix coordinates. -/
theorem generalLinearRegular_algHom_ext
    {f g : GeneralLinearRegularFunctions R n →ₐ[R] A}
    (h : ∀ i j : Fin n,
      f (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
        g (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j)))) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i j

/-- Every actual algebra point is evaluation at its original generic invertible matrix image. -/
theorem generalLinearRegularEval_map_generic (f : GeneralLinearRegularFunctions R n →ₐ[R] A) :
    generalLinearRegularEval (GeneralLinearGroup.map f.toRingHom (generalLinearRegularGeneric R n)) = f := by
  apply generalLinearRegular_algHom_ext
  intro i j
  rw [generalLinearRegularEval_X]
  rfl

/-- Evaluation at the original generic matrix is the identity on original regular functions. -/
theorem generalLinearRegularEval_generic :
    generalLinearRegularEval (generalLinearRegularGeneric R n) =
      AlgHom.id R (GeneralLinearRegularFunctions R n) := by
  apply generalLinearRegular_algHom_ext
  intro i j
  rw [generalLinearRegularEval_X, generalLinearRegularGeneric_apply]
  rfl

/-- The actual regular-function points are exactly the original invertible matrices, with both inverse identities proved. -/
def generalLinearRegularPointsEquiv :
    (GeneralLinearRegularFunctions R n →ₐ[R] A) ≃ GeneralLinearGroup (Fin n) A where
  toFun f := GeneralLinearGroup.map f.toRingHom (generalLinearRegularGeneric R n)
  invFun := generalLinearRegularEval
  left_inv := generalLinearRegularEval_map_generic
  right_inv := generalLinearRegularGeneric_eval R n

/-- Evaluation is natural in the actual coefficient algebra, retaining the original matrix entries. -/
theorem generalLinearRegularEval_natural (f : A →ₐ[R] B) (g : GeneralLinearGroup (Fin n) A) :
    f.comp (generalLinearRegularEval (R := R) g) =
      generalLinearRegularEval (GeneralLinearGroup.map f.toRingHom g) := by
  apply generalLinearRegular_algHom_ext
  intro i j
  simp only [AlgHom.comp_apply, generalLinearRegularEval_X]
  rfl

end
end Dubon2026
