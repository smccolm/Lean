import Dubon2026.LocalCoefficientFiberProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Actual general-linear matrices over the original coefficient fiber product -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C]

/-- Original matrices over the actual coefficient fiber product are exactly compatible pairs of original coefficient matrices, as rings. -/
def matrixCoefficientFiberProductEquiv (f : A →+* C) (g : B →+* C) :
    Matrix ι ι (CoefficientFiberProduct f g) ≃+*
      CoefficientFiberProduct (RingHom.mapMatrix (m := ι) f) (RingHom.mapMatrix (m := ι) g) where
  toFun X := ⟨((RingHom.mapMatrix (coefficientFiberProductFst f g)) X,
    (RingHom.mapMatrix (coefficientFiberProductSnd f g)) X), by
      ext i j
      exact (X i j).property⟩
  invFun Y i j := ⟨(Y.val.1 i j, Y.val.2 i j),
    congrArg (fun X : Matrix ι ι C => X i j) Y.property⟩
  left_inv X := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    apply Prod.ext <;> ext i j <;> rfl
  map_add' X Y := by
    apply Subtype.ext
    exact Prod.ext (map_add _ X Y) (map_add _ X Y)
  map_mul' X Y := by
    apply Subtype.ext
    exact Prod.ext (map_mul _ X Y) (map_mul _ X Y)

/-- Glue the actual compatible invertible original matrices by transporting their genuine compatible-pair unit through the original matrix-ring equivalence. -/
def generalLinearCoefficientFiberProduct (f : A →+* C) (g : B →+* C)
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (h : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V) :
    GeneralLinearGroup ι (CoefficientFiberProduct f g) :=
  Units.map (matrixCoefficientFiberProductEquiv (ι := ι) f g).symm.toMonoidHom
    (coefficientFiberProductUnit (RingHom.mapMatrix (m := ι) f) (RingHom.mapMatrix (m := ι) g) U V h)

/-- The glued genuine invertible matrix has exactly the two supplied original projections. -/
theorem generalLinearCoefficientFiberProduct_projections (f : A →+* C) (g : B →+* C)
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (h : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V) :
    GeneralLinearGroup.map (coefficientFiberProductFst f g)
      (generalLinearCoefficientFiberProduct f g U V h) = U ∧
    GeneralLinearGroup.map (coefficientFiberProductSnd f g)
      (generalLinearCoefficientFiberProduct f g U V h) = V := by
  constructor <;> apply Units.ext <;> ext i j <;> rfl

/-- Equality of both actual coefficient projections determines the entire original invertible matrix over the genuine fiber product. -/
theorem generalLinearCoefficientFiberProduct_ext (f : A →+* C) (g : B →+* C)
    (U V : GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (hA : GeneralLinearGroup.map (coefficientFiberProductFst f g) U =
      GeneralLinearGroup.map (coefficientFiberProductFst f g) V)
    (hB : GeneralLinearGroup.map (coefficientFiberProductSnd f g) U =
      GeneralLinearGroup.map (coefficientFiberProductSnd f g) V) : U = V := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun W : GeneralLinearGroup ι A => W.val i j) hA)
    (congrArg (fun W : GeneralLinearGroup ι B => W.val i j) hB)

/-- Every compatible pair of actual invertible coefficient matrices comes from exactly one genuine invertible matrix over the original coefficient fiber product. -/
theorem generalLinearCoefficientFiberProduct_existsUnique (f : A →+* C) (g : B →+* C)
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (h : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V) :
    ∃! W : GeneralLinearGroup ι (CoefficientFiberProduct f g),
      GeneralLinearGroup.map (coefficientFiberProductFst f g) W = U ∧
      GeneralLinearGroup.map (coefficientFiberProductSnd f g) W = V := by
  refine ⟨generalLinearCoefficientFiberProduct f g U V h,
    generalLinearCoefficientFiberProduct_projections f g U V h, ?_⟩
  intro W hW
  exact generalLinearCoefficientFiberProduct_ext f g _ _
    (hW.1.trans (generalLinearCoefficientFiberProduct_projections f g U V h).1.symm)
    (hW.2.trans (generalLinearCoefficientFiberProduct_projections f g U V h).2.symm)

end
end Dubon2026
