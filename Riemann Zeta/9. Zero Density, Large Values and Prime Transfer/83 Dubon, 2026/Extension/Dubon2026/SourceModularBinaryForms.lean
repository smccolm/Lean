import Dubon2026.HomogeneousMonomialBasis
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The modular-symbol coefficient action from the existing polynomial representation.
DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 require the actual modular Galois
association along the higher symmetric-power continuation route. The period-map
proof of integral Hecke algebra finiteness needs the integral binary forms.
Transpose converts the already proved column substitution into the right row
substitution used by modular symbols. No new symmetric-power framework is needed.
-/

namespace Dubon2026
noncomputable section
open Matrix MulOpposite MvPolynomial

variable (R : Type*) [CommRing R] (w : ℕ)

/-- Integral row substitution on binary forms, obtained from the existing homogeneous action. -/
def sourceModularBinaryFormRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (homogeneousSubmodule (Fin 2) R w) :=
  (homogeneousMatrixRepresentation w).comp
    ((Matrix.transposeRingEquiv (Fin 2) R).symm.toMonoidHom.comp
      (MonoidHom.op (Int.castRingHom R).mapMatrix.toMonoidHom))

variable {R w}

/-- The modular coefficient action is exactly the original action at the transposed matrix. -/
theorem sourceModularBinaryFormRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    (sourceModularBinaryFormRep R w (op M) P).val =
      matrixPolynomialAction (M.map (Int.castRingHom R))ᵀ P.val := rfl

/-- Matrix multiplication gives the right action required by period polynomials. -/
theorem sourceModularBinaryFormRep_mul (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    sourceModularBinaryFormRep R w (op (M * N)) P =
      sourceModularBinaryFormRep R w (op N) (sourceModularBinaryFormRep R w (op M) P) := by
  rw [op_mul, map_mul, Module.End.mul_apply]

variable (R w) in
/-- Adjugate substitution is the genuine left coefficient action for integral modular symbols. -/
def sourceModularBinaryFormAdjugateRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ) (homogeneousSubmodule (Fin 2) R w) :=
  (sourceModularBinaryFormRep R w).comp
    { toFun := fun M => op (adjugate M)
      map_one' := by simp
      map_mul' := fun M N => by simp [adjugate_mul_distrib] }

/-- The constructed integral left action evaluates at the actual adjugate. -/
theorem sourceModularBinaryFormAdjugateRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    sourceModularBinaryFormAdjugateRep R w M P =
      sourceModularBinaryFormRep R w (op (adjugate M)) P := rfl

variable (R w) in
/-- The modular-group coefficient representation uses the inverse matrix in the same right action. -/
def sourceModularBinaryFormSLRep :
    Representation R (SpecialLinearGroup (Fin 2) ℤ) (homogeneousSubmodule (Fin 2) R w) :=
  (sourceModularBinaryFormRep R w).comp
    { toFun := fun g => op ((g⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      map_one' := by simp
      map_mul' := fun g h => by simp }

/-- The modular-group coefficient action is the same row substitution at the inverse. -/
theorem sourceModularBinaryFormSLRep_apply (g : SpecialLinearGroup (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    sourceModularBinaryFormSLRep R w g P =
      sourceModularBinaryFormRep R w
        (op ((g⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) P := rfl

/-- The left coefficient action undoes the corresponding right substitution. -/
theorem sourceModularBinaryFormSLRep_right_cancel (g : SpecialLinearGroup (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    sourceModularBinaryFormSLRep R w g
      (sourceModularBinaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) P) = P := by
  rw [sourceModularBinaryFormSLRep_apply, ← sourceModularBinaryFormRep_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, op_one, map_one, Module.End.one_apply]

/-- Right substitution undoes the corresponding left coefficient action. -/
theorem sourceModularBinaryFormRep_left_cancel (g : SpecialLinearGroup (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    sourceModularBinaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
      (sourceModularBinaryFormSLRep R w g P) = P := by
  rw [sourceModularBinaryFormSLRep_apply, ← sourceModularBinaryFormRep_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, op_one, map_one, Module.End.one_apply]

/-- Restriction of the original adjugate action to determinant-one matrices is the original inverse action. -/
theorem sourceModularBinaryFormAdjugateRep_SL (g : SpecialLinearGroup (Fin 2) ℤ) :
    sourceModularBinaryFormAdjugateRep R w (g : Matrix (Fin 2) (Fin 2) ℤ) =
      sourceModularBinaryFormSLRep R w g := by
  apply LinearMap.ext
  intro P
  change sourceModularBinaryFormRep R w (op (adjugate (g : Matrix (Fin 2) (Fin 2) ℤ))) P =
    sourceModularBinaryFormRep R w (op ((g⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) P
  exact congrArg (fun M => sourceModularBinaryFormRep R w (op M) P)
    (Matrix.SpecialLinearGroup.coe_inv g).symm

/-- The literal integral coefficient module is finite free, witnessed by the already proved monomial basis. -/
theorem sourceModularBinaryForm_finite_free :
    Module.Finite R (homogeneousSubmodule (Fin 2) R w) ∧
      Module.Free R (homogeneousSubmodule (Fin 2) R w) := by
  let b := binaryHomogeneousMonomialBasis (R := R) w
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b⟩

end
end Dubon2026
