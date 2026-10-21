import Dubon2026.SourceCuspHeckeTransitions

/-! The actual exceptional Hecke transition at the original cusp.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> the ell contribution
to the actual cusp-evaluation eigenvalue ell+1. Only original integral
Bezout and translation matrices enter the calculation.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

/-- The actual integral upper translations are the original powers of the unit translation. -/
theorem sourceCuspTranslation_zpow (Q : ℕ) (n : ℤ) :
    heckeUpperTranslation Q 1 ^ n = heckeUpperTranslation Q n := by
  apply Subtype.ext
  apply Subtype.ext
  change (ModularGroup.T ^ n : SL(2, ℤ)).val = _
  rw [ModularGroup.coe_T_zpow]
  rfl

variable (Q ell : ℕ) [NeZero ell] (hell : ell.Prime) (hellQ : Nat.Coprime ell Q)

omit [NeZero ell] in
/-- The original exceptional transition has its exact integral matrix entries. -/
theorem sourceCuspHeckeTransition_none_matrix :
    (sourceCuspHeckeTransition Q ell hell hellQ none).val.val.val =
      !![1 - (ell : ℤ) * Q, (ell : ℤ) * ell;
        -((Q : ℤ) * Q), 1 + (ell : ℤ) * Q] := by
  rw [sourceCuspHeckeTransition_none]
  have hb := heckePrime_bezout hellQ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      heckeBezoutRepresentative, heckeUpperTranslation, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val',
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      first | linear_combination hb | linear_combination -hb | ring

/-- The actual conjugated exceptional transition is conjugate inside Gamma0
to the ell-th power of the original unit translation. -/
theorem sourceCuspHeckeConjugation_none :
    sourceHeckeConjugation hell (sourceCuspHeckeTransition Q ell hell hellQ none) =
      heckeLowerTranslation Q 1 * (heckeUpperTranslation Q 1) ^ ell *
        (heckeLowerTranslation Q 1)⁻¹ := by
  rw [← sourceIntegralHeckeConjugate_eq_prime,
    ← zpow_natCast, sourceCuspTranslation_zpow]
  apply Subtype.ext
  apply Subtype.ext
  change (!![(sourceCuspHeckeTransition Q ell hell hellQ none).val.val.val 0 0,
      (sourceCuspHeckeTransition Q ell hell hellQ none).val.val.val 0 1 / (ell : ℤ);
      (sourceCuspHeckeTransition Q ell hell hellQ none).val.val.val 1 0 * (ell : ℤ),
      (sourceCuspHeckeTransition Q ell hell hellQ none).val.val.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [sourceCuspHeckeTransition_none_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeLowerTranslation, heckeUpperTranslation,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr (NeZero.ne ell))] <;> ring

end
end Dubon2026
