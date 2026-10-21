import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Tactic

/-!
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> actual cusp-evaluation
functional -> a native SL2(Z) cocycle with prescribed S and S*T values.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
The existing underlying group action replaces the external action
construction. Only the required existence statement is developed.
-/

namespace Dubon2026.SourceSL2Cocycle
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup
/-- The actual modular generator S*T. -/
def U : SL(2, ℤ) := S * T

/-- The actual matrix entries of the generator S*T. -/
theorem coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
  rw [U, Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The original modular generator S squares to minus one. -/
theorem S_mul_S : S * S = (-1 : SL(2, ℤ)) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

/-- The original modular generator S*T cubes to minus one. -/
theorem U_pow_three : U ^ 3 = (-1 : SL(2, ℤ)) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_U, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, pow_succ, pow_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The two actual positive unipotent matrices in the reduced-word calculation. -/
def X (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  if a = 0 then !![1, 1; 0, 1] else !![1, 0; 1, 1]

/-- Each actual alternating generator block is a negative positive-unipotent matrix. -/
theorem coe_S_mul_U_pow (a : Fin 2) :
    ((S * U ^ ((a : ℕ) + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -X a := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_S, coe_U]
  fin_cases a
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

/-- The strict diagonal and off-diagonal positivity needed to detect a nonempty original word. -/
def PosInv (P : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (0 < P 0 0 ∧ 0 ≤ P 0 1) ∧ (0 ≤ P 1 0 ∧ 0 < P 1 1) ∧ 0 < P 0 1 + P 1 0

/-- Each original positive-unipotent block has the required positivity. -/
theorem posInv_X (a : Fin 2) : PosInv (X a) := by
  fin_cases a <;> simp [PosInv, X]

/-- The original positive-unipotent blocks preserve the required positivity. -/
theorem posInv_X_mul (a : Fin 2) {P : Matrix (Fin 2) (Fin 2) ℤ} (hP : PosInv P) :
    PosInv (X a * P) := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, hoff⟩ := hP
  fin_cases a <;>
    simp only [PosInv, X, Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte, one_ne_zero,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', one_mul, zero_mul,
      add_zero, zero_add] <;> omega

/-- The actual matrix product of the original positive-unipotent blocks. -/
def xProd (l : List (Fin 2)) : Matrix (Fin 2) (Fin 2) ℤ := (l.map X).prod

/-- Every nonempty original block word has positive off-diagonal sum. -/
theorem posInv_xProd {l : List (Fin 2)} (hl : l ≠ []) : PosInv (xProd l) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    by_cases h : l = []
    · subst h
      simpa [xProd] using posInv_X a
    · simpa [xProd, List.map_cons, List.prod_cons] using posInv_X_mul a (ih h)


end
end Dubon2026.SourceSL2Cocycle
