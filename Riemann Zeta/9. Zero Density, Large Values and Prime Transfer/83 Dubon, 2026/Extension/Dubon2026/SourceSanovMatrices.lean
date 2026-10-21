import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Tactic

/-! The actual integral unipotent matrices for the needed free congruence subgroup.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective native H1 coefficient map -> Gamma0 H2 vanishing
after inverting six -> a free subgroup of index dividing 48.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). The actual integer matrices and their
actions are used throughout.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- The actual upper unipotent generator of the required free subgroup. -/
def sourceSanovA : SL(2, ℤ) :=
  ⟨Matrix.of ![![1, 2], ![0, 1]], by simp [Matrix.det_fin_two]⟩

/-- The actual lower unipotent generator of the required free subgroup. -/
def sourceSanovB : SL(2, ℤ) :=
  ⟨Matrix.of ![![1, 0], ![2, 1]], by simp [Matrix.det_fin_two]⟩

/-- A nonzero even shear strictly increases the dominant integer coordinate. -/
theorem sourceSanov_abs_growth {x y n : ℤ} (hn : n ≠ 0) (h : |x| < |y|) :
    |y| < |x + 2 * n * y| := by
  have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  have h2 : |2 * n * y| - |x| ≤ |x + 2 * n * y| := by
    have he := abs_sub_abs_le_abs_add (2 * n * y) x
    rwa [add_comm] at he
  have h3 : |2 * n * y| = 2 * |n| * |y| := by
    rw [abs_mul, abs_mul]
    norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg y)]

/-- Every integral power of the actual upper generator is the corresponding even shear. -/
theorem sourceSanovA_zpow (n : ℤ) :
    ((sourceSanovA ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2 * n; 0, 1] := by
  have hA : sourceSanovA = ModularGroup.T ^ (2 : ℤ) := by
    apply Subtype.ext
    rw [ModularGroup.coe_T_zpow]
    rfl
  rw [hA, ← zpow_mul]
  exact ModularGroup.coe_T_zpow (2 * n)

/-- Every integral power of the actual lower generator is the corresponding even shear. -/
theorem sourceSanovB_zpow (n : ℤ) :
    ((sourceSanovB ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2 * n, 1] := by
  induction n using Int.induction_on with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [zpow_add_one, SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [sourceSanovB, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals ring
  | pred k ih =>
    rw [zpow_sub_one, SpecialLinearGroup.coe_mul, ih, SpecialLinearGroup.coe_inv]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [sourceSanovB, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals ring

/-- The actual upper matrix power acts by the explicit integer shear. -/
theorem sourceSanovA_zpow_mulVec (n : ℤ) (v : Fin 2 → ℤ) :
    (((sourceSanovA ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).mulVec v =
      ![v 0 + 2 * n * v 1, v 1] := by
  rw [sourceSanovA_zpow]
  funext i
  fin_cases i
  all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The actual lower matrix power acts by the explicit integer shear. -/
theorem sourceSanovB_zpow_mulVec (n : ℤ) (v : Fin 2 → ℤ) :
    (((sourceSanovB ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).mulVec v =
      ![v 0, v 1 + 2 * n * v 0] := by
  rw [sourceSanovB_zpow]
  funext i
  fin_cases i
  all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

end
end Dubon2026
