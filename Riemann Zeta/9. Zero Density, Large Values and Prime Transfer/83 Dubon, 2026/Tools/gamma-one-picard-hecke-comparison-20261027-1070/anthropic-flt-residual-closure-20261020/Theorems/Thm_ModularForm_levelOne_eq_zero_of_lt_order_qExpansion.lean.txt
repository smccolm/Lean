import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import P2M.Util
import P2M.Sol.S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion

open UpperHalfPlane
open scoped MatrixGroups Manifold
theorem ModularForm.levelOne_eq_zero_of_lt_order_qExpansion (M : ℕ) (hM : 0 < M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (h : ((M * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (M : ℝ) F).order) : F = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.solution
