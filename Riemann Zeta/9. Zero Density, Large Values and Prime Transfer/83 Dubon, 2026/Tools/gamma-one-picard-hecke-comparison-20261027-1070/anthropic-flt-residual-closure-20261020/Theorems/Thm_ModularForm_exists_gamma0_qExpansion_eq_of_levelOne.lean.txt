import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.solution
