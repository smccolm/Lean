import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.QExpansion
import P2M.Util
import P2M.Sol.S_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix N • τ)) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.qExpand ℂ N ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.solution
