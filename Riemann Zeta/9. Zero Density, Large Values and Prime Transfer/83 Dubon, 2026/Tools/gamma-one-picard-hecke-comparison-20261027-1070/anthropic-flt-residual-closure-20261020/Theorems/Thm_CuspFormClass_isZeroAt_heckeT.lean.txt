import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspFormClass_isZeroAt_heckeT

theorem CuspFormClass.isZeroAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k := by p2m_exact_reverting @_root_.P2MW.S_CuspFormClass_isZeroAt_heckeT.solution
