import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularFormClass_isBoundedAt_heckeT

theorem ModularFormClass.isBoundedAt_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_isBoundedAt_heckeT.solution
